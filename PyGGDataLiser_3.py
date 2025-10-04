"""
GameMaker Read-Only Viewer (lazy + syntax highlighting + room visualizer)
- Lazy-load images/sounds (store ranges during parse; decode on expand/preview)
- Syntax highlighting for scripts (basic GML heuristics)
- Room visualizer (grid + heuristic object placement)
- Determinate loading window, search, filters, right-click export, export all, waveform

Dependencies (optional features):
    pip install pillow pygame matplotlib pydub simpleaudio numpy
Note: pydub needs ffmpeg to decode OGG; WAV works natively.
"""
import struct, io, os, tempfile, threading, sys, math, time, hashlib, random
from collections import defaultdict

import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext

from PIL import Image, ImageTk

# optional libs
try:
    import pygame
    pygame.mixer.init()
    PYGAME_OK = True
except Exception:
    PYGAME_OK = False

try:
    import simpleaudio as sa
    SIMPLEAUDIO_OK = True
except Exception:
    SIMPLEAUDIO_OK = False

try:
    from pydub import AudioSegment
    PYDUB_OK = True
except Exception:
    PYDUB_OK = False

try:
    import matplotlib.pyplot as plt
    from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
    MATPLOTLIB_OK = True
except Exception:
    MATPLOTLIB_OK = False

# numpy used for waveform decoding/processing
try:
    import numpy as _np
    NUMPY_OK = True
except Exception:
    NUMPY_OK = False

# ---------------------------------------------------------------------------
# Low-level parser functions (chunk discovery, small range finders)
# ---------------------------------------------------------------------------
UPPER_A = 65
UPPER_Z = 90

def is_ascii_upper4(b):
    return len(b) == 4 and all(UPPER_A <= x <= UPPER_Z for x in b)

def read_u32_le(data, offset):
    if offset + 4 <= len(data):
        return struct.unpack_from("<I", data, offset)[0]
    return None

def recursive_find_chunks(data, start, end):
    """
    scan [start,end) for 4-letter uppercase chunk headers + size
    returns list of (name, header_offset, size, content_start, content_end)
    """
    chunks = []
    i = start
    n = end
    while i < n - 8:
        name_bytes = data[i:i+4]
        if is_ascii_upper4(name_bytes):
            size = read_u32_le(data, i+4)
            if size is None:
                i += 1
                continue
            content_start = i + 8
            content_end = content_start + size
            if content_start >= start and content_end <= end and size > 0:
                name = name_bytes.decode('ascii', errors='ignore')
                chunks.append((name, i, size, content_start, content_end))
                inner = recursive_find_chunks(data, content_start, content_end)
                if inner:
                    chunks.extend(inner)
                i = content_end
                continue
        i += 1
    return chunks

def find_top_form(data):
    if data.startswith(b'FORM'):
        size = read_u32_le(data, 4)
        if size:
            cs = 8
            ce = cs + size
            if ce <= len(data):
                return (0, cs, ce)
    genpos = data.find(b'GEN8')
    if genpos != -1:
        back = max(0, genpos - 64)
        formpos = data.find(b'FORM', back, genpos)
        if formpos != -1:
            size = read_u32_le(data, formpos+4)
            if size:
                cs = formpos + 8
                ce = cs + size
                if ce <= len(data):
                    return (formpos, cs, ce)
    return (None, 0, len(data))

def extract_strings_from_region(data, start, end):
    segment = data[start:end]
    strings = []
    off = 0
    while off < len(segment):
        nxt = segment.find(b'\x00', off)
        if nxt == -1:
            break
        raw = segment[off:nxt]
        try:
            s = raw.decode('utf-8')
        except Exception:
            try:
                s = raw.decode('latin-1', errors='ignore')
            except Exception:
                s = None
        if s and len(s) > 0 and any(ch.isalnum() for ch in s):
            strings.append(s)
        off = nxt + 1
    # dedupe preserve order
    seen = set()
    out = []
    for x in strings:
        if x not in seen:
            seen.add(x)
            out.append(x)
    return out

def find_png_ranges(data, start, end):
    """
    Return list of (abs_start, abs_end) for embedded PNGs (using signature & IEND)
    """
    seg = data[start:end]
    png_sig = b'\x89PNG\r\n\x1a\n'
    idx = 0
    ranges = []
    while True:
        pos = seg.find(png_sig, idx)
        if pos == -1:
            break
        abs_pos = start + pos
        # find 'IEND' after pos
        iend = seg.find(b'IEND', pos)
        if iend == -1:
            break
        # include 8 bytes after IEND (IEND + CRC)
        abs_end = start + iend + 8
        if abs_end > end:
            abs_end = end
        ranges.append((abs_pos, abs_end))
        idx = iend + 8
    return ranges

def find_audio_ranges(data, start, end):
    """
    Return list of (abs_start, abs_end, type) for RIFF (wav) and OggS (ogg)
    """
    seg = data[start:end]
    items = []
    # WAV (RIFF)
    idx = 0
    while True:
        riff = seg.find(b'RIFF', idx)
        if riff == -1:
            break
        if riff + 8 > len(seg):
            break
        size = struct.unpack_from('<I', seg, riff+4)[0]
        total = 8 + size
        abs_start = start + riff
        abs_end = start + riff + total if (riff + total) <= len(seg) else end
        items.append((abs_start, abs_end, 'wav'))
        idx = riff + total
    # OggS
    idx = 0
    while True:
        ogg = seg.find(b'OggS', idx)
        if ogg == -1:
            break
        abs_ogg = start + ogg
        next_ogg = seg.find(b'OggS', ogg+4)
        if next_ogg == -1:
            abs_end = end
            items.append((abs_ogg, abs_end, 'ogg'))
            break
        else:
            abs_end = start + next_ogg
            items.append((abs_ogg, abs_end, 'ogg'))
            idx = next_ogg
    return items

def safe_decode_text(blob):
    try:
        return blob.decode('utf-8', errors='strict')
    except Exception:
        try:
            return blob.decode('latin-1', errors='ignore')
        except Exception:
            return None

# ---------------------------------------------------------------------------
# Loading modal with determinate progress
# ---------------------------------------------------------------------------
class LoadingWindow:
    def __init__(self, parent, title="Loading..."):
        self.top = tk.Toplevel(parent)
        self.top.title(title)
        self.top.geometry("460x120")
        self.top.resizable(False, False)
        self.top.transient(parent)
        self.top.grab_set()

        ttk.Label(self.top, text=title, font=("Segoe UI", 11, "bold")).pack(pady=(8,4))
        self.status_var = tk.StringVar(value="Starting...")
        self.status_lbl = ttk.Label(self.top, textvariable=self.status_var)
        self.status_lbl.pack()
        self.progress = ttk.Progressbar(self.top, orient=tk.HORIZONTAL, length=420, mode="determinate")
        self.progress.pack(pady=8)
        self.top.update()
        self._max = 100
        self._val = 0

    def set_max(self, mx):
        self._max = max(1, int(mx))
        try:
            self.progress.config(maximum=self._max)
        except Exception:
            pass
        self.top.update()

    def set_status(self, text):
        self.status_var.set(text)
        self.top.update_idletasks()

    def step(self, n=1):
        self._val += n
        if self._val > self._max:
            self._val = self._max
        try:
            self.progress['value'] = self._val
        except Exception:
            pass
        self.top.update_idletasks()

    def close(self):
        try:
            self.top.grab_release()
        except Exception:
            pass
        try:
            self.top.destroy()
        except Exception:
            pass

# ---------------------------------------------------------------------------
# GUI & App
# ---------------------------------------------------------------------------
class GMViewerApp:
    def __init__(self, root):
        self.root = root
        root.title("GameMaker Read-Only Viewer")
        root.geometry("1200x740")

        # Menu
        menubar = tk.Menu(root)
        filemenu = tk.Menu(menubar, tearoff=0)
        filemenu.add_command(label="Open...", command=self.open_file)
        filemenu.add_separator()
        filemenu.add_command(label="Export all assets...", command=self.export_all_assets)
        filemenu.add_separator()
        filemenu.add_command(label="Exit", command=root.quit)
        menubar.add_cascade(label="File", menu=filemenu)
        root.config(menu=menubar)

        # Top: search + filters
        topbar = ttk.Frame(root)
        topbar.pack(fill=tk.X, padx=6, pady=4)

        ttk.Label(topbar, text="Search:").pack(side=tk.LEFT)
        self.search_var = tk.StringVar()
        self.search_entry = ttk.Entry(topbar, textvariable=self.search_var)
        self.search_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(6,8))
        self.search_entry.bind("<KeyRelease>", lambda e: self.populate_tree())

        self.filters = {}
        for cat in ["Chunks", "Strings", "Images", "Sounds", "Scripts", "Rooms", "Objects"]:
            var = tk.BooleanVar(value=True)
            chk = ttk.Checkbutton(topbar, text=cat, variable=var, command=self.populate_tree)
            chk.pack(side=tk.LEFT, padx=4)
            self.filters[cat.lower()] = var

        # Split panes
        self.pane = ttk.Panedwindow(root, orient=tk.HORIZONTAL)
        self.pane.pack(fill=tk.BOTH, expand=True)

        # Left Tree
        left_frame = ttk.Frame(self.pane, width=380)
        self.tree = ttk.Treeview(left_frame)
        self.tree.pack(fill=tk.BOTH, expand=True, side=tk.LEFT)
        scroll = ttk.Scrollbar(left_frame, orient=tk.VERTICAL, command=self.tree.yview)
        self.tree.configure(yscrollcommand=scroll.set)
        scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.tree.bind("<<TreeviewSelect>>", self.on_tree_select)
        self.tree.bind("<Button-3>", self.on_right_click)
        self.tree.bind("<<TreeviewOpen>>", self.on_tree_open)  # lazy load hook
        self.pane.add(left_frame, weight=1)

        # Right preview
        right_frame = ttk.Frame(self.pane)
        self.preview_title = ttk.Label(right_frame, text="Open a GameMaker file to begin", font=("Segoe UI", 12, "bold"))
        self.preview_title.pack(anchor='nw', padx=6, pady=(6,0))

        self.small_progress = ttk.Progressbar(right_frame, mode="indeterminate")
        self.small_progress.pack(fill=tk.X, padx=6, pady=(4,6))
        self.small_progress.stop()

        self.image_label = ttk.Label(right_frame)
        self.image_label.pack(padx=6, pady=6)
        self.text_preview = scrolledtext.ScrolledText(right_frame, wrap=tk.WORD, height=18)
        self.text_preview.pack(fill=tk.BOTH, expand=True, padx=6, pady=6)
        self.text_preview.configure(state=tk.DISABLED)

        # Setup syntax tags for script highlighting
        self.text_preview.tag_config("kw", foreground="#1E90FF")
        self.text_preview.tag_config("comment", foreground="#228B22")
        self.text_preview.tag_config("string", foreground="#D2691E")
        self.text_preview.tag_config("number", foreground="#8B008B")
        self.text_preview.tag_config("func", foreground="#6A5ACD")

        audio_frame = ttk.Frame(right_frame)
        audio_frame.pack(fill=tk.X, padx=6, pady=6)
        self.play_btn = ttk.Button(audio_frame, text="Play", command=self.play_audio, state=tk.DISABLED)
        self.play_btn.pack(side=tk.LEFT)
        self.stop_btn = ttk.Button(audio_frame, text="Stop", command=self.stop_audio, state=tk.DISABLED)
        self.stop_btn.pack(side=tk.LEFT, padx=(6,0))
        self.wave_btn = ttk.Button(audio_frame, text="Waveform", command=self.show_waveform, state=tk.DISABLED)
        self.wave_btn.pack(side=tk.LEFT, padx=(6,0))
        self.audio_status = ttk.Label(audio_frame, text="")
        self.audio_status.pack(side=tk.LEFT, padx=10)

        # Room canvas (hidden until room selected)
        self.room_canvas = tk.Canvas(right_frame, bg="#2b2b2b")
        # don't pack here; show when needed

        self.pane.add(right_frame, weight=4)

        # Right-click menu
        self.menu = tk.Menu(self.root, tearoff=0)
        self.menu.add_command(label="Export...", command=self.export_item)
        self.menu.add_command(label="Copy name", command=self.copy_name)

        # Data structures (lazy-friendly)
        self.filepath = None
        self.raw = None
        self.form_bounds = None
        self.chunks = []
        self.strings = []
        # images: list of dicts {"name","start","end","pil"(None until loaded)}
        self.images = []
        # sounds: list of dicts {"name","start","end","type","tempfile"(None until played)}
        self.sounds = []
        self.scripts = []
        self.rooms = []
        self.objects = []
        self.tree_map = {}
        self.current_sound_tempfile = None
        self.current_sound_index = None
        self.playing_obj = None

    # ------------------------------
    # Open file -> show loading modal -> parse in thread
    # ------------------------------
    def open_file(self):
        path = filedialog.askopenfilename(title="Open GameMaker data.win / .wim",
                                          filetypes=[("GameMaker Data", "*.wim *.win"), ("All files", "*.*")])
        if not path:
            return
        self.filepath = path
        self.loading = LoadingWindow(self.root, title=f"Loading {os.path.basename(path)}")
        t = threading.Thread(target=self._parse_file_thread, args=(path, self.loading), daemon=True)
        t.start()
        try:
            self.small_progress.start(20)
        except Exception:
            pass

    def _parse_file_thread(self, path, loading_win: LoadingWindow):
        def set_status(s): self.root.after(0, lambda: loading_win.set_status(s))
        def step(n=1): self.root.after(0, lambda: loading_win.step(n))
        def set_max(m): self.root.after(0, lambda: loading_win.set_max(m))

        set_status("Reading file into memory...")
        try:
            with open(path, "rb") as f:
                data = f.read()
        except Exception as e:
            self.root.after(0, lambda: messagebox.showerror("Error", f"Failed to read file: {e}"))
            self.root.after(0, loading_win.close)
            return

        self.raw = data
        set_status("Locating FORM / GEN8...")
        formpos, cs, ce = find_top_form(data)
        self.form_bounds = (formpos, cs, ce)

        set_status("Scanning for chunks...")
        chunks = recursive_find_chunks(data, cs, ce)
        if formpos is not None:
            chunks.insert(0, ("FORM", formpos, ce-cs, cs, ce))
        # dedupe
        seen = set()
        dedup = []
        for c in chunks:
            key = (c[0], c[1])
            if key not in seen:
                seen.add(key)
                dedup.append(c)
        self.chunks = dedup

        # Pre-scan PNGs and audio counts for determinate progress (but don't extract blobs)
        set_status("Counting assets for progress...")
        png_total = 0
        auds_total = 0
        # PNG ranges in TXTR chunks
        for (name, off, size, cs2, ce2) in self.chunks:
            if name == 'TXTR':
                rngs = find_png_ranges(data, cs2, ce2)
                png_total += len(rngs)
        # fallback scan in form region
        if png_total == 0 and cs < ce:
            png_total = len(find_png_ranges(data, cs, ce))
        # audio ranges
        for (name, off, size, cs2, ce2) in self.chunks:
            if name == 'AUDO':
                auds_total += len(find_audio_ranges(data, cs2, ce2))
        if auds_total == 0 and cs < ce:
            auds_total = len(find_audio_ranges(data, cs, ce))

        total_steps = max(1, len(self.chunks) + 1 + png_total + auds_total + 1)
        set_max(total_steps)
        for (name, off, size, cs2, ce2) in self.chunks:
            set_status(f"Found chunk: {name} @ {off}")
            step(1)

        # strings
        set_status("Parsing STRG (strings)...")
        self.strings = []
        for (name, off, size, cs2, ce2) in self.chunks:
            if name == 'STRG':
                s = extract_strings_from_region(data, cs2, ce2)
                for it in s:
                    if it not in self.strings:
                        self.strings.append(it)
        if not self.strings and cs < ce:
            s = extract_strings_from_region(data, cs, ce)
            for it in s:
                if it not in self.strings:
                    self.strings.append(it)
        step(1)

        # find PNG ranges (store ranges only)
        set_status("Indexing PNG textures (lazy)...")
        self.images = []
        pngs_found = []
        for (name, off, size, cs2, ce2) in self.chunks:
            if name == 'TXTR':
                rngs = find_png_ranges(data, cs2, ce2)
                for s,e in rngs:
                    pngs_found.append((s,e))
        if not pngs_found and cs < ce:
            pngs_found = find_png_ranges(data, cs, ce)
        for (start_pos, end_pos) in pngs_found:
            name_guess = None
            for st in self.strings:
                try:
                    p = data.find(st.encode('utf-8'))
                    if p != -1 and abs(p - start_pos) < 4096:
                        name_guess = st
                        break
                except Exception:
                    continue
            # store ranges but do NOT decode bytes until requested
            self.images.append({"name": name_guess or f"image_{start_pos}", "start": start_pos, "end": end_pos, "pil": None})
            step(1)

        # find audio ranges (store ranges only)
        set_status("Indexing audio blobs (lazy)...")
        self.sounds = []
        auds_found = []
        for (name, off, size, cs2, ce2) in self.chunks:
            if name == 'AUDO':
                items = find_audio_ranges(data, cs2, ce2)
                for s,e,t in items:
                    auds_found.append((s,e,t))
        if not auds_found and cs < ce:
            auds_found = find_audio_ranges(data, cs, ce)
        for start_pos, end_pos, typ in auds_found:
            name_guess = None
            for st in self.strings:
                try:
                    p = data.find(st.encode('utf-8'))
                    if p != -1 and abs(p - start_pos) < 4096:
                        name_guess = st
                        break
                except Exception:
                    continue
            self.sounds.append({"name": name_guess or f"audio_{start_pos}", "start": start_pos, "end": end_pos, "type": typ, "temp": None})
            step(1)

        # scripts, rooms, objects heuristics (strings based)
        set_status("Collecting scripts / rooms / objects...")
        self.scripts = []
        self.rooms = []
        self.objects = []
        for s in self.strings:
            if s.startswith("scr_") or s.startswith("gml_") or s.startswith("script_") or s.startswith("gml_Script"):
                if s not in self.scripts:
                    self.scripts.append(s)
            if s.startswith("room_"):
                if s not in self.rooms:
                    self.rooms.append(s)
            if s.startswith("obj_"):
                if s not in self.objects:
                    self.objects.append(s)
        step(1)

        set_status("Finalizing...")
        time.sleep(0.05)
        self.root.after(0, lambda: self.populate_tree())
        self.root.after(0, lambda: loading_win.close())
        self.root.after(0, lambda: self.small_progress.stop())

    # ------------------------------
    # Populate tree (apply search + filters)
    # - For images/sounds we create group nodes with placeholders so they can be expanded to lazy-load details
    # ------------------------------
    def populate_tree(self):
        for it in self.tree.get_children():
            self.tree.delete(it)
        self.tree_map.clear()
        q = (self.search_var.get() or "").lower().strip()
        def match(s): return (not q) or (q in s.lower())

        if self.filters["chunks"].get():
            ch_node = self.tree.insert("", "end", text=f"Chunks ({len(self.chunks)})", open=True)
            for (name,off,size,cs,ce) in self.chunks:
                txt = f"{name} @ {off} ({size} bytes)"
                if match(txt):
                    nid = self.tree.insert(ch_node, "end", text=txt)
                    self.tree_map[nid] = {"type":"chunk","name":name,"offset":off,"size":size,"cs":cs,"ce":ce}

        if self.filters["strings"].get():
            s_node = self.tree.insert("", "end", text=f"Strings ({len(self.strings)})", open=False)
            for s in self.strings:
                if match(s):
                    nid = self.tree.insert(s_node, "end", text=s)
                    self.tree_map[nid] = {"type":"string","text":s}

        # Images: group node only; children are inserted when expanded (lazy)
        if self.filters["images"].get():
            img_node = self.tree.insert("", "end", text=f"Images ({len(self.images)})", open=False)
            # placeholder child so the node is expandable
            if len(self.images) > 0:
                ph = self.tree.insert(img_node, "end", text="(expand to load images...)")
                self.tree_map[ph] = {"type":"placeholder"}
            else:
                # show empty
                ph = self.tree.insert(img_node, "end", text="(no images)")
                self.tree_map[ph] = {"type":"placeholder"}

        # Sounds: group node only
        if self.filters["sounds"].get():
            snd_node = self.tree.insert("", "end", text=f"Sounds ({len(self.sounds)})", open=False)
            if len(self.sounds) > 0:
                ph = self.tree.insert(snd_node, "end", text="(expand to load sounds...)")
                self.tree_map[ph] = {"type":"placeholder"}
            else:
                ph = self.tree.insert(snd_node, "end", text="(no sounds)")
                self.tree_map[ph] = {"type":"placeholder"}

        if self.filters["scripts"].get():
            scr_node = self.tree.insert("", "end", text=f"Scripts ({len(self.scripts)})", open=False)
            for s in self.scripts:
                if match(s):
                    nid = self.tree.insert(scr_node, "end", text=s)
                    self.tree_map[nid] = {"type":"script","text":s}

        if self.filters["rooms"].get():
            rm_node = self.tree.insert("", "end", text=f"Rooms ({len(self.rooms)})", open=False)
            for r in self.rooms:
                if match(r):
                    nid = self.tree.insert(rm_node, "end", text=r)
                    self.tree_map[nid] = {"type":"room","text":r}

        if self.filters["objects"].get():
            obj_node = self.tree.insert("", "end", text=f"Objects ({len(self.objects)})", open=False)
            for o in self.objects:
                if match(o):
                    nid = self.tree.insert(obj_node, "end", text=o)
                    self.tree_map[nid] = {"type":"object","text":o}

        top = self.tree.insert("", "end", text="Summary", open=True)
        self.tree_map[top] = {"type":"summary"}
        self.tree.insert(top, "end", text=f"Images: {len(self.images)}")
        self.tree.insert(top, "end", text=f"Sounds: {len(self.sounds)}")
        self.tree.insert(top, "end", text=f"Strings: {len(self.strings)}")
        self.tree.insert(top, "end", text=f"Scripts: {len(self.scripts)}")
        self.tree.insert(top, "end", text=f"Rooms: {len(self.rooms)}")
        self.tree.insert(top, "end", text=f"Objects: {len(self.objects)}")

    # ------------------------------
    # When an expandable node is opened, populate its children and load actual assets (lazy decode)
    # ------------------------------
    def on_tree_open(self, event):
        iid = self.tree.focus()
        if not iid:
            return
        text = self.tree.item(iid, "text")
        # if Images group opened
        if text.startswith("Images"):
            # check whether there is only a placeholder child
            children = self.tree.get_children(iid)
            if len(children) == 1:
                # remove placeholder(s)
                for c in children:
                    self.tree.delete(c)
                # insert actual image entries (do not decode PIL yet; only when previewed)
                for i, img in enumerate(self.images):
                    label = f"{img.get('name','image')} ({img.get('start')})"
                    nid = self.tree.insert(iid, "end", text=label)
                    self.tree_map[nid] = {"type":"image","index":i}
        # if Sounds group opened
        if text.startswith("Sounds"):
            children = self.tree.get_children(iid)
            if len(children) == 1:
                for c in children:
                    self.tree.delete(c)
                for i, snd in enumerate(self.sounds):
                    label = f"{snd.get('name','sound')} ({snd.get('type')})"
                    nid = self.tree.insert(iid, "end", text=label)
                    self.tree_map[nid] = {"type":"sound","index":i}

    # ------------------------------
    # Right-click menu
    # ------------------------------
    def on_right_click(self, event):
        iid = self.tree.identify_row(event.y)
        if iid:
            self.tree.selection_set(iid)
            self.menu.post(event.x_root, event.y_root)

    def export_item(self):
        sel = self.tree.selection()
        if not sel: return
        meta = self.tree_map.get(sel[0])
        if not meta: return
        t = meta.get("type")
        if t in ("string","script","room","object"):
            s = meta.get("text","")
            path = filedialog.asksaveasfilename(defaultextension=".txt")
            if not path: return
            with open(path, "w", encoding="utf-8") as f: f.write(s)
        elif t == "image":
            idx = meta["index"]; img = self.images[idx]
            path = filedialog.asksaveasfilename(defaultextension=".png")
            if not path: return
            # load bytes lazily and write
            blob = self._read_range(img["start"], img["end"])
            with open(path, "wb") as f: f.write(blob)
        elif t == "sound":
            idx = meta["index"]; snd = self.sounds[idx]
            ext = ".wav" if snd.get("type") == "wav" else ".ogg"
            path = filedialog.asksaveasfilename(defaultextension=ext)
            if not path: return
            blob = self._read_range(snd["start"], snd["end"])
            with open(path, "wb") as f: f.write(blob)
        elif t == "chunk":
            cs, ce = meta["cs"], meta["ce"]
            path = filedialog.asksaveasfilename(defaultextension=".bin")
            if not path: return
            with open(path, "wb") as f: f.write(self.raw[cs:ce])

    def copy_name(self):
        sel = self.tree.selection()
        if not sel: return
        meta = self.tree_map.get(sel[0])
        if not meta: return
        txt = meta.get("text") or meta.get("name") or ""
        try:
            self.root.clipboard_clear()
            self.root.clipboard_append(txt)
        except Exception:
            pass

    # ------------------------------
    # Export all assets (reads ranges lazily)
    # ------------------------------
    def export_all_assets(self):
        if not self.raw:
            messagebox.showinfo("Export", "No file loaded.")
            return
        dest = filedialog.askdirectory(title="Select folder to export all assets into")
        if not dest:
            return
        img_dir = os.path.join(dest, "images")
        snd_dir = os.path.join(dest, "sounds")
        scr_dir = os.path.join(dest, "scripts")
        os.makedirs(img_dir, exist_ok=True)
        os.makedirs(snd_dir, exist_ok=True)
        os.makedirs(scr_dir, exist_ok=True)

        for i, img in enumerate(self.images):
            name = img.get("name", f"image_{i}")
            safe = "".join(c if c.isalnum() or c in "._-" else "_" for c in name)
            path = os.path.join(img_dir, f"{safe}_{i}.png")
            try:
                blob = self._read_range(img["start"], img["end"])
                with open(path, "wb") as f: f.write(blob)
            except Exception:
                pass

        for i, snd in enumerate(self.sounds):
            name = snd.get("name", f"sound_{i}")
            safe = "".join(c if c.isalnum() or c in "._-" else "_" for c in name)
            ext = ".wav" if snd.get("type") == "wav" else ".ogg"
            path = os.path.join(snd_dir, f"{safe}_{i}{ext}")
            try:
                blob = self._read_range(snd["start"], snd["end"])
                with open(path, "wb") as f: f.write(blob)
            except Exception:
                pass

        for i, scr in enumerate(self.scripts):
            safe = "".join(c if c.isalnum() or c in "._-" else "_" for c in scr)
            path = os.path.join(scr_dir, f"{safe}_{i}.txt")
            try:
                with open(path, "w", encoding="utf-8") as f: f.write(scr)
            except Exception:
                pass

        messagebox.showinfo("Export complete", f"Exported assets to {dest}")

    # ------------------------------
    # Read raw slice helper
    # ------------------------------
    def _read_range(self, start, end):
        if self.raw is None:
            return b""
        return self.raw[start:end]

    # ------------------------------
    # Selection handlers and previews
    # ------------------------------
    def on_tree_select(self, event):
        sel = self.tree.selection()
        if not sel:
            return
        meta = self.tree_map.get(sel[0])
        if not meta:
            self.clear_preview()
            return
        t = meta.get("type")
        if t == "string":
            self.show_text(meta["text"])
        elif t == "script":
            self.show_script(meta["text"])
        elif t == "room":
            self.show_room(meta["text"])
        elif t == "object":
            self.show_text(meta["text"])
        elif t == "image":
            self.show_image(meta["index"])
        elif t == "sound":
            self.show_sound(meta["index"])
        elif t == "chunk":
            self.show_chunk(meta)
        else:
            self.clear_preview()

    def clear_preview(self):
        # hide room canvas if visible
        try:
            self.room_canvas.pack_forget()
        except Exception:
            pass
        self.preview_title.config(text="Select an item to preview")
        self.image_label.config(image='', text='')
        self.image_label.image = None
        self.text_preview.pack(fill=tk.BOTH, expand=True, padx=6, pady=6)
        self.text_preview.configure(state=tk.NORMAL)
        self.text_preview.delete("1.0", tk.END)
        self.text_preview.configure(state=tk.DISABLED)
        self.play_btn.config(state=tk.DISABLED)
        self.stop_btn.config(state=tk.DISABLED)
        self.wave_btn.config(state=tk.DISABLED)
        self.audio_status.config(text="")

    def show_text(self, text):
        self.room_canvas.pack_forget()
        self.image_label.config(image='', text='')
        self.image_label.image = None
        self.preview_title.config(text="String / Text")
        self.text_preview.pack(fill=tk.BOTH, expand=True, padx=6, pady=6)
        self.text_preview.configure(state=tk.NORMAL)
        self.text_preview.delete("1.0", tk.END)
        self.text_preview.insert(tk.END, text)
        self.text_preview.configure(state=tk.DISABLED)
        self.play_btn.config(state=tk.DISABLED)
        self.stop_btn.config(state=tk.DISABLED)
        self.wave_btn.config(state=tk.DISABLED)
        self.audio_status.config(text="")

    # Syntax-highlighted script view
    def show_script(self, script_name):
        # try to find script body heuristically (search for name in raw and show following bytes)
        self.room_canvas.pack_forget()
        self.image_label.config(image='', text='')
        self.image_label.image = None
        self.preview_title.config(text=f"Script: {script_name}")
        body = "(script body not found)"
        if self.raw:
            try:
                b = script_name.encode('utf-8')
                pos = self.raw.find(b)
                if pos != -1:
                    sample = self.raw[pos: pos + 8192]
                    decoded = safe_decode_text(sample)
                    if decoded:
                        # try to extract lines after the name
                        idx = decoded.find(script_name)
                        if idx != -1:
                            body = decoded[idx + len(script_name):].strip()
                        else:
                            body = decoded
            except Exception:
                pass
        # show in text widget and highlight
        self.text_preview.pack(fill=tk.BOTH, expand=True, padx=6, pady=6)
        self.text_preview.configure(state=tk.NORMAL)
        self.text_preview.delete("1.0", tk.END)
        self.text_preview.insert(tk.END, body)
        self._highlight_gml(self.text_preview)
        self.text_preview.configure(state=tk.DISABLED)
        self.play_btn.config(state=tk.DISABLED)
        self.stop_btn.config(state=tk.DISABLED)
        self.wave_btn.config(state=tk.DISABLED)
        self.audio_status.config(text="")

    def _highlight_gml(self, widget):
        """
        Basic syntax highlighting for GML-like code in the provided Text widget.
        Tags previously created in __init__: kw, comment, string, number, func
        """
        try:
            import re
        except Exception:
            return
        code = widget.get("1.0", "end-1c")
        widget.tag_remove("kw", "1.0", "end")
        widget.tag_remove("comment", "1.0", "end")
        widget.tag_remove("string", "1.0", "end")
        widget.tag_remove("number", "1.0", "end")
        widget.tag_remove("func", "1.0", "end")

        # comments: // to end of line
        for m in re.finditer(r"//.*", code):
            start = f"1.0+{m.start()}c"
            end = f"1.0+{m.end()}c"
            widget.tag_add("comment", start, end)
        # strings: "..." or '...'
        for m in re.finditer(r"('(?:\\.|[^'])*'|\"(?:\\.|[^\"])*\")", code):
            start = f"1.0+{m.start()}c"
            end = f"1.0+{m.end()}c"
            widget.tag_add("string", start, end)
        # numbers
        for m in re.finditer(r"\b\d+(\.\d+)?\b", code):
            start = f"1.0+{m.start()}c"
            end = f"1.0+{m.end()}c"
            widget.tag_add("number", start, end)
        # functions heuristic: word followed by (
        for m in re.finditer(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*(?=\()", code):
            start = f"1.0+{m.start(1)}c"
            end = f"1.0+{m.end(1)}c"
            widget.tag_add("func", start, end)
        # keywords
        kws = ["if","else","for","while","repeat","return","break","continue","var","global","with","switch","case","default","function","do","until"]
        for kw in kws:
            for m in re.finditer(rf"\b{kw}\b", code):
                start = f"1.0+{m.start()}c"
                end = f"1.0+{m.end()}c"
                widget.tag_add("kw", start, end)

    def show_chunk(self, meta):
        self.room_canvas.pack_forget()
        name = meta.get("name"); off = meta.get("offset"); size = meta.get("size"); cs = meta.get("cs"); ce = meta.get("ce")
        self.preview_title.config(text=f"Chunk {name} @ {off}")
        self.image_label.config(image='', text='')
        self.image_label.image = None
        self.text_preview.pack(fill=tk.BOTH, expand=True, padx=6, pady=6)
        self.text_preview.configure(state=tk.NORMAL)
        self.text_preview.delete("1.0", tk.END)
        self.text_preview.insert(tk.END, f"Chunk '{name}' at offset {off}\nSize: {size}\nContent range: {cs}..{ce}\n\nHex preview:\n")
        if self.raw:
            sample = self.raw[cs: cs + min(size, 512)]
            hexp = " ".join(f"{b:02X}" for b in sample)
            self.text_preview.insert(tk.END, hexp)
        self.text_preview.configure(state=tk.DISABLED)
        self.play_btn.config(state=tk.DISABLED)
        self.stop_btn.config(state=tk.DISABLED)
        self.wave_btn.config(state=tk.DISABLED)
        self.audio_status.config(text="")

    def show_image(self, idx):
        self.room_canvas.pack_forget()
        entry = self.images[idx]
        name = entry.get("name")
        self.preview_title.config(text=f"Image: {name}")
        self.text_preview.pack(fill=tk.BOTH, expand=True, padx=6, pady=6)
        self.text_preview.configure(state=tk.NORMAL)
        self.text_preview.delete("1.0", tk.END)
        self.text_preview.insert(tk.END, f"Name hint: {name}\nRange: {entry.get('start')}..{entry.get('end')}\n")
        self.text_preview.configure(state=tk.DISABLED)
        # load PIL lazily if not loaded
        if entry.get("pil") is None:
            try:
                blob = self._read_range(entry["start"], entry["end"])
                pil = Image.open(io.BytesIO(blob)).convert("RGBA")
                entry["pil"] = pil
                # free blob by not storing it
            except Exception:
                entry["pil"] = None
        pil = entry.get("pil")
        if pil:
            maxw, maxh = 780, 420
            w, h = pil.size
            scale = min(maxw / w, maxh / h, 1.0)
            if scale < 1.0:
                disp = pil.resize((int(w*scale), int(h*scale)), Image.LANCZOS)
            else:
                disp = pil
            tkimg = ImageTk.PhotoImage(disp)
            self.image_label.config(image=tkimg)
            self.image_label.image = tkimg
        else:
            self.image_label.config(image='', text='(could not decode image)')
        self.play_btn.config(state=tk.DISABLED)
        self.stop_btn.config(state=tk.DISABLED)
        self.wave_btn.config(state=tk.DISABLED)
        self.audio_status.config(text="")

    def show_sound(self, idx):
        self.room_canvas.pack_forget()
        entry = self.sounds[idx]
        name = entry.get("name"); atype = entry.get("type")
        self.preview_title.config(text=f"Sound: {name} ({atype})")
        self.image_label.config(image='', text='')
        self.image_label.image = None
        self.text_preview.pack(fill=tk.BOTH, expand=True, padx=6, pady=6)
        self.text_preview.configure(state=tk.NORMAL)
        self.text_preview.delete("1.0", tk.END)
        self.text_preview.insert(tk.END, f"Name hint: {name}\nType: {atype}\nRange: {entry.get('start')}..{entry.get('end')}\n\nClick Play or Waveform.")
        self.text_preview.configure(state=tk.DISABLED)
        # enable audio controls
        self.play_btn.config(state=tk.NORMAL if (SIMPLEAUDIO_OK or PYGAME_OK or True) else tk.DISABLED)
        self.stop_btn.config(state=tk.NORMAL if (SIMPLEAUDIO_OK or PYGAME_OK or True) else tk.DISABLED)
        self.wave_btn.config(state=tk.NORMAL if (MATPLOTLIB_OK and NUMPY_OK) else tk.DISABLED)
        self.audio_status.config(text="Ready")
        self.current_sound_index = idx

    # ------------------------------
    # Audio playback & waveform (reads ranges lazily)
    # ------------------------------
    def _save_temp_sound(self, blob, typ):
        ext = ".wav" if typ == "wav" else ".ogg"
        tf = tempfile.NamedTemporaryFile(delete=False, suffix=ext)
        tf.write(blob)
        tf.flush()
        tf.close()
        return tf.name

    def play_audio(self):
        idx = getattr(self, "current_sound_index", None)
        if idx is None:
            return
        entry = self.sounds[idx]
        blob = self._read_range(entry["start"], entry["end"])
        typ = entry.get('type', 'wav')
        try:
            path = self._save_temp_sound(blob, typ)
            self.current_sound_tempfile = path
            # try simpleaudio first (works for wav)
            if SIMPLEAUDIO_OK and typ == "wav":
                try:
                    wave_obj = sa.WaveObject.from_wave_file(path)
                    play_obj = wave_obj.play()
                    self.playing_obj = play_obj
                    self.audio_status.config(text=f"Playing (simpleaudio): {os.path.basename(path)}")
                    return
                except Exception:
                    pass
            # fallback to pygame if available
            if PYGAME_OK:
                try:
                    pygame.mixer.stop()
                    sound = pygame.mixer.Sound(path)
                    sound.play()
                    self.audio_status.config(text=f"Playing (pygame): {os.path.basename(path)}")
                    return
                except Exception:
                    pass
            # last fallback: try os start (may open external player)
            try:
                if sys.platform.startswith("win"):
                    os.startfile(path)
                elif sys.platform.startswith("darwin"):
                    os.system(f'open "{path}"')
                else:
                    os.system(f'xdg-open "{path}" &')
                self.audio_status.config(text=f"Opened external player for {os.path.basename(path)}")
            except Exception:
                messagebox.showerror("Audio", "Could not play audio on this system.")
        except Exception as e:
            messagebox.showerror("Audio error", f"Could not play audio: {e}")

    def stop_audio(self):
        try:
            if getattr(self, "playing_obj", None):
                try:
                    self.playing_obj.stop()
                except Exception:
                    pass
                self.playing_obj = None
        except Exception:
            pass
        try:
            if PYGAME_OK:
                pygame.mixer.stop()
        except Exception:
            pass
        self.audio_status.config(text="Stopped")
        if getattr(self, "current_sound_tempfile", None):
            try:
                os.unlink(self.current_sound_tempfile)
            except Exception:
                pass
            self.current_sound_tempfile = None

    def show_waveform(self):
        idx = getattr(self, "current_sound_index", None)
        if idx is None:
            return
        entry = self.sounds[idx]
        blob = self._read_range(entry["start"], entry["end"])
        typ = entry.get('type','wav')

        # try to decode to samples using pydub or wave+numpy
        samples = None
        sr = None
        if PYDUB_OK:
            try:
                audio = AudioSegment.from_file(io.BytesIO(blob), format=typ)
                sr = audio.frame_rate
                channels = audio.channels
                arr = audio.get_array_of_samples()
                import numpy as _np_local
                if channels > 1:
                    a = _np_local.array(arr).reshape((-1, channels))
                    samples = a.mean(axis=1)
                else:
                    samples = _np_local.array(arr)
            except Exception:
                samples = None
        else:
            try:
                import wave, numpy as _np_local
                bf = io.BytesIO(blob)
                wf = wave.open(bf, 'rb')
                sr = wf.getframerate()
                frames = wf.readframes(wf.getnframes())
                sampwidth = wf.getsampwidth()
                dtype = None
                if sampwidth == 1:
                    dtype = 'int8'
                elif sampwidth == 2:
                    dtype = 'int16'
                elif sampwidth == 4:
                    dtype = 'int32'
                else:
                    dtype = 'int16'
                samples = _np_local.frombuffer(frames, dtype=_np_local.dtype(dtype))
                if wf.getnchannels() > 1:
                    samples = samples.reshape((-1, wf.getnchannels()))
                    samples = samples.mean(axis=1)
                wf.close()
            except Exception:
                samples = None

        if samples is None or not MATPLOTLIB_OK:
            messagebox.showinfo("Waveform", "Could not decode audio for waveform (requires pydub/numpy or wave+numpy and matplotlib).")
            return

        win = tk.Toplevel(self.root)
        win.title(f"Waveform - {entry.get('name')}")
        fig, ax = plt.subplots(figsize=(8, 3))
        times = (1.0 * _np.arange(len(samples))) / float(sr if sr else 44100)
        ax.plot(times, samples)
        ax.set_xlabel("Seconds")
        ax.set_ylabel("Amplitude")
        fig.tight_layout()
        canvas = FigureCanvasTkAgg(fig, master=win)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

    # ------------------------------
    # Room visualizer (heuristic)
    # ------------------------------
    def show_room(self, room_name):
        # Hide text preview and image label; show canvas
        try:
            self.text_preview.pack_forget()
            self.image_label.pack_forget()
        except Exception:
            pass
        self.preview_title.config(text=f"Room: {room_name}")
        self.room_canvas.pack(fill=tk.BOTH, expand=True, padx=6, pady=6)
        self.room_canvas.delete("all")

        # grid settings
        cols, rows = 20, 15
        w = max(640, self.room_canvas.winfo_width() or 640)
        h = max(480, self.room_canvas.winfo_height() or 480)
        cell_w = w // cols
        cell_h = h // rows
        self.room_canvas.config(width=w, height=h)

        # draw grid
        for i in range(cols+1):
            x = i * cell_w
            self.room_canvas.create_line(x, 0, x, h, fill="#444444")
        for j in range(rows+1):
            y = j * cell_h
            self.room_canvas.create_line(0, y, w, y, fill="#444444")

        # title in center
        self.room_canvas.create_text(w//2, 18, text=room_name, fill="white", font=("Segoe UI", 14, "bold"))

        # Heuristic: try to find object names nearby in raw and place icons deterministically
        found_objects = []
        if self.raw:
            # search for room_name occurrence and get window around it
            try:
                b = room_name.encode('utf-8')
                pos = self.raw.find(b)
                if pos != -1:
                    window = self.raw[max(0,pos-4096): pos+4096]
                    for obj in self.objects:
                        if obj.encode('utf-8') in window:
                            found_objects.append(obj)
            except Exception:
                pass
        # fallback: show first N objects if none matched
        if not found_objects:
            found_objects = self.objects[:min(10, len(self.objects))]

        # place found_objects deterministically using hash of name (so it's stable)
        for i, objname in enumerate(found_objects):
            # deterministic pseudo-random position within grid
            hval = int(hashlib.sha1(objname.encode('utf-8')).hexdigest()[:8], 16)
            col = hval % cols
            row = (hval >> 8) % rows
            cx = col * cell_w + cell_w//2
            cy = row * cell_h + cell_h//2
            # draw a small rectangle or icon
            rect = self.room_canvas.create_rectangle(cx-12, cy-12, cx+12, cy+12, fill="#FFA500", outline="#000000")
            txt = self.room_canvas.create_text(cx, cy+20, text=objname, anchor="n", fill="white", font=("Segoe UI", 8))
        # also show list of objects in text preview area below
        self.text_preview.pack(fill=tk.BOTH, expand=False, padx=6, pady=(4,6))
        self.text_preview.configure(state=tk.NORMAL)
        self.text_preview.delete("1.0", tk.END)
        if found_objects:
            self.text_preview.insert(tk.END, "Objects (heuristic):\n")
            for o in found_objects:
                self.text_preview.insert(tk.END, "- " + o + "\n")
        else:
            self.text_preview.insert(tk.END, "No objects detected for this room (heuristic).")
        self.text_preview.configure(state=tk.DISABLED)
        self.play_btn.config(state=tk.DISABLED)
        self.stop_btn.config(state=tk.DISABLED)
        self.wave_btn.config(state=tk.DISABLED)
        self.audio_status.config(text="")

# ---------------------------------------------------------------------------
# Run
# ---------------------------------------------------------------------------
def main():
    root = tk.Tk()
    app = GMViewerApp(root)
    root.mainloop()

if __name__ == "__main__":
    main()
