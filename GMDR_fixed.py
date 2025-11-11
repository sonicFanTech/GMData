# gm_viewer_qt.py
# GameMaker Read-Only Viewer (PySide6)
# - Tabs: Text | Room | Info
# - Tools -> Show Chunks (checkable view filters)
# - Help -> About (rich window)
# - Sprites (no Images category) with lazy decoding and grouping by `spr_*`
# - Room viewer: zoom (wheel), pan (drag), draws sprites at detected instance coords (heuristic)
# - Export (context menu) + Export All
# - GML syntax highlighting

import io, os, sys, time, struct, re, tempfile, math, threading

from PIL import Image
from PySide6 import QtCore, QtGui, QtWidgets

# ---------- Optional libs ----------
SIMPLEAUDIO_OK = False
try:
    import simpleaudio as sa
    SIMPLEAUDIO_OK = True
except Exception:
    pass

PYGAME_OK = False
try:
    import pygame
    pygame.mixer.init()
    PYGAME_OK = True
except Exception:
    pass

MATPLOTLIB_OK = False
NUMPY_OK = False
try:
    import numpy as _np
    NUMPY_OK = True
    import matplotlib
    matplotlib.use("Agg")  # we'll embed via canvas pixmap
    import matplotlib.pyplot as plt
    MATPLOTLIB_OK = True
except Exception:
    pass

PYDUB_OK = False
try:
    from pydub import AudioSegment
    PYDUB_OK = True
except Exception:
    pass
# -----------------------------------


# ---------- Low-level parsing helpers ----------
UPPER_A, UPPER_Z = 65, 90

def is_ascii_upper4(b: bytes) -> bool:
    return len(b) == 4 and all(UPPER_A <= x <= UPPER_Z for x in b)

def read_u32_le(data: bytes, off: int):
    if off + 4 <= len(data):
        return struct.unpack_from("<I", data, off)[0]
    return None

def recursive_find_chunks(data: bytes, start: int, end: int):
    """Find nested chunks: 4CC + u32 size + data."""
    out = []
    i, n = start, end
    while i < n - 8:
        tag = data[i:i+4]
        if is_ascii_upper4(tag):
            size = read_u32_le(data, i+4)
            if size is not None and size > 0:
                cs, ce = i+8, i+8+size
                if start <= cs <= ce <= end:
                    out.append((tag.decode('ascii'), i, size, cs, ce))
                    out.extend(recursive_find_chunks(data, cs, ce))
                    i = ce
                    continue
        i += 1
    return out

def find_top_form(data: bytes):
    if data.startswith(b"FORM"):
        size = read_u32_le(data, 4)
        if size:
            cs, ce = 8, 8+size
            if ce <= len(data):
                return (0, cs, ce)
    # fallback around GEN8
    gen = data.find(b"GEN8")
    if gen != -1:
        back = max(0, gen - 64)
        form = data.find(b"FORM", back, gen)
        if form != -1:
            size = read_u32_le(data, form+4)
            if size:
                cs, ce = form+8, form+8+size
                if ce <= len(data):
                    return (form, cs, ce)
    return (None, 0, len(data))

def extract_strings_from_region(data: bytes, start: int, end: int):
    seg = data[start:end]
    out, off = [], 0
    while True:
        n = seg.find(b"\x00", off)
        if n == -1:
            break
        raw = seg[off:n]
        s = None
        try:
            s = raw.decode("utf-8")
        except Exception:
            try:
                s = raw.decode("latin-1", errors="ignore")
            except Exception:
                s = None
        if s and any(ch.isalnum() for ch in s):
            out.append(s)
        off = n + 1
    # dedupe keep-order
    seen, uniq = set(), []
    for s in out:
        if s not in seen:
            seen.add(s)
            uniq.append(s)
    return uniq

def find_pngs_offsets(data: bytes, start: int, end: int):
    """List of (abs_start, abs_end) of PNGs within region."""
    seg = data[start:end]
    sig = b"\x89PNG\r\n\x1a\n"
    i, out = 0, []
    while True:
        p = seg.find(sig, i)
        if p == -1:
            break
        iend = seg.find(b"IEND", p)
        if iend == -1:
            break
        abs_s = start + p
        abs_e = start + iend + 8
        if abs_e > end:
            abs_e = end
        out.append((abs_s, abs_e))
        i = iend + 8
    return out

def find_audio_offsets(data: bytes, start: int, end: int):
    """Heuristic RIFF/WAV and OggS finder: [(start, end, type), ...]."""
    seg = data[start:end]
    out = []

    # WAV
    i = 0
    while True:
        p = seg.find(b"RIFF", i)
        if p == -1:
            break
        abs_p = start + p
        if p + 8 <= len(seg):
            size = struct.unpack_from("<I", seg, p+4)[0]
            total = 8 + size
            if p + total <= len(seg):
                out.append((abs_p, start + p + total, "wav"))
                i = p + total
            else:
                out.append((abs_p, end, "wav"))
                break
        else:
            break

    # OGG
    i = 0
    while True:
        p = seg.find(b"OggS", i)
        if p == -1:
            break
        abs_p = start + p
        nxt = seg.find(b"OggS", p+4)
        abs_e = start + (nxt if nxt != -1 else len(seg))
        out.append((abs_p, abs_e, "ogg"))
        i = nxt if nxt != -1 else len(seg)

    return out

def safe_decode_text(blob: bytes):
    try:
        return blob.decode("utf-8", errors="strict")
    except Exception:
        try:
            return blob.decode("latin-1", errors="ignore")
        except Exception:
            return None
# ------------------------------------------------------


# ---------- GML syntax highlighter ----------
class GmlHighlighter(QtGui.QSyntaxHighlighter):
    def __init__(self, doc: QtGui.QTextDocument):
        super().__init__(doc)
        self.kw_format = QtGui.QTextCharFormat()
        self.kw_format.setForeground(QtGui.QColor("#c586c0"))
        self.num_format = QtGui.QTextCharFormat()
        self.num_format.setForeground(QtGui.QColor("#b5cea8"))
        self.str_format = QtGui.QTextCharFormat()
        self.str_format.setForeground(QtGui.QColor("#ce9178"))
        self.cmt_format = QtGui.QTextCharFormat()
        self.cmt_format.setForeground(QtGui.QColor("#6a9955"))

        self.kw_re = re.compile(r"\b(var|if|else|for|while|do|switch|case|break|continue|return|with|repeat|until|function|enum|try|catch|finally|and|or|not|true|false)\b")
        self.num_re = re.compile(r"\b(?:0x[0-9A-Fa-f]+|\d+(?:\.\d+)?(?:e[+-]?\d+)?)\b")
        self.str_re = re.compile(r"\"([^\"\\]|\\.)*\"|'([^'\\]|\\.)*'")
        self.c1_re = re.compile(r"//.*?$", re.MULTILINE)
        self.c2_re = re.compile(r"/\*.*?\*/", re.DOTALL)

    def highlightBlock(self, text: str):
        # multi-line comments
        for m in self.c2_re.finditer(text):
            start, end = m.span()
            self.setFormat(start, end-start, self.cmt_format)

        # single-line comments
        for m in self.c1_re.finditer(text):
            start, end = m.span()
            self.setFormat(start, end-start, self.cmt_format)

        for m in self.str_re.finditer(text):
            start, end = m.span()
            self.setFormat(start, end-start, self.str_format)
        for m in self.num_re.finditer(text):
            start, end = m.span()
            self.setFormat(start, end-start, self.num_format)
        for m in self.kw_re.finditer(text):
            start, end = m.span()
            self.setFormat(start, end-start, self.kw_format)
# ------------------------------------------------------


# ---------- Room view (zoom+pan) ----------
class RoomView(QtWidgets.QGraphicsView):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setScene(QtWidgets.QGraphicsScene(self))
        self.setRenderHint(QtGui.QPainter.Antialiasing, True)
        self.setDragMode(QtWidgets.QGraphicsView.ScrollHandDrag)
        self.setBackgroundBrush(QtGui.QBrush(QtGui.QColor("#1e1e1e")))
        self._zoom = 0

    def wheelEvent(self, event: QtGui.QWheelEvent):
        # zoom around cursor
        if event.angleDelta().y() == 0:
            return
        factor = 1.15 if event.angleDelta().y() > 0 else 1/1.15
        self._zoom += 1 if factor > 1 else -1
        if self._zoom < -30:  # min zoom
            self._zoom = -30; return
        self.scale(factor, factor)
# ------------------------------------------------------


# ---------- Loading dialog ----------
class LoadingDialog(QtWidgets.QDialog):
    def __init__(self, title="Loading...", parent=None):
        super().__init__(parent)
        self.setWindowTitle(title)
        self.setModal(True)
        self.setFixedSize(500, 135)
        v = QtWidgets.QVBoxLayout(self)
        self.title_lbl = QtWidgets.QLabel(f"<b>{title}</b>")
        self.status_lbl = QtWidgets.QLabel("Starting…")
        self.bar = QtWidgets.QProgressBar()
        v.addWidget(self.title_lbl)
        v.addWidget(self.status_lbl)
        v.addWidget(self.bar)
        self.bar.setRange(0, 100)

    @QtCore.Slot(int)
    def setMax(self, m: int):
        self.bar.setMaximum(max(1, int(m)))

    @QtCore.Slot(str)
    def setStatus(self, s: str):
        self.status_lbl.setText(s)

    @QtCore.Slot(int)
    def step(self, n: int = 1):
        self.bar.setValue(min(self.bar.maximum(), self.bar.value() + n))
# ------------------------------------------------------


# ---------- Worker (QThread) ----------
class ParseResult(QtCore.QObject):
    def __init__(self):
        super().__init__()
        self.raw = b""
        self.form_bounds = (None, 0, 0)
        self.chunks = []          # (name, off, size, cs, ce)
        self.strings = []
        self.sounds = []          # {name,pos,end,type}
        self.sprite_frames = []   # [{name,pos,end,pix=None}, ...]
        self.sprite_groups = {}   # name -> [frame indices]
        self.scripts = []
        self.rooms = []
        self.objects = []
        self.fonts = []

class ParserWorker(QtCore.QThread):
    progressMax = QtCore.Signal(int)
    progressStep = QtCore.Signal(int)
    progressText = QtCore.Signal(str)
    done = QtCore.Signal(object, str)

    def __init__(self, path: str):
        super().__init__()
        self.path = path

    def run(self):
        pr = ParseResult()
        try:
            self.progressText.emit("Reading file…")
            with open(self.path, "rb") as f:
                data = f.read()
            pr.raw = data

            self.progressText.emit("Locating FORM/GEN8…")
            formpos, cs, ce = find_top_form(data)
            pr.form_bounds = (formpos, cs, ce)

            self.progressText.emit("Scanning for chunks…")
            chunks = recursive_find_chunks(data, cs, ce)
            if formpos is not None:
                chunks.insert(0, ("FORM", formpos, ce-cs, cs, ce))
            seen, dedup = set(), []
            for c in chunks:
                key = (c[0], c[1])
                if key not in seen:
                    seen.add(key); dedup.append(c)
            pr.chunks = dedup

            # counts for progress
            png_total, aud_total = 0, 0
            for (nm, off, size, c1, c2) in pr.chunks:
                if nm == "TXTR":
                    png_total += len(find_pngs_offsets(data, c1, c2))
                if nm == "AUDO":
                    aud_total += len(find_audio_offsets(data, c1, c2))
            if png_total == 0 and cs < ce:
                png_total = len(find_pngs_offsets(data, cs, ce))
            if aud_total == 0 and cs < ce:
                aud_total = len(find_audio_offsets(data, cs, ce))

            total = max(1, len(pr.chunks) + 1 + 1 + png_total + aud_total + 1)
            self.progressMax.emit(total)
            for (nm, off, size, c1, c2) in pr.chunks:
                self.progressText.emit(f"Found chunk: {nm} @ {off}")
                self.progressStep.emit(1)

            # strings
            self.progressText.emit("Collecting strings (STRG + scan)…")
            strings = []
            for (nm, off, size, c1, c2) in pr.chunks:
                if nm == "STRG":
                    strings.extend(extract_strings_from_region(data, c1, c2))
            if not strings and cs < ce:
                strings.extend(extract_strings_from_region(data, cs, ce))
            # de-dupe
            seen, uniq = set(), []
            for s in strings:
                if s not in seen:
                    seen.add(s); uniq.append(s)
            pr.strings = uniq
            self.progressStep.emit(1)

            # sprite frames offsets (from TXTR PNGs) but shown as "Sprites"
            self.progressText.emit("Indexing sprites (PNG frames)…")
            sprite_frames = []
            pngs = []
            for (nm, off, size, c1, c2) in pr.chunks:
                if nm == "TXTR":
                    pngs.extend(find_pngs_offsets(data, c1, c2))
            if not pngs and cs < ce:
                pngs = find_pngs_offsets(data, cs, ce)
            for (p0, p1) in pngs:
                name_guess = None
                for s in pr.strings:
                    try:
                        loc = data.find(s.encode("utf-8"))
                        if loc != -1 and abs(loc - p0) < 4096:
                            name_guess = s; break
                    except Exception:
                        pass
                sprite_frames.append({"name": name_guess or f"spr_frame_{p0}", "pos": p0, "end": p1, "pix": None})
                self.progressStep.emit(1)
            pr.sprite_frames = sprite_frames

            # audio offsets
            self.progressText.emit("Indexing audio…")
            auds = []
            for (nm, off, size, c1, c2) in pr.chunks:
                if nm == "AUDO":
                    auds.extend(find_audio_offsets(data, c1, c2))
            if not auds and cs < ce:
                auds = find_audio_offsets(data, cs, ce)
            sounds = []
            for (p0,p1,typ) in auds:
                name_guess = None
                for s in pr.strings:
                    try:
                        loc = data.find(s.encode("utf-8"))
                        if loc != -1 and abs(loc - p0) < 4096:
                            name_guess = s; break
                    except Exception:
                        pass
                sounds.append({"name": name_guess or f"audio_{p0}", "pos": p0, "end": p1, "type": typ})
                self.progressStep.emit(1)
            pr.sounds = sounds

            # scripts / rooms / objects / fonts
            self.progressText.emit("Collecting scripts/rooms/objects/fonts…")
            pr.scripts = [s for s in pr.strings if s.startswith(("scr_","gml_","script_","gml_Script"))]
            pr.rooms   = [s for s in pr.strings if s.startswith("room_")]
            pr.objects = [s for s in pr.strings if s.startswith("obj_")]
            pr.fonts   = [s for s in pr.strings if s.startswith("fnt_")]

            # group frames by spr_* root
            groups = {}
            for idx, fr in enumerate(pr.sprite_frames):
                nm = (fr.get("name") or "").lower()
                if nm.startswith("spr_"):
                    root = nm.split("_frame")[0]
                    groups.setdefault(root, []).append(idx)
            pr.sprite_groups = groups

            self.progressStep.emit(1)
            self.done.emit(pr, "")
        except Exception as e:
            self.done.emit(ParseResult(), f"{type(e).__name__}: {e}")
# ------------------------------------------------------


# ---------- Main window ----------
class MainWindow(QtWidgets.QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("GameMaker Read-Only Viewer (PySide6)")
        self.resize(1320, 820)

        # Data
        self.raw = b""
        self.form_bounds = (None, 0, 0)
        self.chunks = []
        self.strings = []
        self.sounds = []         # dicts
        self.sprite_frames = []  # dicts
        self.sprite_groups = {}  # name -> [indices]
        self.scripts = []
        self.rooms = []
        self.objects = []
        self.fonts = []

        self.current_sound_temp = None
        self.current_sound_index = None
        self.filters = {
            "chunks": True, "strings": True, "sprites": True, "sounds": True,
            "scripts": True, "rooms": True, "objects": True, "fonts": True
        }

        # ----- UI layout -----
        central = QtWidgets.QWidget()
        self.setCentralWidget(central)
        grid = QtWidgets.QGridLayout(central)
        grid.setContentsMargins(6,6,6,6)

        # Top search
        self.search = QtWidgets.QLineEdit()
        self.search.setPlaceholderText("Search…")
        self.search.textChanged.connect(self.populate_tree)
        grid.addWidget(self.search, 0, 0, 1, 2)

        # Splitter
        split = QtWidgets.QSplitter()
        split.setOrientation(QtCore.Qt.Horizontal)
        grid.addWidget(split, 1, 0, 1, 2)

        # Left: tree
        left = QtWidgets.QWidget(); lv = QtWidgets.QVBoxLayout(left); lv.setContentsMargins(0,0,0,0)
        self.tree = QtWidgets.QTreeWidget()
        self.tree.setHeaderHidden(True)
        self.tree.itemSelectionChanged.connect(self.on_tree_sel)
        self.tree.setContextMenuPolicy(QtCore.Qt.CustomContextMenu)
        self.tree.customContextMenuRequested.connect(self.show_tree_menu)
        lv.addWidget(self.tree)
        split.addWidget(left)

        # Right: tabs
        self.tabs = QtWidgets.QTabWidget()
        split.addWidget(self.tabs)

        # Text tab
        text_wrap = QtWidgets.QWidget(); tlay = QtWidgets.QVBoxLayout(text_wrap); tlay.setContentsMargins(6,6,6,6)
        self.text_edit = QtWidgets.QPlainTextEdit()
        self.text_edit.setReadOnly(True)
        self.highlighter = GmlHighlighter(self.text_edit.document())
        tlay.addWidget(self.text_edit)
        self.tabs.addTab(text_wrap, "Text")

        # Room tab
        room_wrap = QtWidgets.QWidget(); rlay = QtWidgets.QVBoxLayout(room_wrap); rlay.setContentsMargins(6,6,6,6)
        self.room_view = RoomView()
        rlay.addWidget(self.room_view)
        self.tabs.addTab(room_wrap, "Room")

        # Info tab
        info_wrap = QtWidgets.QWidget(); ilay = QtWidgets.QVBoxLayout(info_wrap); ilay.setContentsMargins(6,6,6,6)
        self.info_edit = QtWidgets.QPlainTextEdit()
        self.info_edit.setReadOnly(True)
        ilay.addWidget(self.info_edit)

        # Audio controls (appear when a sound is selected)
        arow = QtWidgets.QHBoxLayout()
        self.play_btn = QtWidgets.QPushButton("Play"); self.play_btn.clicked.connect(self.play_audio); self.play_btn.setEnabled(False)
        self.stop_btn = QtWidgets.QPushButton("Stop"); self.stop_btn.clicked.connect(self.stop_audio); self.stop_btn.setEnabled(False)
        self.wave_btn = QtWidgets.QPushButton("Waveform"); self.wave_btn.clicked.connect(self.show_waveform); self.wave_btn.setEnabled(False)
        self.audio_lbl = QtWidgets.QLabel()
        arow.addWidget(self.play_btn); arow.addWidget(self.stop_btn); arow.addWidget(self.wave_btn); arow.addWidget(self.audio_lbl, 1)
        ilay.addLayout(arow)

        self.tabs.addTab(info_wrap, "Info")

        split.setStretchFactor(0, 1)   # tree
        split.setStretchFactor(1, 3)   # tabs

        # ----- Menus -----
        bar = self.menuBar()

        filem = bar.addMenu("&File")
        act_open = filem.addAction("Open…")
        act_open.triggered.connect(self.open_file)
        filem.addSeparator()
        act_export_all = filem.addAction("Export all assets…")
        act_export_all.triggered.connect(self.export_all)
        filem.addSeparator()
        filem.addAction("Exit", self.close)

        toolsm = bar.addMenu("&Tools")
        self.show_menu = toolsm.addMenu("Show &Chunks")
        self.actions_filters = {}
        for key, label in [
            ("chunks","Chunks"), ("strings","Strings"), ("sprites","Sprites"),
            ("sounds","Sounds"), ("scripts","Scripts"), ("rooms","Rooms"),
            ("objects","Objects"), ("fonts","Fonts")
        ]:
            a = QtGui.QAction(label, self, checkable=True, checked=self.filters[key])
            a.toggled.connect(self.populate_tree)
            self.show_menu.addAction(a)
            self.actions_filters[key] = a

        helpm = bar.addMenu("&Help")
        about = helpm.addAction("&About…")
        about.triggered.connect(self.show_about)

        # Defaults in Info tab
        self.set_info("Open a data.win/.wim to begin.")

    # --------- About Dialog ---------
    def show_about(self):
        dlg = QtWidgets.QDialog(self)
        dlg.setWindowTitle("About — GameMaker Read-Only Viewer")
        dlg.resize(640, 520)
        v = QtWidgets.QVBoxLayout(dlg)
        lbl = QtWidgets.QLabel()
        lbl.setTextFormat(QtCore.Qt.RichText)
        lbl.setWordWrap(True)
        lbl.setText(
            "<h2>GameMaker Read-Only Viewer</h2>"
            "<p>This open-source tool lets you inspect GameMaker <code>data.win/.wim</code> files.</p>"
            "<ul>"
            "<li><b>Tabs:</b> <i>Text</i> (scripts/strings/code), <i>Room</i> (zoomable viewer), <i>Info</i> (details).</li>"
            "<li><b>Tools → Show Chunks:</b> toggle categories shown in the left tree.</li>"
            "<li><b>Right-click</b> any item in the tree to Export or Copy Name.</li>"
            "<li><b>Sprites:</b> frames grouped by <code>spr_*</code> name, decoded lazily from embedded PNGs.</li>"
            "<li><b>Room viewer:</b> heuristically places instances using discovered <code>(x,y)</code> pairs. "
            "If a sprite can't be matched, a labeled dot is drawn.</li>"
            "<li><b>Audio:</b> WAV/OGG detection; playback via simpleaudio/pygame; optional waveform via matplotlib+numpy.</li>"
            "</ul>"
            "<p><b>Note:</b> Parsing is heuristic (safe/read-only). Some titles may require tweaks.</p>"
        )
        v.addWidget(lbl)
        btn = QtWidgets.QDialogButtonBox(QtWidgets.QDialogButtonBox.Ok)
        btn.accepted.connect(dlg.accept)
        v.addWidget(btn)
        dlg.show()

    # --------- Open / parse ---------
    def open_file(self):
        path, _ = QtWidgets.QFileDialog.getOpenFileName(self, "Open GameMaker data.win / .wim",
                                                        "", "GameMaker Data (*.wim *.win);;All files (*)")
        if not path:
            return
        self.loading = LoadingDialog(f"Loading {os.path.basename(path)}", self)
        self.loading.show()

        self.worker = ParserWorker(path)
        self.worker.progressMax.connect(self.loading.setMax)
        self.worker.progressStep.connect(self.loading.step)
        self.worker.progressText.connect(self.loading.setStatus)
        self.worker.done.connect(self.on_parsed)
        self.worker.start()

    @QtCore.Slot(ParseResult, str)
    def on_parsed(self, pr: "ParseResult", err: str):
        self.loading.close()
        if err:
            QtWidgets.QMessageBox.critical(self, "Error", f"Failed to parse: {err}")
            return

        # adopt result
        self.raw = pr.raw
        self.form_bounds = pr.form_bounds
        self.chunks = pr.chunks
        self.strings = pr.strings
        self.sounds = pr.sounds
        self.sprite_frames = pr.sprite_frames
        self.sprite_groups = pr.sprite_groups
        self.scripts = pr.scripts
        self.rooms = pr.rooms
        self.objects = pr.objects
        self.fonts = pr.fonts

        self.populate_tree()
        self.set_info(f"Loaded. FORM region: {self.form_bounds}. "
                      f"{len(self.sprite_frames)} sprite frames, {len(self.sounds)} sounds, "
                      f"{len(self.strings)} strings.")

    # --------- Tree population & search ---------
    def populate_tree(self):
        self.tree.clear()
        q = (self.search.text() or "").lower().strip()
        def match(s: str) -> bool:
            return (not q) or (q in s.lower())

        # reflect menu checks into filters
        for key, act in self.actions_filters.items():
            self.filters[key] = act.isChecked()

        # Data (UMT-style top node) – purely navigational
        data_root = QtWidgets.QTreeWidgetItem(["Data"])
        self.tree.addTopLevelItem(data_root)
        for label in [
            "General info", "Audio groups", "Variables", "Functions", "Code"
        ]:
            QtWidgets.QTreeWidgetItem(data_root, [label])
        data_root.setExpanded(True)

        # Chunks
        if self.filters["chunks"]:
            ch = QtWidgets.QTreeWidgetItem([f"Chunks ({len(self.chunks)})"])
            self.tree.addTopLevelItem(ch)
            for (nm, off, size, c1, c2) in self.chunks:
                label = f"{nm} @ {off} ({size} bytes)"
                if match(label):
                    it = QtWidgets.QTreeWidgetItem([label])
                    it.setData(0, QtCore.Qt.UserRole, {"type":"chunk","name":nm,"off":off,"size":size,"cs":c1,"ce":c2})
                    ch.addChild(it)

        # Strings
        if self.filters["strings"]:
            sr = QtWidgets.QTreeWidgetItem([f"Strings ({len(self.strings)})"])
            self.tree.addTopLevelItem(sr)
            for s in self.strings:
                if match(s):
                    it = QtWidgets.QTreeWidgetItem([s])
                    it.setData(0, QtCore.Qt.UserRole, {"type":"string","text":s})
                    sr.addChild(it)

        # Sprites (groups first)
        if self.filters["sprites"]:
            root = QtWidgets.QTreeWidgetItem([f"Sprites ({len(self.sprite_groups)})"])
            self.tree.addTopLevelItem(root)
            for gname, idxs in sorted(self.sprite_groups.items()):
                if match(gname):
                    git = QtWidgets.QTreeWidgetItem([f"{gname} ({len(idxs)} frames)"])
                    git.setData(0, QtCore.Qt.UserRole, {"type":"sprite_group","name":gname,"indices":idxs})
                    root.addChild(git)
            # orphan frames (no spr_* name)
            orphans = [i for i, fr in enumerate(self.sprite_frames)
                       if not (fr.get("name","").lower().startswith("spr_"))]
            if orphans:
                oroot = QtWidgets.QTreeWidgetItem([f"Other Frames ({len(orphans)})"])
                root.addChild(oroot)
                for i in orphans:
                    fr = self.sprite_frames[i]
                    label = f"{fr.get('name','frame')} @ {fr['pos']}"
                    if match(label):
                        it = QtWidgets.QTreeWidgetItem([label])
                        it.setData(0, QtCore.Qt.UserRole, {"type":"sprite_frame","index":i})
                        oroot.addChild(it)

        # Sounds
        if self.filters["sounds"]:
            ar = QtWidgets.QTreeWidgetItem([f"Sounds ({len(self.sounds)})"])
            self.tree.addTopLevelItem(ar)
            for i, snd in enumerate(self.sounds):
                label = f"{snd.get('name','sound')} ({snd.get('type')})"
                if match(label):
                    it = QtWidgets.QTreeWidgetItem([label])
                    it.setData(0, QtCore.Qt.UserRole, {"type":"sound","index":i})
                    ar.addChild(it)

        # Scripts
        if self.filters["scripts"]:
            scr = QtWidgets.QTreeWidgetItem([f"Scripts ({len(self.scripts)})"])
            self.tree.addTopLevelItem(scr)
            for s in self.scripts:
                if match(s):
                    it = QtWidgets.QTreeWidgetItem([s])
                    it.setData(0, QtCore.Qt.UserRole, {"type":"script","text":s})
                    scr.addChild(it)

        # Rooms
        if self.filters["rooms"]:
            rr = QtWidgets.QTreeWidgetItem([f"Rooms ({len(self.rooms)})"])
            self.tree.addTopLevelItem(rr)
            for r in self.rooms:
                if match(r):
                    it = QtWidgets.QTreeWidgetItem([r])
                    it.setData(0, QtCore.Qt.UserRole, {"type":"room","text":r})
                    rr.addChild(it)

        # Objects
        if self.filters["objects"]:
            oroot = QtWidgets.QTreeWidgetItem([f"Objects ({len(self.objects)})"])
            self.tree.addTopLevelItem(oroot)
            for o in self.objects:
                if match(o):
                    it = QtWidgets.QTreeWidgetItem([o])
                    it.setData(0, QtCore.Qt.UserRole, {"type":"object","text":o})
                    oroot.addChild(it)

        # Fonts
        if self.filters["fonts"]:
            froot = QtWidgets.QTreeWidgetItem([f"Fonts ({len(self.fonts)})"])
            self.tree.addTopLevelItem(froot)
            for f in self.fonts:
                if match(f):
                    it = QtWidgets.QTreeWidgetItem([f])
                    it.setData(0, QtCore.Qt.UserRole, {"type":"font","text":f})
                    froot.addChild(it)

        # Summary
        top = QtWidgets.QTreeWidgetItem(["Summary"])
        self.tree.addTopLevelItem(top)
        for line in [
            f"Sprite frames: {len(self.sprite_frames)}",
            f"Sounds: {len(self.sounds)}",
            f"Strings: {len(self.strings)}",
            f"Scripts: {len(self.scripts)}",
            f"Rooms: {len(self.rooms)}",
            f"Objects: {len(self.objects)}",
            f"Fonts: {len(self.fonts)}",
        ]:
            QtWidgets.QTreeWidgetItem(top, [line])

        self.tree.expandToDepth(0)

    # --------- Context menu on tree ---------
    def show_tree_menu(self, pos):
        it = self.tree.itemAt(pos)
        if not it:
            return
        meta = it.data(0, QtCore.Qt.UserRole) or {}
        menu = QtWidgets.QMenu(self)
        act_copy = menu.addAction("Copy name")
        act_export = menu.addAction("Export…")
        chosen = menu.exec_(self.tree.mapToGlobal(pos))
        if chosen == act_copy:
            QtWidgets.QApplication.clipboard().setText(it.text(0))
        elif chosen == act_export:
            self.export_item(meta)

    def export_item(self, meta):
        t = meta.get("type")
        if not t:
            return
        if t in ("string","script","room","object","font"):
            s = meta.get("text","")
            path, _ = QtWidgets.QFileDialog.getSaveFileName(self, "Export text", "", "Text (*.txt)")
            if not path: return
            with open(path, "w", encoding="utf-8") as f:
                f.write(s)
        elif t == "chunk":
            cs, ce = meta["cs"], meta["ce"]
            path, _ = QtWidgets.QFileDialog.getSaveFileName(self, "Export chunk", "", "Binary (*.bin)")
            if not path: return
            with open(path, "wb") as f: f.write(self.raw[cs:ce])
        elif t == "sound":
            idx = meta["index"]; snd = self.sounds[idx]
            ext = ".wav" if snd.get("type") == "wav" else ".ogg"
            path, _ = QtWidgets.QFileDialog.getSaveFileName(self, "Export sound", "", f"*{ext}")
            if not path: return
            with open(path, "wb") as f: f.write(self.raw[snd["pos"]:snd["end"]])
        elif t == "sprite_frame":
            idx = meta["index"]; fr = self.sprite_frames[idx]
            path, _ = QtWidgets.QFileDialog.getSaveFileName(self, "Export sprite frame", "", "*.png")
            if not path: return
            with open(path, "wb") as f: f.write(self.raw[fr["pos"]:fr["end"]])
        elif t == "sprite_group":
            dest = QtWidgets.QFileDialog.getExistingDirectory(self, "Export sprite frames to folder")
            if not dest: return
            name = meta["name"]
            for n, idx in enumerate(meta["indices"]):
                fr = self.sprite_frames[idx]
                p = os.path.join(dest, f"{name}_{n:03d}.png")
                with open(p, "wb") as f: f.write(self.raw[fr["pos"]:fr["end"]])
            QtWidgets.QMessageBox.information(self, "Export", "Sprite frames exported.")

    # --------- Selection handling ---------
    def on_tree_sel(self):
        it = self.tree.currentItem()
        if not it:
            return
        meta = it.data(0, QtCore.Qt.UserRole) or {}
        t = meta.get("type")
        if t == "string":
            self.show_text(meta["text"])
            self.set_info("String")
        elif t == "script":
            self.show_script(meta["text"])
        elif t == "room":
            self.show_room(meta["text"])
        elif t == "object":
            self.show_text(meta["text"])
            self.set_info("Object name (no body)")
        elif t == "chunk":
            self.show_chunk(meta)
        elif t == "sound":
            self.show_sound(meta["index"])
        elif t == "sprite_group":
            self.show_sprite_group(meta["name"], meta["indices"])
        elif t == "sprite_frame":
            self.show_sprite_frame(meta["index"])
        elif t == "font":
            self.show_font(meta["text"])

    # --------- Tabs updaters ---------
    def set_text(self, text: str):
        self.tabs.setCurrentIndex(0)
        self.text_edit.setPlainText(text)

    def set_info(self, text: str):
        self.tabs.setCurrentIndex(2)
        self.info_edit.setPlainText(text)

    # ---- Text tab ----
    def show_text(self, text: str):
        self.set_text(text)

    def show_script(self, script_name: str):
        # heuristic: show bytes near the script name
        view = "(script body not parsed; showing nearby bytes)"
        if self.raw:
            b = script_name.encode("utf-8", errors="ignore")
            p = self.raw.find(b)
            if p != -1:
                sample = self.raw[p:p+8192]
                dec = safe_decode_text(sample)
                if dec: view = dec
        self.set_text(view)
        self.set_info(f"Script: {script_name}")

    def show_chunk(self, meta):
        name, off, size, cs, ce = meta["name"], meta["off"], meta["size"], meta["cs"], meta["ce"]
        self.set_text(f"Chunk '{name}' at offset {off}\nSize: {size}\nContent: {cs}..{ce}\n\nHex preview:\n" +
                      " ".join(f"{b:02X}" for b in self.raw[cs:cs+min(size,512)]))
        self.set_info(f"Chunk details\nName: {name}\nOffset: {off}\nSize: {size}\nContent: {cs}..{ce}")

    # ---- Sprite tab (we preview on Text tab with a note; frames render in Room if placed) ----
    def _frame_pixmap(self, idx: int) -> QtGui.QPixmap | None:
        fr = self.sprite_frames[idx]
        if fr.get("pix") is None:
            blob = self.raw[fr["pos"]:fr["end"]]
            try:
                img = Image.open(io.BytesIO(blob)).convert("RGBA")
                b = img.tobytes("raw","BGRA")
                qimg = QtGui.QImage(b, img.width, img.height, QtGui.QImage.Format.Format_ARGB32)
                fr["pix"] = QtGui.QPixmap.fromImage(qimg)
            except Exception:
                fr["pix"] = None
        return fr["pix"]

    def show_sprite_group(self, name: str, indices: list[int]):
        # Compose a horizontal strip preview in Text tab
        sizes = []
        frames = []
        for i in indices:
            pm = self._frame_pixmap(i)
            if pm:
                frames.append(pm)
                sizes.append((pm.width(), pm.height()))
        if not frames:
            self.set_text(f"{name}: (no decodable frames)"); self.set_info(f"Sprite group: {name}"); return
        h = max(h for _,h in sizes)
        w = sum(w for w,_ in sizes)
        canv = QtGui.QPixmap(w, h)
        canv.fill(QtCore.Qt.transparent)
        p = QtGui.QPainter(canv)
        x = 0
        for pm in frames:
            p.drawPixmap(x, 0, pm)
            x += pm.width()
        p.end()
        # show as image -> convert to base64 html to embed
        ba = QtCore.QByteArray()
        buff = QtCore.QBuffer(ba)
        buff.open(QtCore.QIODevice.WriteOnly)
        canv.save(buff, "PNG")
        b64 = bytes(ba.toBase64()).decode()
        html = f'<img src="data:image/png;base64,{b64}"/>'
        self.tabs.setCurrentIndex(0)
        self.text_edit.setPlainText("")  # clear
        self.text_edit.insertPlainText(f"{name}: {len(indices)} frames\n")
        # also show in Info
        self.set_info(f"Sprite group: {name}\nFrames: {len(indices)}")
        # lightweight: show below as image preview by opening mini window
        prev = QtWidgets.QDialog(self); prev.setWindowTitle(f"Sprite: {name}")
        prev.resize(min(w+24, 1000), min(h+80, 600))
        v = QtWidgets.QVBoxLayout(prev)
        lab = QtWidgets.QLabel(); lab.setTextFormat(QtCore.Qt.RichText); lab.setAlignment(QtCore.Qt.AlignCenter)
        lab.setText(html)
        v.addWidget(lab)
        btn = QtWidgets.QDialogButtonBox(QtWidgets.QDialogButtonBox.Close); btn.rejected.connect(prev.reject)
        v.addWidget(btn)
        prev.show()

    def show_sprite_frame(self, idx: int):
        pm = self._frame_pixmap(idx)
        if not pm:
            self.set_text("(could not decode frame)"); return
        ba = QtCore.QByteArray()
        buff = QtCore.QBuffer(ba); buff.open(QtCore.QIODevice.WriteOnly)
        pm.save(buff, "PNG")
        b64 = bytes(ba.toBase64()).decode()
        html = f'<img src="data:image/png;base64,{b64}"/>'
        self.tabs.setCurrentIndex(0)
        self.text_edit.setPlainText("")
        # display with QLabel/HTML in a small dialog
        dlg = QtWidgets.QDialog(self); dlg.setWindowTitle("Sprite Frame")
        dlg.resize(pm.width()+40, pm.height()+80)
        v = QtWidgets.QVBoxLayout(dlg)
        lab = QtWidgets.QLabel(); lab.setAlignment(QtCore.Qt.AlignCenter); lab.setTextFormat(QtCore.Qt.RichText)
        lab.setText(html); v.addWidget(lab)
        btn = QtWidgets.QDialogButtonBox(QtWidgets.QDialogButtonBox.Close); btn.rejected.connect(dlg.reject)
        v.addWidget(btn)
        dlg.show()
        self.set_info("Sprite frame")

    # ---- Room tab ----
    def show_room(self, room_name: str):
        # Try to find ROOM chunks and extract plausible (x,y) instance coords,
        # then draw sprites if a name match is plausible; else dots.
        self.tabs.setCurrentIndex(1)
        scene = self.room_view.scene()
        scene.clear()

        # Gather ROOM regions
        regions = [(c1,c2) for (nm, off, size, c1, c2) in self.chunks if nm == "ROOM"]
        pts = []
        for (c1,c2) in regions:
            blob = self.raw[c1:c2]
            # scan int32 pairs
            for i in range(0, len(blob)-8, 4):
                x = struct.unpack_from("<i", blob, i)[0]
                y = struct.unpack_from("<i", blob, i+4)[0]
                if 0 <= x < 8000 and 0 <= y < 8000:
                    pts.append((x,y))
        if len(pts) > 6000:
            step = max(1, len(pts)//6000)
            pts = pts[::step]

        # basic room bounds
        maxx = max([p[0] for p in pts], default=1024)
        maxy = max([p[1] for p in pts], default=768)
        scene.setSceneRect(0, 0, max(1024, maxx+64), max(768, maxy+64))

        # map some objects to sprite groups by name hints
        obj_to_group = {}
        for oname in self.objects:
            low = oname.lower()
            spr_guess = low.replace("obj_", "spr_")
            if spr_guess in self.sprite_groups:
                obj_to_group[oname] = spr_guess

        # draw pts as sprites or dots
        dot_pen = QtGui.QPen(QtGui.QColor("#7fbfff"))
        dot_br = QtGui.QBrush(QtGui.QColor("#7fbfff"))
        for (x,y) in pts:
            drawn = False
            # rough association: if an object name nearby is known, try its first frame
            # (this is heuristic; real mapping needs full SPRT/TPAG parse)
            for oname, gname in obj_to_group.items():
                idxs = self.sprite_groups.get(gname, [])
                if not idxs:
                    continue
                pm = self._frame_pixmap(idxs[0])
                if pm:
                    pix = scene.addPixmap(pm)
                    pix.setPos(x, y)
                    drawn = True
                    break
            if not drawn:
                scene.addEllipse(x-2, y-2, 4, 4, dot_pen, dot_br)

        self.set_info(f"Room: {room_name}\nInstances plotted: {len(pts)}\n"
                      f"Scene bounds: {scene.sceneRect().width()} x {scene.sceneRect().height()}")

    # ---- Font -> show sample text in Text tab ----
    def show_font(self, font_name: str):
        self.set_text(f"{font_name}\nThe quick brown fox jumps over the lazy dog.\n0123456789 !@#$%^&*()")
        self.set_info(f"Font tag: {font_name}")

    # ---- Sound selection -> info tab + controls ----
    def show_sound(self, idx: int):
        self.current_sound_index = idx
        snd = self.sounds[idx]
        name, typ = snd.get("name"), snd.get("type")
        bytesz = snd["end"] - snd["pos"]
        self.set_info(f"Sound: {name}\nType: {typ}\nBytes: {bytesz}\n\nUse Play / Stop / Waveform below.")
        self.play_btn.setEnabled(SIMPLEAUDIO_OK or PYGAME_OK)
        self.stop_btn.setEnabled(SIMPLEAUDIO_OK or PYGAME_OK)
        self.wave_btn.setEnabled(MATPLOTLIB_OK and NUMPY_OK)
        self.audio_lbl.setText("Ready")

    # --------- Audio controls ---------
    def _save_temp_sound(self, blob: bytes, typ: str):
        ext = ".wav" if typ == "wav" else ".ogg"
        tf = tempfile.NamedTemporaryFile(delete=False, suffix=ext)
        tf.write(blob); tf.flush(); tf.close()
        return tf.name

    def play_audio(self):
        idx = self.current_sound_index
        if idx is None:
            return
        snd = self.sounds[idx]
        blob = self.raw[snd["pos"]:snd["end"]]
        typ = snd.get("type","wav")
        try:
            path = self._save_temp_sound(blob, typ)
            self.current_sound_temp = path
            if SIMPLEAUDIO_OK and typ == "wav":
                w = sa.WaveObject.from_wave_file(path)
                self._play_obj = w.play()
                self.audio_lbl.setText(f"Playing (simpleaudio): {os.path.basename(path)}")
                return
            if PYGAME_OK:
                pygame.mixer.stop()
                pygame.mixer.Sound(path).play()
                self.audio_lbl.setText(f"Playing (pygame): {os.path.basename(path)}")
                return
            # fallback external
            if sys.platform.startswith("win"):
                os.startfile(path)
            elif sys.platform.startswith("darwin"):
                os.system(f'open "{path}"')
            else:
                os.system(f'xdg-open "{path}" &')
            self.audio_lbl.setText(f"Opened external player: {os.path.basename(path)}")
        except Exception as e:
            QtWidgets.QMessageBox.critical(self, "Audio", f"Could not play: {e}")

    def stop_audio(self):
        try:
            if hasattr(self, "_play_obj") and self._play_obj:
                self._play_obj.stop()
                self._play_obj = None
        except Exception:
            pass
        try:
            if PYGAME_OK:
                pygame.mixer.stop()
        except Exception:
            pass
        self.audio_lbl.setText("Stopped")
        if self.current_sound_temp:
            try: os.unlink(self.current_sound_temp)
            except Exception: pass
            self.current_sound_temp = None

    def show_waveform(self):
        idx = self.current_sound_index
        if idx is None or not (MATPLOTLIB_OK and NUMPY_OK):
            QtWidgets.QMessageBox.information(self, "Waveform", "Requires matplotlib + numpy.")
            return
        snd = self.sounds[idx]
        blob = self.raw[snd["pos"]:snd["end"]]
        typ = snd.get("type","wav")

        samples, sr = None, None
        if PYDUB_OK:
            try:
                audio = AudioSegment.from_file(io.BytesIO(blob), format=typ)
                sr = audio.frame_rate
                arr = audio.get_array_of_samples()
                ch = audio.channels
                a = _np.array(arr)
                samples = a.reshape((-1, ch)).mean(axis=1) if ch > 1 else a
            except Exception:
                samples = None
        if samples is None:
            try:
                import wave
                bf = io.BytesIO(blob)
                wf = wave.open(bf, 'rb')
                sr = wf.getframerate()
                frames = wf.readframes(wf.getnframes())
                width = wf.getsampwidth()
                dtype = {1:'int8',2:'int16',4:'int32'}.get(width,'int16')
                a = _np.frombuffer(frames, dtype=_np.dtype(dtype))
                if wf.getnchannels() > 1:
                    a = a.reshape((-1, wf.getnchannels())).mean(axis=1)
                samples = a
                wf.close()
            except Exception:
                samples = None

        if samples is None:
            QtWidgets.QMessageBox.information(self, "Waveform", "Could not decode audio.")
            return

        # Draw into a QPixmap to show in a dialog
        fig, ax = plt.subplots(figsize=(8,3))
        t = (1.0 * _np.arange(len(samples))) / float(sr if sr else 44100)
        ax.plot(t, samples)
        ax.set_xlabel("Seconds"); ax.set_ylabel("Amplitude")
        fig.tight_layout()
        png = io.BytesIO(); fig.savefig(png, format="png"); plt.close(fig)

        img = QtGui.QImage.fromData(png.getvalue(), "PNG")
        pm = QtGui.QPixmap.fromImage(img)
        d = QtWidgets.QDialog(self); d.setWindowTitle("Waveform")
        d.resize(pm.width()+40, pm.height()+80)
        v = QtWidgets.QVBoxLayout(d)
        lab = QtWidgets.QLabel(); lab.setPixmap(pm); lab.setAlignment(QtCore.Qt.AlignCenter)
        v.addWidget(lab)
        btn = QtWidgets.QDialogButtonBox(QtWidgets.QDialogButtonBox.Close); btn.rejected.connect(d.reject)
        v.addWidget(btn)
        d.show()

    # --------- Export all ---------
    def export_all(self):
        if not self.raw:
            QtWidgets.QMessageBox.information(self, "Export", "No file loaded.")
            return
        dest = QtWidgets.QFileDialog.getExistingDirectory(self, "Export assets to folder")
        if not dest: return
        img_dir = os.path.join(dest, "sprites"); snd_dir = os.path.join(dest, "sounds"); scr_dir = os.path.join(dest, "scripts")
        os.makedirs(img_dir, exist_ok=True); os.makedirs(snd_dir, exist_ok=True); os.makedirs(scr_dir, exist_ok=True)

        for i, fr in enumerate(self.sprite_frames):
            nm = fr.get("name", f"spr_{i}")
            safe = "".join(c if c.isalnum() or c in "._-" else "_" for c in nm)
            p = os.path.join(img_dir, f"{safe}_{i}.png")
            with open(p, "wb") as f: f.write(self.raw[fr["pos"]:fr["end"]])

        for i, snd in enumerate(self.sounds):
            nm = snd.get("name", f"sound_{i}")
            safe = "".join(c if c.isalnum() or c in "._-" else "_" for c in nm)
            ext = ".wav" if snd.get("type") == "wav" else ".ogg"
            p = os.path.join(snd_dir, f"{safe}_{i}{ext}")
            with open(p, "wb") as f: f.write(self.raw[snd["pos"]:snd["end"]])

        for i, scr in enumerate(self.scripts):
            safe = "".join(c if c.isalnum() or c in "._-" else "_" for c in scr)
            p = os.path.join(scr_dir, f"{safe}_{i}.txt")
            with open(p, "w", encoding="utf-8") as f: f.write(scr)

        QtWidgets.QMessageBox.information(self, "Export", f"Exported to: {dest}")


# ---------- Entrypoint ----------
def main():
    app = QtWidgets.QApplication(sys.argv)
    w = MainWindow()
    w.show()
    sys.exit(app.exec())

if __name__ == "__main__":
    main()
