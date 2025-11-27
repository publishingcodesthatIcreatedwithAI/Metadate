import argparse
import io
import json
import logging
import mimetypes
import os
import random
import shutil
import struct
import tempfile
import time
import zipfile
import tkinter as tk
from datetime import datetime
from pathlib import Path
from tkinter import filedialog, messagebox, ttk
from typing import Any, Dict, Optional

# Pillow
try:
    from PIL import Image, ImageFile, PngImagePlugin, TiffImagePlugin
    from PIL.ExifTags import TAGS
except Exception:
    Image = None
    ImageFile = None
    PngImagePlugin = None
    TiffImagePlugin = None
    TAGS = {}

# Allow truncated images to load sometimes
if ImageFile is not None:
    ImageFile.LOAD_TRUNCATED_IMAGES = True

# Optional libraries with graceful fallback
try:
    import magic  # python-magic / python-magic-bin
except Exception:
    magic = None

try:
    import piexif
except Exception:
    piexif = None

try:
    import pikepdf
except Exception:
    pikepdf = None

try:
    import fitz  # PyMuPDF
except Exception:
    fitz = None

# ----------------------------
# Logging
# ----------------------------
def setup_logging(level=logging.INFO):
    logging.basicConfig(level=level, format="%(asctime)s %(levelname)s: %(message)s")

# ----------------------------
# Shared utilities (extractor)
# ----------------------------
def read_raw_header(path: Path, count: int = 256) -> str:
    try:
        with path.open("rb") as f:
            data = f.read(count)
            return " ".join(f"{b:02X}" for b in data)
    except Exception as e:
        logging.debug("Failed to read header: %s", e)
        return ""

def safe_unpack(fmt: str, buffer: bytes, offset: int) -> Optional[tuple]:
    size = struct.calcsize(fmt)
    if offset + size > len(buffer):
        return None
    try:
        return struct.unpack_from(fmt, buffer, offset)
    except Exception:
        return None

def extract_exif(path: Path) -> Dict[str, Any]:
    if Image is None:
        return {"error": "Pillow not installed"}
    exif_data: Dict[str, Any] = {}
    try:
        with Image.open(path) as img:
            exif = getattr(img, "_getexif", lambda: None)() or {}
            for tag_id, value in exif.items():
                tag = TAGS.get(tag_id, tag_id)
                if isinstance(value, bytes):
                    try:
                        value = value.decode("utf-8", errors="replace")
                    except Exception:
                        value = repr(value)
                exif_data[str(tag)] = value
    except Exception as e:
        logging.debug("Error extracting EXIF: %s", e)
        return {"error": str(e)}
    return exif_data

def parse_icc_profile(icc_bytes: bytes) -> Dict[str, Any]:
    md: Dict[str, Any] = {}
    if not icc_bytes or len(icc_bytes) < 128:
        return {"icc_error": "profile too short or missing"}
    try:
        profile_size = safe_unpack(">I", icc_bytes, 0)
        if profile_size is None:
            return {"icc_error": "invalid header"}
        md["profile_size"] = profile_size[0]
        md["cmm_type"] = icc_bytes[4:8].decode("ascii", errors="ignore").strip() or None
        major = icc_bytes[8]
        minor = (icc_bytes[9] >> 4)
        bugfix = (icc_bytes[9] & 0x0F)
        md["version"] = f"{major}.{minor}.{bugfix}"
        md["profile_class"] = icc_bytes[12:16].decode("ascii", errors="ignore").strip()
        md["color_space"] = icc_bytes[16:20].decode("ascii", errors="ignore").strip()
        md["pcs"] = icc_bytes[20:24].decode("ascii", errors="ignore").strip()
        dt = safe_unpack(">6H", icc_bytes, 24)
        if dt:
            md["date_time"] = f"{dt[0]:04d}:{dt[1]:02d}:{dt[2]:02d} {dt[3]:02d}:{dt[4]:02d}:{dt[5]:02d}"
        md["signature"] = icc_bytes[36:40].decode("ascii", errors="ignore").strip()
        md["platform"] = icc_bytes[40:44].decode("ascii", errors="ignore").strip()
        flags = safe_unpack(">I", icc_bytes, 44)
        if flags:
            md["flags"] = flags[0]
        md["creator"] = icc_bytes[80:84].decode("ascii", errors="ignore").strip()
        pid = icc_bytes[84:100]
        md["profile_id"] = pid.hex() if pid != b"\x00" * 16 else None
        tag_count = safe_unpack(">I", icc_bytes, 128)
        if not tag_count:
            md["tag_count"] = 0
            md["tags"] = {}
            return md
        tag_count = tag_count[0]
        md["tag_count"] = tag_count
        tags = {}
        for i in range(tag_count):
            base = 132 + i * 12
            entry = safe_unpack(">4sII", icc_bytes, base)
            if not entry:
                continue
            sig_bytes, toff, tsize = entry
            sig = sig_bytes.decode("ascii", errors="ignore").strip()
            if toff + tsize > len(icc_bytes) or toff < 0:
                tags[sig] = {"error": "out of bounds"}
                continue
            tdata = icc_bytes[toff:toff + tsize]
            tags[sig] = {"size": tsize}
        md["tags"] = tags
    except Exception as e:
        return {"icc_error": str(e)}
    return md

def parse_jpeg_markers(path: Path) -> Dict[str, Any]:
    out: Dict[str, Any] = {}
    try:
        with path.open("rb") as f:
            data = f.read()
        if not data.startswith(b"\xFF\xD8"):
            return {"error": "not_jpeg"}
        i = 2
        quant_tables = 0
        sof_components = []
        while i < len(data):
            if data[i] != 0xFF:
                i += 1
                continue
            while i < len(data) and data[i] == 0xFF:
                i += 1
            if i >= len(data):
                break
            marker = data[i]
            i += 1
            if marker == 0xD9:
                break
            if marker in range(0xD0, 0xD8):
                continue
            if i + 2 > len(data):
                break
            length = struct.unpack_from(">H", data, i)[0]
            if length < 2:
                break
            payload_start = i + 2
            payload_end = payload_start + (length - 2)
            if payload_end > len(data):
                break
            segment = data[payload_start:payload_end]
            if marker == 0xDB:  # DQT
                quant_tables += 1
            elif marker in (0xC0, 0xC1, 0xC2, 0xC3):
                try:
                    if len(segment) >= 6:
                        precision = segment[0]
                        height = struct.unpack_from(">H", segment, 1)[0]
                        width = struct.unpack_from(">H", segment, 3)[0]
                        num_comp = segment[5]
                        comps = []
                        off = 6
                        for c in range(num_comp):
                            cid = segment[off]
                            samp = segment[off + 1]
                            qt = segment[off + 2]
                            h = samp >> 4
                            v = samp & 0x0F
                            comps.append({"id": cid, "h": h, "v": v, "qt": qt})
                            off += 3
                        sof_components = comps
                except Exception:
                    pass
            i = payload_end
        out["quant_tables"] = quant_tables
        if sof_components:
            out["sof"] = {"components": sof_components}
    except Exception as e:
        out["error"] = str(e)
    return out

def get_basic_filesystem_metadata(path: Path) -> Dict[str, Any]:
    try:
        st = path.stat()
        return {
            "file_name": path.name,
            "file_path": str(path.resolve()),
            "size_bytes": st.st_size,
            "modified": datetime.fromtimestamp(st.st_mtime).isoformat(),
            "created": datetime.fromtimestamp(st.st_ctime).isoformat(),
        }
    except Exception as e:
        return {"error": str(e)}

def extract_metadata(path: Path) -> Dict[str, Any]:
    if not path.exists():
        return {"error": "not_found"}
    meta: Dict[str, Any] = {}
    meta.update(get_basic_filesystem_metadata(path))
    meta["raw_header"] = read_raw_header(path, 512)
    mime = mimetypes.guess_type(str(path))[0] or "unknown"
    meta["mime_type"] = mime
    if mime.startswith("image/") and Image is not None:
        try:
            with Image.open(path) as img:
                meta["image_format"] = img.format
                meta["width"] = img.width
                meta["height"] = img.height
                meta["mode"] = img.mode
                info = getattr(img, "info", {}) or {}
                if "icc_profile" in info:
                    icc = info["icc_profile"]
                    if isinstance(icc, str):
                        icc = icc.encode("latin1")
                    meta["icc"] = parse_icc_profile(icc)
                exif = extract_exif(path)
                if exif:
                    meta["exif"] = exif
        except Exception as e:
            logging.debug("Pillow image processing failed: %s", e)
            meta.setdefault("warnings", []).append("image_processing_failed")
    if path.suffix.lower() in (".jpg", ".jpeg"):
        meta["jpeg_markers"] = parse_jpeg_markers(path)
    return meta

def save_metadata_to_file(metadata: Dict[str, Any], target_path: Path, output_format: str = "text"):
    suffix = ".metadata.json" if output_format == "json" else ".metadata.txt"
    out_path = target_path.with_suffix(target_path.suffix + suffix)
    try:
        if output_format == "json":
            with out_path.open("w", encoding="utf-8") as f:
                json.dump(metadata, f, indent=2, ensure_ascii=False)
        else:
            with out_path.open("w", encoding="utf-8") as f:
                f.write(f"Metadata for {target_path.name}\n")
                f.write("=" * 80 + "\n")
                for k, v in metadata.items():
                    f.write(f"{k}:\n{json.dumps(v, indent=2, ensure_ascii=False) if not isinstance(v, str) else v}\n\n")
        return out_path
    except Exception as e:
        logging.exception("Failed to save metadata: %s", e)
        return None

# ----------------------------
# Cleaner functions
# ----------------------------
def detect_file_type(filepath):
    # Try python-magic first
    try:
        if magic:
            m = magic.Magic(mime=True)
            mime_type = m.from_file(filepath)
            if mime_type:
                return mime_type
    except Exception:
        pass
    # Fallback: inspect header bytes
    try:
        with open(filepath, 'rb') as f:
            header = f.read(4096)
    except Exception:
        return 'application/octet-stream'
    header_lower = header[:16]
    if header.startswith(b'%PDF'):
        return 'application/pdf'
    if header.startswith(b'\x89PNG\r\n\x1a\n'):
        return 'image/png'
    if header.startswith(b'\xff\xd8'):
        return 'image/jpeg'
    if header.startswith(b'GIF87a') or header.startswith(b'GIF89a'):
        return 'image/gif'
    if header.startswith(b'II*\x00') or header.startswith(b'MM\x00*'):
        return 'image/tiff'
    if header.startswith(b'PK\x03\x04'):
        try:
            with zipfile.ZipFile(filepath, 'r') as zf:
                namelist = zf.namelist()
                if 'word/document.xml' in namelist:
                    return 'application/vnd.openxmlformats-officedocument.wordprocessingml.document'
                if 'ppt/presentation.xml' in namelist:
                    return 'application/vnd.openxmlformats-officedocument.presentationml.presentation'
                if 'xl/workbook.xml' in namelist:
                    return 'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet'
                return 'application/zip'
        except Exception:
            return 'application/zip'
    if header_lower[:8] == b'\xd0\xcf\x11\xe0\xa1\xb1\x1a\xe1':
        return 'application/vnd.ms-office'
    mime_guess, _ = mimetypes.guess_type(filepath)
    return mime_guess or 'application/octet-stream'

def wipe_filesystem_timestamps(filepath, randomize=False):
    if randomize:
        neutral_time = time.time() - (86400 * random.randint(1, 3650))
    else:
        neutral_time = time.mktime((2000, 1, 1, 0, 0, 0, 0, 0, 0))
    try:
        os.utime(filepath, (neutral_time, neutral_time))
    except Exception as e:
        logging.debug("[timestamp] Failed setting mtime/atime: %s", e)
    if os.name == "nt":
        try:
            import pywintypes, win32file, win32con
            handle = win32file.CreateFile(
                filepath,
                win32con.GENERIC_WRITE,
                win32con.FILE_SHARE_READ | win32con.FILE_SHARE_WRITE | win32con.FILE_SHARE_DELETE,
                None,
                win32con.OPEN_EXISTING,
                win32con.FILE_ATTRIBUTE_NORMAL,
                None
            )
            win_time = pywintypes.Time(neutral_time)
            win32file.SetFileTime(handle, win_time, win_time, win_time)
            handle.close()
        except Exception as e:
            logging.debug("[timestamp] Failed to set creation time: %s", e)
    return True

def wipe_directory_timestamps(path, randomize=False):
    try:
        if randomize:
            neutral_time = time.time() - (86400 * random.randint(1, 3650))
        else:
            neutral_time = time.mktime((2000, 1, 1, 0, 0, 0, 0, 0, 0))
        os.utime(path, (neutral_time, neutral_time))
    except Exception as e:
        logging.debug("[timestamp] Failed to wipe directory timestamps: %s", e)

# Image cleaners
def clean_jpeg_metadata(input_path, output_path):
    try:
        img = Image.open(input_path)
        if piexif:
            exif_bytes = piexif.dump({})
            img.save(output_path, format="JPEG", quality=95, exif=exif_bytes)
        else:
            data = list(img.getdata())
            new_img = Image.new(img.mode, img.size)
            new_img.putdata(data)
            new_img.save(output_path, format="JPEG", quality=95)
        return True
    except Exception as e:
        logging.debug("[jpeg] error: %s", e)
        return False

def clean_png_metadata(input_path, output_path):
    try:
        img = Image.open(input_path)
        data = list(img.getdata())
        new_img = Image.new(img.mode, img.size)
        new_img.putdata(data)
        pnginfo = PngImagePlugin.PngInfo()
        new_img.save(output_path, format="PNG", optimize=True, pnginfo=pnginfo)
        return True
    except Exception as e:
        logging.debug("[png] error: %s", e)
        return False

def clean_image_metadata(input_path, output_path, strip_all=True):
    try:
        img = Image.open(input_path)
    except Exception as e:
        logging.debug("[image] cannot open image: %s", e)
        return False
    fmt = img.format or os.path.splitext(input_path)[1].lstrip('.').upper()
    if fmt.upper() in ('JPEG', 'JPG'):
        return clean_jpeg_metadata(input_path, output_path)
    elif fmt.upper() == 'PNG':
        return clean_png_metadata(input_path, output_path)
    elif fmt.upper() in ('TIFF', 'TIF'):
        try:
            data = list(img.getdata())
            new_img = Image.new(img.mode, img.size)
            new_img.putdata(data)
            new_img.save(output_path, format='TIFF', tiffinfo={})
            return True
        except Exception as e:
            logging.debug("[image][tiff] error cleaning: %s", e)
            return False
    else:
        try:
            data = list(img.getdata())
            new_img = Image.new(img.mode, img.size)
            new_img.putdata(data)
            fmt_out = img.format if img.format else 'PNG'
            new_img.save(output_path, format=fmt_out)
            return True
        except Exception as e:
            logging.debug("[image][generic] error cleaning: %s", e)
            return False

# PDF cleaners
def clean_pdf_with_pikepdf(input_path, output_path):
    if not pikepdf:
        logging.debug("[pdf] pikepdf not installed.")
        return False
    try:
        with pikepdf.open(input_path, allow_overwriting_input=True) as pdf:
            try:
                pdf.docinfo.clear()
            except Exception:
                pass
            root = pdf.root
            if '/Metadata' in root:
                try:
                    del root['/Metadata']
                except Exception:
                    root.pop('/Metadata', None)
            if '/ID' in pdf.trailer:
                try:
                    del pdf.trailer['/ID']
                except Exception:
                    pdf.trailer.pop('/ID', None)
            try:
                names = pdf.root.get('/Names')
                if names and '/EmbeddedFiles' in names:
                    names.pop('/EmbeddedFiles', None)
            except Exception:
                pass
            try:
                if '/Names' in pdf.root:
                    pdf.root['/Names'].pop('/EmbeddedFiles', None)
            except Exception:
                pass
            try:
                for page in pdf.pages:
                    if '/Annots' in page.obj:
                        page.obj.pop('/Annots', None)
            except Exception:
                pass
            pdf.save(output_path, linearize=False)
        return True
    except Exception as e:
        logging.debug("[pdf][pikepdf] failed: %s", e)
        return False

def rasterize_pdf_with_pymupdf(input_path, output_path, dpi=300):
    if not fitz:
        logging.debug("[pdf] PyMuPDF not installed.")
        return False
    try:
        doc = fitz.open(input_path)
        new_pdf = fitz.open()
        zoom = dpi / 72.0
        mat = fitz.Matrix(zoom, zoom)
        for i in range(len(doc)):
            page = doc.load_page(i)
            pix = page.get_pixmap(matrix=mat, alpha=False)
            rect = fitz.Rect(0, 0, pix.width, pix.height)
            page_out = new_pdf.new_page(width=pix.width, height=pix.height)
            page_out.insert_image(rect, pixmap=pix)
        new_pdf.save(output_path)
        new_pdf.close()
        doc.close()
        return True
    except Exception as e:
        logging.debug("[pdf][raster] error: %s", e)
        return False

# OOXML cleaning
def clean_office_ooxml(input_path, output_path):
    try:
        with zipfile.ZipFile(input_path, 'r') as zin:
            with zipfile.ZipFile(output_path, 'w', compression=zipfile.ZIP_DEFLATED) as zout:
                for item in zin.infolist():
                    name = item.filename
                    if name.startswith('docProps/') or name.startswith('customXml/'):
                        continue
                    data = zin.read(name)
                    # ensure zip entry timestamp neutralization
                    zi = zipfile.ZipInfo(name)
                    zi.date_time = (2000, 1, 1, 0, 0, 0)
                    zout.writestr(zi, data)
        return True
    except Exception as e:
        logging.debug("[office] error cleaning OOXML file: %s", e)
        return False

def clean_metadata(filepath, destructive_pdf_rasterize=False, dpi=300, randomize_timestamps=False):
    if not os.path.exists(filepath):
        return False, "File not found"
    file_type = detect_file_type(filepath)
    logging.info("[detect] %s", file_type)
    base, ext = os.path.splitext(filepath)
    output_path = f"{base}_cleaned{ext}"
    success = False
    msg = ""
    try:
        if file_type.startswith('image/'):
            success = clean_image_metadata(filepath, output_path)
            msg = "Image metadata cleaned." if success else "Failed to clean image metadata."
        elif file_type == 'application/pdf':
            if not destructive_pdf_rasterize:
                ok = clean_pdf_with_pikepdf(filepath, output_path)
                if ok:
                    success = True
                    msg = "PDF metadata cleaned with pikepdf (non-destructive)."
                else:
                    logging.info("[pdf] pikepdf failed or incomplete; falling back to rasterize (destructive).")
                    ok2 = rasterize_pdf_with_pymupdf(filepath, output_path, dpi=dpi)
                    if ok2:
                        success = True
                        msg = "PDF cleaned by rasterizing pages (destructive — text/search lost)."
                    else:
                        success = False
                        msg = "Failed to clean PDF with both pikepdf and rasterization."
            else:
                ok2 = rasterize_pdf_with_pymupdf(filepath, output_path, dpi=dpi)
                if ok2:
                    success = True
                    msg = "PDF cleaned by rasterizing pages (destructive — text/search lost)."
                else:
                    success = False
                    msg = "Rasterization failed; cannot guarantee PDF sanitization."
        elif file_type in (
            'application/vnd.openxmlformats-officedocument.wordprocessingml.document',
            'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet',
            'application/vnd.openxmlformats-officedocument.presentationml.presentation',
            'application/zip'
        ):
            success = clean_office_ooxml(filepath, output_path)
            if success:
                msg = "Office OOXML metadata cleaned (docProps/customXml removed)."
            else:
                msg = "Failed to clean OOXML file."
        elif file_type == 'application/vnd.ms-office':
            try:
                shutil.copy2(filepath, output_path)
                success = True
                msg = "Old MS Office file copied. Binary CFBF cleaning not implemented (consider using external tools)."
            except Exception as e:
                success = False
                msg = f"Failed to copy file: {e}"
        else:
            try:
                shutil.copy2(filepath, output_path)
                success = True
                msg = f"File type '{file_type}' not explicitly supported. File copied without modification."
            except Exception as e:
                success = False
                msg = f"Error copying file: {e}"
    except Exception as e:
        success = False
        msg = f"Unexpected error: {e}"
    if success:
        try:
            wipe_filesystem_timestamps(output_path, randomize=randomize_timestamps)
            wipe_directory_timestamps(os.path.dirname(output_path), randomize=randomize_timestamps)
        except Exception as e:
            logging.debug("[timestamp] error: %s", e)
        info = (
            f"{msg}\n\nOriginal: {os.path.basename(filepath)}\n"
            f"Cleaned: {os.path.basename(output_path)}\nLocation: {os.path.dirname(output_path)}"
        )
        return True, info
    else:
        return False, msg

# ----------------------------
# GUI (two tabs: Inspect | Clean)
# ----------------------------
class MetadataToolGUI:
    def __init__(self, root):
        self.root = root
        root.title("Metadata Inspector & Cleaner")
        root.geometry("920x640")
        self.notebook = ttk.Notebook(root)
        self.notebook.pack(fill=tk.BOTH, expand=True)

        self._build_inspect_tab()
        self._build_clean_tab()

    # ---------- Inspect tab ----------
    def _build_inspect_tab(self):
        frm = ttk.Frame(self.notebook, padding=8)
        self.notebook.add(frm, text="Inspect")

        top = ttk.Frame(frm)
        top.pack(fill=tk.X, pady=6)

        ttk.Label(top, text="File:").pack(side=tk.LEFT)
        self.inspect_path_var = tk.StringVar()
        entry = ttk.Entry(top, textvariable=self.inspect_path_var, width=90)
        entry.pack(side=tk.LEFT, padx=6)
        ttk.Button(top, text="Browse...", command=self._inspect_browse).pack(side=tk.LEFT)
        ttk.Button(top, text="Inspect", command=self._do_inspect).pack(side=tk.LEFT, padx=6)
        ttk.Button(top, text="Save metadata", command=self._save_inspect_output).pack(side=tk.LEFT)

        # Result area
        self.inspect_text = tk.Text(frm, wrap="none")
        self.inspect_text.pack(fill=tk.BOTH, expand=True, padx=6, pady=6)

        # add scrollbars
        ysb = ttk.Scrollbar(frm, orient="vertical", command=self.inspect_text.yview)
        ysb.place(relx=1.0, rely=0.08, relheight=0.84, anchor='ne')
        self.inspect_text.configure(yscrollcommand=ysb.set)

    def _inspect_browse(self):
        path = filedialog.askopenfilename(title="Select file to inspect", filetypes=[("All files", "*.*")])
        if path:
            self.inspect_path_var.set(path)

    def _do_inspect(self):
        path_str = self.inspect_path_var.get().strip()
        if not path_str:
            messagebox.showerror("Error", "No file selected.")
            return
        p = Path(path_str)
        md = extract_metadata(p)
        pretty = json.dumps(md, indent=2, ensure_ascii=False)
        self.inspect_text.delete("1.0", tk.END)
        self.inspect_text.insert(tk.END, pretty)

    def _save_inspect_output(self):
        path_str = self.inspect_path_var.get().strip()
        if not path_str:
            messagebox.showerror("Error", "No file selected.")
            return
        p = Path(path_str)
        md_text = self.inspect_text.get("1.0", tk.END).strip()
        if not md_text:
            messagebox.showinfo("Info", "Nothing to save. Run Inspect first.")
            return
        # Ask format
        fmt = messagebox.askquestion("Save format", "Save as JSON? (No -> plain text)", icon='question')
        out_fmt = "json" if fmt == "yes" else "text"
        out_path = save_metadata_to_file(json.loads(md_text) if out_fmt == "json" else json.loads(md_text), p, output_format=out_fmt)
        if out_path:
            messagebox.showinfo("Saved", f"Metadata saved to:\n{out_path}")
        else:
            messagebox.showerror("Error", "Failed to save metadata.")

    # ---------- Clean tab ----------
    def _build_clean_tab(self):
        frm = ttk.Frame(self.notebook, padding=8)
        self.notebook.add(frm, text="Clean")

        top = ttk.Frame(frm)
        top.pack(fill=tk.X, pady=6)

        ttk.Label(top, text="File:").pack(side=tk.LEFT)
        self.clean_path_var = tk.StringVar()
        entry = ttk.Entry(top, textvariable=self.clean_path_var, width=74)
        entry.pack(side=tk.LEFT, padx=6)
        ttk.Button(top, text="Browse...", command=self._clean_browse).pack(side=tk.LEFT)
        ttk.Button(top, text="Clean", command=self._do_clean).pack(side=tk.LEFT, padx=6)

        opts = ttk.Frame(frm)
        opts.pack(fill=tk.X, pady=6)
        self.destructive_var = tk.BooleanVar(value=False)
        self.randomize_ts_var = tk.BooleanVar(value=False)
        self.dpi_var = tk.IntVar(value=300)
        ttk.Checkbutton(opts, text="Force destructive PDF rasterization (removes text/search/links)", variable=self.destructive_var).pack(anchor='w')
        ttk.Checkbutton(opts, text="Randomize timestamps (past 1-10 years instead of 2000-01-01)", variable=self.randomize_ts_var).pack(anchor='w')
        dpifrm = ttk.Frame(opts)
        dpifrm.pack(anchor='w', pady=(6,0))
        ttk.Label(dpifrm, text="Raster DPI (if destructive):").pack(side=tk.LEFT)
        ttk.Spinbox(dpifrm, from_=72, to=600, textvariable=self.dpi_var, width=8).pack(side=tk.LEFT, padx=6)

        # Status / log area
        self.clean_text = tk.Text(frm, height=18, wrap="word")
        self.clean_text.pack(fill=tk.BOTH, expand=True, padx=6, pady=6)
        ysb = ttk.Scrollbar(frm, orient="vertical", command=self.clean_text.yview)
        ysb.place(relx=1.0, rely=0.28, relheight=0.62, anchor='ne')
        self.clean_text.configure(yscrollcommand=ysb.set)

    def _clean_browse(self):
        path = filedialog.askopenfilename(title="Select file to clean", filetypes=[("All files", "*.*")])
        if path:
            self.clean_path_var.set(path)

    def _log_clean(self, *parts):
        self.clean_text.insert(tk.END, " ".join(str(p) for p in parts) + "\n")
        self.clean_text.see(tk.END)
        self.clean_text.update_idletasks()

    def _do_clean(self):
        filepath = self.clean_path_var.get().strip()
        if not filepath:
            messagebox.showerror("Error", "No file selected.")
            return
        pre_checks = []
        if not piexif:
            pre_checks.append("piexif (for robust JPEG EXIF removal) is not installed.")
        if not pikepdf:
            pre_checks.append("pikepdf (for PDF XMP/metadata removal) is not installed.")
        if not fitz:
            pre_checks.append("PyMuPDF/fitz (for PDF rasterize fallback) is not installed.")
        if pre_checks:
            msg = "Prerequisite warnings:\n" + "\n".join(pre_checks) + "\n\nProceed anyway?"
            if not messagebox.askyesno("Prerequisites missing", msg):
                return
        self.clean_text.delete("1.0", tk.END)
        self._log_clean("Processing:", filepath)
        destructive = self.destructive_var.get()
        randomize_ts = self.randomize_ts_var.get()
        dpi = self.dpi_var.get() if destructive else 300
        ok, info = clean_metadata(filepath, destructive_pdf_rasterize=destructive, dpi=dpi, randomize_timestamps=randomize_ts)
        if ok:
            self._log_clean("SUCCESS:", info)
            messagebox.showinfo("Success", info)
        else:
            self._log_clean("ERROR:", info)
            messagebox.showerror("Error", info)

# ----------------------------
# CLI fallback (optional)
# ----------------------------
def main_cli():
    p = argparse.ArgumentParser(description="Metadata Inspector & Cleaner (GUI recommended)")
    p.add_argument("--nogui", action="store_true", help="Run in CLI mode (inspect single file)")
    p.add_argument("path", nargs="?", help="File to inspect (CLI mode)")
    args = p.parse_args()
    if args.nogui:
        setup_logging()
        if not args.path:
            print("Provide a path in --nogui mode.")
            return
        md = extract_metadata(Path(args.path))
        print(json.dumps(md, indent=2, ensure_ascii=False))
    else:
        root = tk.Tk()
        app = MetadataToolGUI(root)
        root.mainloop()

if __name__ == "__main__":
    main_cli()
