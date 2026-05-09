"""
KeyStroke Monitor — Production Edition
=======================================
Professional desktop monitoring framework.
Architecture: UI layer / logging engine / monitoring services /
              analytics engine / storage layer / reporting system

Hotkeys: F12 = toggle visibility  |  F11 = pause  |  F10 = screenshot
"""

from __future__ import annotations

import base64
import datetime
import hashlib
import json
import math
import os
import queue
import re
import subprocess
import sys
import threading
import time
from collections import defaultdict, deque
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Callable, Dict, List, Optional, Set, Tuple

import tkinter as tk
from tkinter import font as tkfont
from tkinter import messagebox, scrolledtext, ttk

# ── Optional dependencies ──────────────────────────────────────────────────────

try:
    from PIL import Image, ImageGrab, ImageTk
    PIL_AVAILABLE = True
except ImportError:
    ImageGrab = ImageTk = None
    PIL_AVAILABLE = False

try:
    from cryptography.fernet import Fernet
    CRYPTO_AVAILABLE = True
except ImportError:
    CRYPTO_AVAILABLE = False

try:
    import pyperclip
    CLIPBOARD_AVAILABLE = True
except ImportError:
    CLIPBOARD_AVAILABLE = False

try:
    from pynput import keyboard, mouse
    PYNPUT_AVAILABLE = True
except ImportError:
    PYNPUT_AVAILABLE = False

try:
    if sys.platform == "win32":
        import win32gui, win32process, psutil
        WIN32_AVAILABLE = True
    else:
        WIN32_AVAILABLE = False
except ImportError:
    WIN32_AVAILABLE = False

try:
    from win10toast import ToastNotifier as _ToastNotifier
    _TOAST_BACKEND = "win10toast"
except ImportError:
    try:
        from plyer import notification as _plyer_notify
        _TOAST_BACKEND = "plyer"
    except ImportError:
        _TOAST_BACKEND = None


# ══════════════════════════════════════════════════════════════════════════════
# CONFIGURATION
# ══════════════════════════════════════════════════════════════════════════════

@dataclass
class AppConfig:
    """Single source of truth for all runtime configuration."""
    root_dir: str = "KeyStroke-Monitor"
    flush_interval: float = 5.0
    idle_threshold: float = 60.0
    screenshot_cooldown: float = 3.0
    log_buffer_max: int = 5000
    ui_queue_max: int = 300
    ui_poll_ms: int = 80
    stats_interval_ms: int = 1000
    spark_interval_ms: int = 2000
    log_trim_keep: int = 1000
    log_trim_at: int = 2000
    kpm_window: float = 60.0
    clipboard_poll: float = 1.5

    # Derived paths (not serialized directly)
    @property
    def keystrokes_dir(self) -> str:
        return "Keystrokes"

    @property
    def screenshots_dir(self) -> str:
        return "Screenshots"

    @property
    def reports_dir(self) -> str:
        return "Reports"

    @property
    def encrypted_dir(self) -> str:
        return "Encrypted"


CONFIG = AppConfig()


# ══════════════════════════════════════════════════════════════════════════════
# DESIGN SYSTEM
# ══════════════════════════════════════════════════════════════════════════════

class Theme:
    # Backgrounds
    BG       = "#0f1115"
    BG2      = "#151821"
    BG3      = "#1b1f2a"
    BG4      = "#1e2330"

    # Text
    FG       = "#e6e9ef"
    FG2      = "#9aa3b2"
    FG3      = "#5c6370"

    # Accent
    ACCENT   = "#5b8cff"
    ACCENT_DIM = "#3d6ee0"

    # Semantic
    SUCCESS  = "#3fb950"
    WARNING  = "#d29922"
    DANGER   = "#f85149"

    # Log category colors
    LOG_TS   = "#5c6370"
    LOG_KB   = "#9aa3b2"
    LOG_WEB  = "#5b8cff"
    LOG_CLIP = "#d29922"
    LOG_SYS  = "#4a5568"

    # Layout
    BORDER   = "#2a2f3a"
    SIDEBAR_W = 260


class Fonts:
    _ui_family: str = "Segoe UI"
    _mono_family: str = "Consolas"
    _initialized: bool = False

    @classmethod
    def init(cls):
        if cls._initialized:
            return
        available = set(tkfont.families())
        for candidate in ["Segoe UI Variable", "Segoe UI", "SF Pro Display", "Helvetica Neue", "Arial"]:
            if candidate in available:
                cls._ui_family = candidate
                break
        for candidate in ["Cascadia Code", "Cascadia Mono", "Consolas", "Fira Code", "Monaco", "Courier New"]:
            if candidate in available:
                cls._mono_family = candidate
                break
        cls._initialized = True

    @classmethod
    def ui(cls, size: int = 10, weight: str = "normal") -> tuple:
        return (cls._ui_family, size, weight)

    @classmethod
    def mono(cls, size: int = 9) -> tuple:
        return (cls._mono_family, size)

    @classmethod
    def label(cls) -> tuple:
        return cls.ui(8)

    @classmethod
    def small(cls) -> tuple:
        return cls.ui(9)

    @classmethod
    def body(cls) -> tuple:
        return cls.ui(10)

    @classmethod
    def heading(cls) -> tuple:
        return cls.ui(11, "bold")

    @classmethod
    def metric(cls) -> tuple:
        return cls.ui(20, "bold")

    @classmethod
    def metric_sm(cls) -> tuple:
        return cls.ui(15, "bold")

    @classmethod
    def title(cls) -> tuple:
        return cls.ui(13, "bold")


# ══════════════════════════════════════════════════════════════════════════════
# UTILITIES
# ══════════════════════════════════════════════════════════════════════════════

def sanitize_filename(name: str) -> str:
    if not name:
        return "Unknown"
    cleaned = "".join(c for c in name if c.isalnum() or c in (" ", "_", "-")).strip()
    return (cleaned.replace(" ", "_")[:100]) or "Unknown"


def normalize_process(name: str) -> str:
    name = name.strip()
    return name[:-4] if name.lower().endswith(".exe") else name


def resource_path(rel: str) -> str:
    base = getattr(sys, "_MEIPASS", os.path.abspath("."))
    return os.path.join(base, rel)


def write_atomic(path: Path, content: str, mode: str = "a", encoding: str = "utf-8"):
    try:
        with open(path, mode, encoding=encoding) as f:
            f.write(content)
    except Exception:
        pass


def log_error(msg: str):
    try:
        ts = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        with open("monitor_error.log", "a", encoding="utf-8") as f:
            f.write(f"[{ts}] {msg}\n")
    except Exception:
        pass


def notify(title: str, msg: str):
    try:
        if _TOAST_BACKEND == "win10toast":
            _ToastNotifier().show_toast(title, msg, duration=3, threaded=True)
        elif _TOAST_BACKEND == "plyer":
            _plyer_notify.notify(title=title, message=msg, app_name="KeyStroke Monitor", timeout=3)
    except Exception:
        pass


# ══════════════════════════════════════════════════════════════════════════════
# STORAGE LAYER
# ══════════════════════════════════════════════════════════════════════════════

class EncryptionManager:
    def __init__(self, key_file: Path):
        self.key_file = key_file
        self.fernet = None
        if CRYPTO_AVAILABLE:
            self._load_or_create_key()

    def _load_or_create_key(self):
        try:
            if self.key_file.exists():
                with open(self.key_file, "rb") as f:
                    key = f.read()
            else:
                key = Fernet.generate_key()
                with open(self.key_file, "wb") as f:
                    f.write(key)
            self.fernet = Fernet(key)
        except Exception as e:
            log_error(f"EncryptionManager._load_or_create_key: {e}")

    def encrypt(self, text: str) -> bytes:
        if self.fernet:
            return self.fernet.encrypt(text.encode("utf-8"))
        return text.encode("utf-8")

    def decrypt(self, data: bytes) -> str:
        if self.fernet:
            return self.fernet.decrypt(data).decode("utf-8")
        return data.decode("utf-8")

    @property
    def available(self) -> bool:
        return self.fernet is not None


class AppLogger:
    """Buffered, thread-safe log writer with configurable flush interval."""

    def __init__(self, web_root: Path, sys_root: Path, enc_root: Path,
                 enc_manager: Optional[EncryptionManager] = None):
        self.web_root = web_root
        self.sys_root = sys_root
        self.enc_root = enc_root
        self.enc = enc_manager
        self._buffer: Dict[str, List[str]] = defaultdict(list)
        self._lock = threading.Lock()
        self._last_flush = time.monotonic()

        for d in (web_root, sys_root, enc_root):
            d.mkdir(parents=True, exist_ok=True)

    def _ts(self) -> str:
        return datetime.datetime.now().strftime("%H:%M:%S")

    def log_browser(self, browser: str, site: str, text: str):
        self._enqueue(f"WEB:{browser}:{site}", f"[{self._ts()}] {text}\n")

    def log_system(self, app: str, text: str):
        self._enqueue(f"SYS:{app}", f"[{self._ts()}] {text}\n")

    def log_app(self, app: str, text: str):
        self._enqueue(f"APP:{app}", f"[{self._ts()}] {text}\n")

    def log_clipboard(self, content: str):
        self._enqueue("CLIPBOARD:events", f"[{self._ts()}] [CLIPBOARD] {content}\n")

    def _enqueue(self, key: str, entry: str):
        with self._lock:
            self._buffer[key].append(entry)

    def should_flush(self) -> bool:
        return (time.monotonic() - self._last_flush) >= CONFIG.flush_interval

    def flush(self):
        with self._lock:
            if not self._buffer:
                return
            snapshot = {k: list(v) for k, v in self._buffer.items()}
            self._buffer.clear()
            self._last_flush = time.monotonic()

        for key, entries in snapshot.items():
            if not entries:
                continue
            parts = key.split(":", 2)
            category = parts[0]
            blob = "".join(entries)
            try:
                if category == "WEB" and len(parts) == 3:
                    browser, site = parts[1], parts[2]
                    folder = self.web_root / sanitize_filename(browser)
                    folder.mkdir(exist_ok=True)
                    write_atomic(folder / f"{sanitize_filename(site)}.txt", blob)
                    if self.enc and self.enc.available:
                        enc_data = self.enc.encrypt(blob)
                        write_atomic(self.enc_root / f"{sanitize_filename(site)}.enc", enc_data.decode() + "\n")
                elif category in ("SYS", "APP") and len(parts) >= 2:
                    write_atomic(self.sys_root / f"{sanitize_filename(parts[1])}.txt", blob)
                elif category == "CLIPBOARD":
                    write_atomic(self.sys_root / "clipboard_events.txt", blob)
            except Exception as e:
                log_error(f"AppLogger.flush [{key}]: {e}")


# ══════════════════════════════════════════════════════════════════════════════
# ANALYTICS ENGINE
# ══════════════════════════════════════════════════════════════════════════════

class SessionStats:
    """Thread-safe session analytics."""

    def __init__(self):
        self.start = time.time()
        self.total_keys = 0
        self.total_clicks = 0
        self.clipboard_events = 0
        self.app_keystrokes: Dict[str, int] = defaultdict(int)
        self._rolling: deque = deque(maxlen=3600)
        self._lock = threading.Lock()
        self.peak_kpm = 0.0

    def add_key(self, app: str = "Unknown"):
        with self._lock:
            self.total_keys += 1
            self.app_keystrokes[app] += 1
            self._rolling.append(time.time())

    def add_click(self):
        with self._lock:
            self.total_clicks += 1

    def add_clipboard(self):
        with self._lock:
            self.clipboard_events += 1

    def kpm(self, window: float = None) -> float:
        window = window or CONFIG.kpm_window
        with self._lock:
            now = time.time()
            recent = sum(1 for t in self._rolling if now - t <= window)
            rate = recent * (60.0 / window)
            if rate > self.peak_kpm:
                self.peak_kpm = rate
            return rate

    def wpm(self) -> float:
        return self.kpm() / 5.0

    def elapsed_str(self) -> str:
        s = int(time.time() - self.start)
        h, r = divmod(s, 3600)
        m, s = divmod(r, 60)
        return f"{h:02d}:{m:02d}:{s:02d}" if h else f"{m:02d}:{s:02d}"

    def top_apps(self, n: int = 5) -> List[Tuple[str, int]]:
        with self._lock:
            return sorted(self.app_keystrokes.items(), key=lambda x: x[1], reverse=True)[:n]


class UsageTracker:
    """Tracks foreground application dwell time."""

    def __init__(self):
        self.times: Dict[str, float] = defaultdict(float)
        self._current: Optional[str] = None
        self._current_start: Optional[float] = None
        self._lock = threading.Lock()

    def switch(self, app: str):
        with self._lock:
            now = time.time()
            if self._current and self._current_start:
                self.times[self._current] += now - self._current_start
            self._current = app
            self._current_start = now

    def snapshot(self):
        with self._lock:
            if self._current and self._current_start:
                self.times[self._current] += time.time() - self._current_start
                self._current_start = time.time()

    def top(self, n: int = 10) -> List[Tuple[str, float]]:
        with self._lock:
            return sorted(self.times.items(), key=lambda x: x[1], reverse=True)[:n]


class IdleDetector:
    def __init__(self, threshold: float = None):
        self.threshold = threshold or CONFIG.idle_threshold
        self._last = time.time()
        self._was_idle = False
        self._lock = threading.Lock()

    def activity(self) -> bool:
        """Record activity; returns True if returning from idle."""
        with self._lock:
            self._last = time.time()
            was = self._was_idle
            self._was_idle = False
            return was

    def check(self) -> bool:
        """Returns True once when idle threshold is first crossed."""
        with self._lock:
            idle = (time.time() - self._last) >= self.threshold
            if idle and not self._was_idle:
                self._was_idle = True
                return True
            return False


# ══════════════════════════════════════════════════════════════════════════════
# MONITORING SERVICES
# ══════════════════════════════════════════════════════════════════════════════

BROWSER_MAP = {
    "chrome": "Google Chrome", "firefox": "Firefox", "msedge": "Microsoft Edge",
    "brave": "Brave", "opera": "Opera", "safari": "Safari", "vivaldi": "Vivaldi",
    "thorium": "Thorium", "librewolf": "LibreWolf",
}
APP_MAP = {
    "applicationframehost": "WindowsSystemApp", "systemsettings": "WindowsSettings",
    "mspaint": "Paint", "excel": "MicrosoftExcel", "winword": "MicrosoftWord",
    "powerpnt": "PowerPoint", "onenote": "OneNote", "notepad": "Notepad",
    "calc": "Calculator", "code": "VSCode", "pycharm64": "PyCharm",
    "idea64": "IntelliJ IDEA", "slack": "Slack", "discord": "Discord",
    "spotify": "Spotify", "teams": "Microsoft Teams", "zoom": "Zoom",
    "obsidian": "Obsidian", "notion": "Notion",
}
SYSTEM_APPS = {
    "SystemSettings", "WindowsSettings", "ApplicationFrameHost", "SearchApp",
    "StartMenuExperienceHost", "ShellExperienceHost", "explorer", "FileExplorer",
    "WindowsShell", "taskmgr", "mmc", "control", "regedit", "services",
    "eventvwr", "perfmon", "msconfig", "cmd", "powershell", "WindowsTerminal",
    "conhost", "RuntimeBroker", "SearchUI", "SearchHost", "SettingsHost",
    "Paint", "MicrosoftExcel", "MicrosoftWord", "PowerPoint", "OneNote",
    "Notepad", "Calculator", "WindowsSystemApp",
}

KEY_LABEL_MAP = {
    "SPACE": "[SPC]", "ENTER": "[ENTER]", "BACKSPACE": "[BS]",
    "TAB": "[TAB]", "ESC": "[ESC]", "DELETE": "[DEL]",
    "CTRL_L": "[CTRL]", "CTRL_R": "[CTRL]",
    "SHIFT": "[SHIFT]", "SHIFT_R": "[SHIFT]",
    "ALT": "[ALT]", "ALT_R": "[ALT]",
    "CMD": "[CMD]", "CMD_R": "[CMD]",
}


class ProcessDetector:
    @staticmethod
    def get_active() -> Tuple[str, str]:
        try:
            if sys.platform == "win32" and WIN32_AVAILABLE:
                hwnd = win32gui.GetForegroundWindow()
                title = win32gui.GetWindowText(hwnd)
                _, pid = win32process.GetWindowThreadProcessId(hwnd)
                try:
                    p = psutil.Process(pid)
                    raw = normalize_process(p.name()).lower()
                    for key, display in BROWSER_MAP.items():
                        if key in raw:
                            return display, title
                    for key, display in APP_MAP.items():
                        if key == raw:
                            return display, title
                    if raw == "explorer":
                        label = "FileExplorer" if (title and title != "Program Manager") else "WindowsShell"
                        return label, title
                    return normalize_process(p.name()), title
                except Exception:
                    return "Unknown", title
            elif sys.platform == "darwin":
                from AppKit import NSWorkspace
                app = NSWorkspace.sharedWorkspace().frontmostApplication()
                n = app.localizedName() if app else "Unknown"
                return n, n
            else:
                r = subprocess.run(["xprop", "-root", "_NET_ACTIVE_WINDOW"],
                                   capture_output=True, text=True, timeout=1)
                wid = r.stdout.strip().split()[-1]
                rc = subprocess.run(["xprop", "-id", wid, "WM_CLASS"],
                                    capture_output=True, text=True, timeout=1)
                cls = rc.stdout.split('"')[1] if '"' in rc.stdout else "Unknown"
                rn = subprocess.run(["xprop", "-id", wid, "WM_NAME"],
                                    capture_output=True, text=True, timeout=1)
                wname = rn.stdout.split('"', 1)[1].rsplit('"', 1)[0] if '"' in rn.stdout else "Unknown"
                return cls, wname
        except Exception:
            return "Unknown", "Unknown"


class BrowserDetector:
    _browsers = set(BROWSER_MAP.values())

    @staticmethod
    def is_browser(name: str) -> bool:
        return any(b in name for b in BrowserDetector._browsers)

    @staticmethod
    def extract_site(title: str) -> Optional[str]:
        if not title or title.lower() in ("new tab", "about:blank", ""):
            return "NewTab"
        for sep in (" - ", " — ", " | ", " – "):
            if sep in title:
                for part in title.split(sep):
                    part = part.strip()
                    if part and not any(b in part for b in BrowserDetector._browsers):
                        return sanitize_filename(part[:60])
        return sanitize_filename(title[:60])


class ScreenshotManager:
    def __init__(self, folder: Path):
        self.folder = folder
        self.count = 0
        self._lock = threading.Lock()
        self._last_taken = 0.0

    def take(self, process: str, trigger: str, force: bool = False):
        if not PIL_AVAILABLE:
            return
        now = time.time()
        with self._lock:
            if not force and (now - self._last_taken) < CONFIG.screenshot_cooldown:
                return
            self._last_taken = now
        try:
            ts = datetime.datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
            fname = self.folder / f"{sanitize_filename(trigger)}_{ts}.png"
            img = ImageGrab.grab()
            img.save(fname)
            with self._lock:
                self.count += 1
        except Exception as e:
            log_error(f"ScreenshotManager.take: {e}")


class ClipboardMonitor:
    def __init__(self, callback: Callable[[str], None]):
        self._callback = callback
        self._last = ""
        self._stop = threading.Event()
        self._thread: Optional[threading.Thread] = None

    def start(self):
        if not CLIPBOARD_AVAILABLE:
            return
        self._stop.clear()
        self._thread = threading.Thread(target=self._run, daemon=True, name="ClipboardMonitor")
        self._thread.start()

    def stop(self):
        self._stop.set()

    def _run(self):
        while not self._stop.wait(CONFIG.clipboard_poll):
            try:
                content = pyperclip.paste()
                if content and content != self._last:
                    self._last = content
                    self._callback(content[:200])
            except Exception:
                pass


# ══════════════════════════════════════════════════════════════════════════════
# REPORTING SYSTEM
# ══════════════════════════════════════════════════════════════════════════════

class ReportGenerator:
    def __init__(self, reports_dir: Path):
        self.reports_dir = reports_dir
        self.reports_dir.mkdir(parents=True, exist_ok=True)

    def generate_html(self, stats: SessionStats, usage: UsageTracker,
                      websites: Set[str], screenshots: int) -> Path:
        ts = datetime.datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
        path = self.reports_dir / f"session_{ts}.html"
        elapsed = stats.elapsed_str()

        top_apps_rows = "".join(
            f"<tr><td>{app}</td><td class='num'>{count:,}</td></tr>\n"
            for app, count in stats.top_apps(10)
        )
        usage_rows = "".join(
            f"<tr><td>{app}</td><td class='num'>{int(secs)//60}m {int(secs)%60}s</td></tr>\n"
            for app, secs in usage.top(10)
        )
        site_list = "".join(f"<li>{s}</li>" for s in sorted(websites)) or "<li>None recorded</li>"

        html = f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<title>Session Report — {ts}</title>
<style>
*{{margin:0;padding:0;box-sizing:border-box}}
body{{font-family:'Segoe UI',sans-serif;background:#0f1115;color:#e6e9ef;padding:48px;line-height:1.6}}
h1{{font-size:24px;font-weight:600;color:#e6e9ef;margin-bottom:4px}}
.sub{{color:#9aa3b2;font-size:13px;margin-bottom:40px}}
.grid{{display:grid;grid-template-columns:repeat(auto-fit,minmax(180px,1fr));gap:16px;margin-bottom:40px}}
.card{{background:#151821;border:1px solid #2a2f3a;padding:20px 24px;border-radius:6px}}
.card-val{{font-size:32px;font-weight:700;color:#5b8cff;margin-bottom:2px;letter-spacing:-1px}}
.card-label{{font-size:12px;color:#9aa3b2;text-transform:uppercase;letter-spacing:.5px}}
h2{{font-size:15px;font-weight:600;margin-bottom:14px;color:#e6e9ef;border-bottom:1px solid #2a2f3a;padding-bottom:8px}}
section{{margin-bottom:40px}}
table{{width:100%;border-collapse:collapse;font-size:13px}}
thead tr{{background:#1b1f2a}}
th{{padding:10px 14px;text-align:left;font-size:12px;color:#9aa3b2;font-weight:500;text-transform:uppercase;letter-spacing:.4px;border-bottom:1px solid #2a2f3a}}
td{{padding:9px 14px;border-bottom:1px solid #1e2330;color:#e6e9ef}}
td.num{{text-align:right;color:#5b8cff;font-family:Consolas,monospace}}
ul{{list-style:none;font-size:13px}}
li{{padding:7px 0;border-bottom:1px solid #1e2330;color:#9aa3b2}}
li:last-child{{border-bottom:none}}
.peak{{color:#d29922}}
</style>
</head>
<body>
<h1>KeyStroke Monitor — Session Report</h1>
<p class="sub">Generated {datetime.datetime.now().strftime('%Y-%m-%d at %H:%M:%S')} &nbsp;&middot;&nbsp; Duration: {elapsed}</p>
<div class="grid">
  <div class="card"><div class="card-val">{stats.total_keys:,}</div><div class="card-label">Total Keystrokes</div></div>
  <div class="card"><div class="card-val">{stats.total_clicks:,}</div><div class="card-label">Mouse Clicks</div></div>
  <div class="card"><div class="card-val peak">{stats.peak_kpm:.0f}</div><div class="card-label">Peak Keys / Min</div></div>
  <div class="card"><div class="card-val">{stats.wpm():.0f}</div><div class="card-label">Current WPM</div></div>
  <div class="card"><div class="card-val">{len(websites)}</div><div class="card-label">Sites Visited</div></div>
  <div class="card"><div class="card-val">{screenshots}</div><div class="card-label">Screenshots</div></div>
  <div class="card"><div class="card-val">{stats.clipboard_events}</div><div class="card-label">Clipboard Events</div></div>
</div>
<section>
<h2>Top Apps by Keystrokes</h2>
<table><thead><tr><th>Application</th><th>Keystrokes</th></tr></thead><tbody>{top_apps_rows}</tbody></table>
</section>
<section>
<h2>Time per Application</h2>
<table><thead><tr><th>Application</th><th>Duration</th></tr></thead><tbody>{usage_rows}</tbody></table>
</section>
<section>
<h2>Websites Visited ({len(websites)})</h2>
<ul>{site_list}</ul>
</section>
</body></html>"""
        try:
            with open(path, "w", encoding="utf-8") as f:
                f.write(html)
        except Exception as e:
            log_error(f"ReportGenerator.generate_html: {e}")
        return path

    def generate_json(self, stats: SessionStats, usage: UsageTracker,
                      websites: Set[str], screenshots: int) -> Path:
        ts = datetime.datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
        path = self.reports_dir / f"session_{ts}.json"
        data = {
            "session": {
                "start": datetime.datetime.fromtimestamp(stats.start).isoformat(),
                "end": datetime.datetime.now().isoformat(),
                "duration": stats.elapsed_str(),
            },
            "stats": {
                "total_keystrokes": stats.total_keys,
                "total_clicks": stats.total_clicks,
                "clipboard_events": stats.clipboard_events,
                "peak_kpm": round(stats.peak_kpm, 1),
                "screenshots": screenshots,
            },
            "top_apps": dict(stats.top_apps(20)),
            "time_per_app_seconds": {app: round(secs, 1) for app, secs in usage.top(20)},
            "websites_visited": sorted(websites),
        }
        try:
            with open(path, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2)
        except Exception as e:
            log_error(f"ReportGenerator.generate_json: {e}")
        return path


# ══════════════════════════════════════════════════════════════════════════════
# UI COMPONENTS
# ══════════════════════════════════════════════════════════════════════════════

def _frame(parent, bg=None, **kw) -> tk.Frame:
    return tk.Frame(parent, bg=bg or Theme.BG, **kw)


def _label(parent, text="", font=None, fg=None, bg=None, **kw) -> tk.Label:
    return tk.Label(parent, text=text, font=font or Fonts.body(),
                    fg=fg or Theme.FG, bg=bg or Theme.BG, **kw)


def _divider(parent, bg=None, pady=(8, 8)) -> tk.Frame:
    outer = _frame(parent, bg=bg or Theme.BG2)
    outer.pack(fill=tk.X)
    tk.Frame(outer, height=1, bg=Theme.BORDER).pack(fill=tk.X)
    return outer


class HoverButton(tk.Label):
    """
    Flat label-style button with hover/active states.
    Much lighter than tk.Button for sidebar controls.
    """

    def __init__(self, parent, text: str, command: Callable = None,
                 icon: str = "", bg=None, fg=None, hover_bg=None,
                 active_bg=None, font=None, padx=12, pady=8, **kw):
        self._bg = bg or Theme.BG2
        self._hover_bg = hover_bg or Theme.BG3
        self._active_bg = active_bg or Theme.BG4
        self._fg = fg or Theme.FG
        self._command = command

        display = f"{icon}  {text}" if icon else text
        super().__init__(parent, text=display, font=font or Fonts.body(),
                         fg=self._fg, bg=self._bg, cursor="hand2",
                         padx=padx, pady=pady, anchor="w", **kw)

        self.bind("<Enter>", self._on_enter)
        self.bind("<Leave>", self._on_leave)
        self.bind("<ButtonPress-1>", self._on_press)
        self.bind("<ButtonRelease-1>", self._on_release)

    def _on_enter(self, _):
        self.configure(bg=self._hover_bg)

    def _on_leave(self, _):
        self.configure(bg=self._bg)

    def _on_press(self, _):
        self.configure(bg=self._active_bg)

    def _on_release(self, e):
        self.configure(bg=self._hover_bg)
        if self._command:
            self._command()

    def set_active(self, active: bool):
        self._bg = Theme.BG3 if active else Theme.BG2
        self.configure(bg=self._bg)

    def set_enabled(self, enabled: bool):
        if enabled:
            self.configure(fg=self._fg, cursor="hand2")
        else:
            self.configure(fg=Theme.FG3, cursor="")


class MetricCard(tk.Frame):
    """Sidebar statistic widget: label + large value."""

    def __init__(self, parent, label: str, value: str = "—",
                 value_color=None, **kw):
        super().__init__(parent, bg=Theme.BG3, padx=14, pady=12, **kw)
        self._val_color = value_color or Theme.ACCENT

        _label(self, text=label.upper(), font=Fonts.label(),
               fg=Theme.FG3, bg=Theme.BG3).pack(anchor="w")
        self._val_lbl = _label(self, text=value, font=Fonts.metric(),
                                fg=self._val_color, bg=Theme.BG3)
        self._val_lbl.pack(anchor="w", pady=(2, 0))

    def update(self, value: str):
        self._val_lbl.configure(text=value)


class StatusBar(tk.Frame):
    """Bottom status strip."""

    def __init__(self, parent, **kw):
        super().__init__(parent, bg=Theme.BG2, height=28, **kw)
        self.pack_propagate(False)

        self._left = _label(self, text="Ready", font=Fonts.small(),
                            fg=Theme.FG2, bg=Theme.BG2)
        self._left.pack(side=tk.LEFT, padx=14)

        self._right = _label(self, text="", font=Fonts.small(),
                             fg=Theme.FG3, bg=Theme.BG2)
        self._right.pack(side=tk.RIGHT, padx=14)

    def set_left(self, text: str):
        self._left.configure(text=text)

    def set_right(self, text: str):
        self._right.configure(text=text)


class TabBar(tk.Frame):
    """Minimal underline-style tab bar."""

    def __init__(self, parent, tabs: List[Tuple[str, str]],
                 on_change: Callable[[str], None], **kw):
        super().__init__(parent, bg=Theme.BG2, height=42, **kw)
        self.pack_propagate(False)
        self._on_change = on_change
        self._buttons: Dict[str, tk.Label] = {}
        self._active: Optional[str] = None

        for key, label in tabs:
            btn = tk.Label(self, text=label, font=Fonts.body(),
                           fg=Theme.FG2, bg=Theme.BG2,
                           padx=20, pady=10, cursor="hand2")
            btn.pack(side=tk.LEFT)
            btn.bind("<ButtonRelease-1>", lambda e, k=key: self.select(k))
            btn.bind("<Enter>", lambda e, b=btn: b.configure(fg=Theme.FG))
            btn.bind("<Leave>", lambda e, b=btn, k=key:
                     b.configure(fg=Theme.ACCENT if self._active == k else Theme.FG2))
            self._buttons[key] = btn

        # bottom border
        tk.Frame(self, height=1, bg=Theme.BORDER).place(relx=0, rely=1.0, anchor="sw", relwidth=1)

    def select(self, key: str):
        if key == self._active:
            return
        if self._active and self._active in self._buttons:
            self._buttons[self._active].configure(fg=Theme.FG2, bg=Theme.BG2)
        self._active = key
        self._buttons[key].configure(fg=Theme.ACCENT, bg=Theme.BG2)
        self._on_change(key)

    def initial(self, key: str):
        self._active = key
        if key in self._buttons:
            self._buttons[key].configure(fg=Theme.ACCENT)


class ScrolledLog(tk.Frame):
    """
    High-performance log widget with tag-based syntax highlighting.
    Uses batch inserts and line-count trimming to stay smooth under load.
    """

    TAGS = {
        "ts":        {"foreground": Theme.LOG_TS},
        "keyboard":  {"foreground": Theme.LOG_KB},
        "web":       {"foreground": Theme.LOG_WEB},
        "clipboard": {"foreground": Theme.LOG_CLIP},
        "system":    {"foreground": Theme.LOG_SYS},
    }

    def __init__(self, parent, **kw):
        super().__init__(parent, bg=Theme.BG2, **kw)

        self._text = tk.Text(
            self, font=Fonts.mono(), wrap=tk.WORD, state=tk.DISABLED,
            relief=tk.FLAT, padx=18, pady=14,
            bg=Theme.BG2, fg=Theme.FG, insertbackground=Theme.ACCENT,
            selectbackground=Theme.ACCENT, selectforeground=Theme.FG,
            spacing1=1, spacing2=0, spacing3=2,
            highlightthickness=0, borderwidth=0,
        )
        self._sb = ttk.Scrollbar(self, orient=tk.VERTICAL,
                                 command=self._text.yview)
        self._text.configure(yscrollcommand=self._sb.set)

        self._sb.pack(side=tk.RIGHT, fill=tk.Y)
        self._text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        for tag, cfg in self.TAGS.items():
            self._text.tag_config(tag, **cfg)

    def append_batch(self, entries: List[Tuple[str, str]]):
        """Insert a batch of (text, category) tuples efficiently."""
        self._text.configure(state=tk.NORMAL)
        for line, cat in entries:
            # Split timestamp from content
            if line.startswith("[") and "]" in line:
                bracket_end = line.index("]") + 1
                ts_part = line[:bracket_end]
                rest = line[bracket_end:]
                self._text.insert(tk.END, ts_part, "ts")
                self._text.insert(tk.END, rest + "\n", cat)
            else:
                self._text.insert(tk.END, line + "\n", cat)

        # Trim if needed
        line_count = int(self._text.index("end-1c").split(".")[0])
        if line_count > CONFIG.log_trim_at:
            self._text.delete("1.0", f"{line_count - CONFIG.log_trim_keep}.0")

        self._text.see(tk.END)
        self._text.configure(state=tk.DISABLED)

    def clear(self):
        self._text.configure(state=tk.NORMAL)
        self._text.delete("1.0", tk.END)
        self._text.configure(state=tk.DISABLED)

    def search(self, pattern: str) -> List[str]:
        """Return matching lines from current buffer."""
        content = self._text.get("1.0", tk.END)
        try:
            rx = re.compile(pattern, re.IGNORECASE)
            return [ln for ln in content.splitlines() if rx.search(ln)]
        except re.error:
            return []


class SparklineCanvas(tk.Canvas):
    """Minimal keystroke-rate sparkline."""

    def __init__(self, parent, **kw):
        super().__init__(parent, height=52, bg=Theme.BG2,
                         highlightthickness=0, **kw)

    def draw(self, data: List[float]):
        self.delete("all")
        w = self.winfo_width() or 600
        h = 52
        if len(data) < 2:
            return
        mx = max(data) or 1
        pts = []
        for i, v in enumerate(data):
            x = int(i / (len(data) - 1) * w)
            y = int(h - 8 - (v / mx) * (h - 18))
            pts.extend([x, y])
        if len(pts) >= 4:
            self.create_line(*pts, fill=Theme.ACCENT, width=1, smooth=True)
        self.create_text(8, 6, anchor="nw", text=f"peak {max(data):.0f} k/m",
                         fill=Theme.FG3, font=Fonts.label())
        self.create_text(w - 8, 6, anchor="ne", text=f"now {data[-1]:.0f} k/m",
                         fill=Theme.FG3, font=Fonts.label())


class SearchPanel(tk.Frame):
    """Clean search interface with result count badge."""

    def __init__(self, parent, on_search: Callable[[str], None], **kw):
        super().__init__(parent, bg=Theme.BG, **kw)

        # Search bar
        bar = _frame(self, bg=Theme.BG)
        bar.pack(fill=tk.X, padx=20, pady=14)

        _label(bar, text="Search", font=Fonts.heading(), fg=Theme.FG2, bg=Theme.BG).pack(side=tk.LEFT)

        self._entry = tk.Entry(
            bar, font=Fonts.mono(9), bg=Theme.BG3, fg=Theme.FG,
            insertbackground=Theme.ACCENT, relief=tk.FLAT,
            highlightthickness=1, highlightcolor=Theme.ACCENT,
            highlightbackground=Theme.BORDER,
        )
        self._entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(16, 10), ipady=5)
        self._entry.bind("<Return>", lambda e: on_search(self._entry.get().strip()))

        self._btn = HoverButton(bar, text="Run", command=lambda: on_search(self._entry.get().strip()),
                                bg=Theme.ACCENT, fg="#ffffff",
                                hover_bg=Theme.ACCENT_DIM, active_bg=Theme.ACCENT_DIM,
                                font=Fonts.small(), padx=14, pady=5)
        self._btn.pack(side=tk.LEFT)

        self._count_lbl = _label(bar, text="", font=Fonts.small(), fg=Theme.FG3, bg=Theme.BG)
        self._count_lbl.pack(side=tk.LEFT, padx=(12, 0))

        # Results area
        self._results = ScrolledLog(self)
        self._results.pack(fill=tk.BOTH, expand=True, padx=20, pady=(0, 16))

    def show_results(self, lines: List[str]):
        self._results.clear()
        self._results.append_batch([(ln, "keyboard") for ln in lines])
        self._count_lbl.configure(text=f"{len(lines)} result{'s' if len(lines) != 1 else ''}")


# ══════════════════════════════════════════════════════════════════════════════
# SIDEBAR
# ══════════════════════════════════════════════════════════════════════════════

class Sidebar(tk.Frame):
    """
    Left panel: branding, session controls, status indicator, metric cards.
    """

    def __init__(self, parent, app, **kw):
        super().__init__(parent, bg=Theme.BG2, width=Theme.SIDEBAR_W, **kw)
        self.pack_propagate(False)
        self._app = app
        self._build()

    def _build(self):
        # ── Branding ──────────────────────────────────────────────────────────
        brand = _frame(self, bg=Theme.BG2)
        brand.pack(fill=tk.X, padx=20, pady=(22, 16))

        _label(brand, text="KeyStroke Monitor", font=Fonts.title(),
               fg=Theme.FG, bg=Theme.BG2).pack(anchor="w")
        _label(brand, text="Production Edition", font=Fonts.label(),
               fg=Theme.FG3, bg=Theme.BG2).pack(anchor="w", pady=(2, 0))

        _divider(self, bg=Theme.BG2)

        # ── Status indicator ──────────────────────────────────────────────────
        status_row = _frame(self, bg=Theme.BG2)
        status_row.pack(fill=tk.X, padx=20, pady=(10, 12))

        self._dot_canvas = tk.Canvas(status_row, width=8, height=8,
                                     bg=Theme.BG2, highlightthickness=0)
        self._dot_canvas.pack(side=tk.LEFT, padx=(0, 8))
        self._dot = self._dot_canvas.create_oval(0, 0, 8, 8,
                                                  fill=Theme.FG3, outline="")

        self._status_lbl = _label(status_row, text="Idle",
                                  font=Fonts.small(), fg=Theme.FG2, bg=Theme.BG2)
        self._status_lbl.pack(side=tk.LEFT)

        _divider(self, bg=Theme.BG2)

        # ── Session controls ──────────────────────────────────────────────────
        ctrl = _frame(self, bg=Theme.BG2)
        ctrl.pack(fill=tk.X, pady=(8, 4))

        self.btn_start  = self._control_btn(ctrl, "Start Recording",  "▶",  self._app.start_logging)
        self.btn_pause  = self._control_btn(ctrl, "Pause",            "⏸",  self._app.pause_logging)
        self.btn_stop   = self._control_btn(ctrl, "Stop Session",     "■",  self._app.stop_logging)

        _divider(self, bg=Theme.BG2)

        # ── Tools ─────────────────────────────────────────────────────────────
        tools = _frame(self, bg=Theme.BG2)
        tools.pack(fill=tk.X, pady=(4, 4))

        self._control_btn(tools, "Capture Screenshot",  "⬡",  self._app._manual_screenshot)
        self._control_btn(tools, "Open Data Folder",    "⊞",  self._app.open_folder)
        self._control_btn(tools, "Export Report",       "↗",  self._app.export_report)
        self._control_btn(tools, "Toggle Visibility",   "◎",  self._app.toggle_hide)

        _divider(self, bg=Theme.BG2)

        # ── Metrics ───────────────────────────────────────────────────────────
        metrics = _frame(self, bg=Theme.BG2)
        metrics.pack(fill=tk.X, padx=14, pady=(8, 4))

        self.card_keys   = self._metric_card(metrics, "Keystrokes")
        self.card_kpm    = self._metric_card(metrics, "Keys / Min")
        self.card_wpm    = self._metric_card(metrics, "Words / Min")
        self.card_clicks = self._metric_card(metrics, "Mouse Clicks")
        self.card_time   = self._metric_card(metrics, "Session Time", value_color=Theme.FG2)

        self._update_controls_state()

    def _control_btn(self, parent, label: str, icon: str,
                     cmd: Callable) -> HoverButton:
        btn = HoverButton(parent, text=label, icon=icon, command=cmd,
                          bg=Theme.BG2, fg=Theme.FG,
                          hover_bg=Theme.BG3, active_bg=Theme.BG4,
                          font=Fonts.body(), padx=20, pady=7)
        btn.pack(fill=tk.X)
        return btn

    def _metric_card(self, parent, label: str, value_color=None) -> MetricCard:
        card = MetricCard(parent, label=label, value_color=value_color)
        card.pack(fill=tk.X, pady=3)
        return card

    def set_status(self, state: str):
        colors = {"logging": Theme.SUCCESS, "paused": Theme.WARNING, "idle": Theme.FG3}
        labels = {"logging": "Recording", "paused": "Paused", "idle": "Idle"}
        color = colors.get(state, Theme.FG3)
        self._dot_canvas.itemconfig(self._dot, fill=color)
        self._status_lbl.configure(text=labels.get(state, "Idle"))

    def _update_controls_state(self):
        is_logging = self._app.is_logging
        is_paused = self._app.is_paused
        self.btn_start.set_enabled(not is_logging)
        self.btn_pause.set_enabled(is_logging)
        self.btn_stop.set_enabled(is_logging)

    def refresh_controls(self):
        self._update_controls_state()


# ══════════════════════════════════════════════════════════════════════════════
# APPS / SITES VIEWS
# ══════════════════════════════════════════════════════════════════════════════

class AppsView(tk.Frame):
    """Canvas-drawn bar chart for top apps by keystroke count."""

    def __init__(self, parent, **kw):
        super().__init__(parent, bg=Theme.BG, **kw)

        header = _frame(self, bg=Theme.BG)
        header.pack(fill=tk.X, padx=20, pady=(18, 8))
        _label(header, text="Top Applications", font=Fonts.heading(),
               fg=Theme.FG, bg=Theme.BG).pack(side=tk.LEFT)
        self._session_lbl = _label(header, text="", font=Fonts.small(),
                                   fg=Theme.FG3, bg=Theme.BG)
        self._session_lbl.pack(side=tk.RIGHT)

        self._canvas = tk.Canvas(self, bg=Theme.BG, highlightthickness=0)
        self._sb = ttk.Scrollbar(self, orient=tk.VERTICAL, command=self._canvas.yview)
        self._canvas.configure(yscrollcommand=self._sb.set)
        self._sb.pack(side=tk.RIGHT, fill=tk.Y)
        self._canvas.pack(fill=tk.BOTH, expand=True, padx=20)

        self._inner = _frame(self._canvas, bg=Theme.BG)
        self._canvas.create_window((0, 0), window=self._inner, anchor="nw")
        self._inner.bind("<Configure>", lambda e: self._canvas.configure(
            scrollregion=self._canvas.bbox("all")))

    def refresh(self, stats: Optional[SessionStats], usage: Optional[UsageTracker]):
        for w in self._inner.winfo_children():
            w.destroy()
        if not stats:
            _label(self._inner, text="No session data.", font=Fonts.body(),
                   fg=Theme.FG3, bg=Theme.BG).pack(padx=20, pady=40)
            return

        self._session_lbl.configure(text=f"Session: {stats.elapsed_str()}")
        total = max(stats.total_keys, 1)

        _label(self._inner, text="Keystrokes", font=Fonts.label(),
               fg=Theme.FG3, bg=Theme.BG).pack(anchor="w", pady=(8, 6))

        for app, count in stats.top_apps(20):
            pct = count / total
            self._bar_row(self._inner, app, count, pct)

        if usage:
            _label(self._inner, text="Time Spent", font=Fonts.label(),
                   fg=Theme.FG3, bg=Theme.BG).pack(anchor="w", pady=(20, 6))
            top = usage.top(10)
            max_t = max((t for _, t in top), default=1)
            for app, secs in top:
                m, s = divmod(int(secs), 60)
                label = f"{m}m {s}s"
                self._bar_row(self._inner, app, label, secs / max(max_t, 1))

    def _bar_row(self, parent, name: str, value, pct: float):
        row = _frame(parent, bg=Theme.BG)
        row.pack(fill=tk.X, pady=3)

        _label(row, text=name[:32], font=Fonts.mono(9),
               fg=Theme.FG2, bg=Theme.BG, width=26, anchor="w").pack(side=tk.LEFT)

        bar_outer = _frame(row, bg=Theme.BG3)
        bar_outer.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(8, 12))
        bar_outer.configure(height=14)
        bar_inner = _frame(bar_outer, bg=Theme.ACCENT)
        bar_inner.place(relx=0, rely=0, relheight=1, relwidth=max(0.002, pct))

        val_text = f"{value:,}" if isinstance(value, int) else str(value)
        _label(row, text=val_text, font=Fonts.mono(9),
               fg=Theme.FG2, bg=Theme.BG, width=10, anchor="e").pack(side=tk.LEFT)


class SitesView(tk.Frame):
    """Clean list of visited websites."""

    def __init__(self, parent, **kw):
        super().__init__(parent, bg=Theme.BG, **kw)

        header = _frame(self, bg=Theme.BG)
        header.pack(fill=tk.X, padx=20, pady=(18, 8))
        _label(header, text="Browser Activity", font=Fonts.heading(),
               fg=Theme.FG, bg=Theme.BG).pack(side=tk.LEFT)
        self._count_lbl = _label(header, text="", font=Fonts.small(),
                                  fg=Theme.FG3, bg=Theme.BG)
        self._count_lbl.pack(side=tk.RIGHT)

        container = _frame(self, bg=Theme.BG)
        container.pack(fill=tk.BOTH, expand=True, padx=20, pady=(0, 16))

        self._text = tk.Text(
            container, font=Fonts.mono(9), state=tk.DISABLED, relief=tk.FLAT,
            bg=Theme.BG2, fg=Theme.FG2, padx=16, pady=14,
            highlightthickness=0, spacing1=1, spacing3=2,
        )
        sb = ttk.Scrollbar(container, orient=tk.VERTICAL, command=self._text.yview)
        self._text.configure(yscrollcommand=sb.set)
        sb.pack(side=tk.RIGHT, fill=tk.Y)
        self._text.pack(fill=tk.BOTH, expand=True)

    def refresh(self, sites: Set[str]):
        self._text.configure(state=tk.NORMAL)
        self._text.delete("1.0", tk.END)
        if not sites:
            self._text.insert(tk.END, "No sites recorded yet.")
            self._count_lbl.configure(text="")
        else:
            self._count_lbl.configure(text=f"{len(sites)} site{'s' if len(sites) != 1 else ''}")
            for s in sorted(sites):
                self._text.insert(tk.END, f"  {s}\n")
        self._text.configure(state=tk.DISABLED)


# ══════════════════════════════════════════════════════════════════════════════
# SESSION MANAGER
# ══════════════════════════════════════════════════════════════════════════════

class SessionManager:
    """
    Owns all session-scoped components and their lifecycle.
    Separates session state from UI state.
    """

    def __init__(self, root_dir: Path):
        self.root_dir = root_dir
        self.stats: Optional[SessionStats] = None
        self.usage: Optional[UsageTracker] = None
        self.idle: Optional[IdleDetector] = None
        self.app_logger: Optional[AppLogger] = None
        self.screenshot_mgr: Optional[ScreenshotManager] = None
        self.enc_manager: Optional[EncryptionManager] = None
        self.report_gen: Optional[ReportGenerator] = None
        self.clipboard_mon: Optional[ClipboardMonitor] = None
        self.unique_sites: Set[str] = set()

    def setup(self, clipboard_callback: Callable):
        ks_dir   = self.root_dir / "Keystrokes"
        web_dir  = ks_dir / "Browser-Sessions"
        sys_dir  = ks_dir / "System-Apps"
        shot_dir = ks_dir / "Screenshots"
        enc_dir  = ks_dir / "Encrypted"
        rep_dir  = self.root_dir / "Reports"

        for d in (web_dir, sys_dir, shot_dir, enc_dir, rep_dir):
            d.mkdir(parents=True, exist_ok=True)

        self.enc_manager    = EncryptionManager(self.root_dir / ".session.key")
        self.app_logger     = AppLogger(web_dir, sys_dir, enc_dir, self.enc_manager)
        self.screenshot_mgr = ScreenshotManager(shot_dir)
        self.stats          = SessionStats()
        self.usage          = UsageTracker()
        self.idle           = IdleDetector()
        self.report_gen     = ReportGenerator(rep_dir)
        self.unique_sites   = set()

        if CLIPBOARD_AVAILABLE:
            self.clipboard_mon = ClipboardMonitor(clipboard_callback)
            self.clipboard_mon.start()

    def teardown(self):
        if self.clipboard_mon:
            self.clipboard_mon.stop()
            self.clipboard_mon = None
        if self.app_logger:
            self.app_logger.flush()


# ══════════════════════════════════════════════════════════════════════════════
# MAIN APPLICATION
# ══════════════════════════════════════════════════════════════════════════════

class KeyStrokeMonitor:
    """
    Top-level application controller.
    Delegates to: SessionManager, Sidebar, content views, background workers.
    """

    def __init__(self, root: tk.Tk):
        self.root = root
        self.is_logging = False
        self.is_paused = False
        self.is_hidden = False

        # Derived paths
        _base = Path(getattr(sys, "_MEIPASS", os.path.dirname(os.path.abspath(__file__))))
        self._root_dir = _base / CONFIG.root_dir

        # Session manager (owns session-scoped singletons)
        self._session = SessionManager(self._root_dir)

        # Input state (thread-safe)
        self._current_process: Optional[str] = None
        self._current_window:  Optional[str] = None
        self._current_site:    Optional[str] = None
        self._keystroke_buffer: List[str] = []
        self._context_lock = threading.Lock()

        # Listeners
        self._kb_listener   = None
        self._mouse_listener = None
        self._hotkey_listener = None

        # Queues
        self._stop_event     = threading.Event()
        self._shutdown_event = threading.Event()
        self._log_queue: queue.Queue = queue.Queue(maxsize=CONFIG.log_buffer_max)
        self._ui_queue:  queue.Queue = queue.Queue(maxsize=CONFIG.ui_queue_max)

        # Sparkline data
        self._kpm_history: deque = deque(maxlen=60)

        # Asset registry
        self._icons: Dict[str, tk.PhotoImage] = {}

        Fonts.init()
        self._load_icons()
        self._build_ui()
        self._apply_ttk_style()
        self._start_background_workers()
        self._start_hotkeys()

        self.root.protocol("WM_DELETE_WINDOW", self._on_close)
        self._pump_ui_queue()

    # ── Asset management ───────────────────────────────────────────────────────

    def _load_icons(self):
        if not PIL_AVAILABLE:
            return
        specs = {
            "app": ("assets/app.ico", None),
        }
        for key, (path, size) in specs.items():
            try:
                full = resource_path(path)
                if not os.path.exists(full):
                    continue
                if size:
                    img = Image.open(full).resize(size, Image.Resampling.LANCZOS)
                    self._icons[key] = ImageTk.PhotoImage(img)
                else:
                    self.root.iconbitmap(full)
            except Exception:
                pass

    # ── UI construction ────────────────────────────────────────────────────────

    def _build_ui(self):
        self.root.title("KeyStroke Monitor")
        self.root.geometry("1320x820")
        self.root.minsize(900, 600)
        self.root.configure(bg=Theme.BG2)

        try:
            self.root.state("zoomed")
        except Exception:
            pass

        # DPI awareness (Windows)
        if sys.platform == "win32":
            try:
                from ctypes import windll
                windll.shcore.SetProcessDpiAwareness(1)
            except Exception:
                pass

        # ── Layout skeleton ────────────────────────────────────────────────────
        self._sidebar = Sidebar(self.root, app=self)
        self._sidebar.pack(side=tk.LEFT, fill=tk.Y)

        # Vertical separator
        tk.Frame(self.root, width=1, bg=Theme.BORDER).pack(side=tk.LEFT, fill=tk.Y)

        # Main content column
        self._content = _frame(self.root, bg=Theme.BG)
        self._content.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        # Tab bar
        tabs = [("live", "Live Feed"), ("apps", "Applications"),
                ("sites", "Browser"), ("search", "Search")]
        self._tabbar = TabBar(self._content, tabs=tabs, on_change=self._switch_tab)
        self._tabbar.pack(fill=tk.X)

        # Pages
        self._pages: Dict[str, tk.Frame] = {}

        self._live_page = _frame(self._content, bg=Theme.BG)
        self._pages["live"] = self._live_page
        self._log_view = ScrolledLog(self._live_page)
        self._log_view.pack(fill=tk.BOTH, expand=True, padx=0, pady=0)

        self._apps_view = AppsView(self._content)
        self._pages["apps"] = self._apps_view

        self._sites_view = SitesView(self._content)
        self._pages["sites"] = self._sites_view

        self._search_page = _frame(self._content, bg=Theme.BG)
        self._pages["search"] = self._search_page
        self._search_panel = SearchPanel(self._search_page, on_search=self._do_search)
        self._search_panel.pack(fill=tk.BOTH, expand=True)

        # Sparkline
        self._sparkline = SparklineCanvas(self._content)
        self._sparkline.pack(fill=tk.X, padx=1, pady=0)

        # Status bar
        self._statusbar = StatusBar(self._content)
        self._statusbar.pack(fill=tk.X, side=tk.BOTTOM)
        self._update_statusbar_hints()

        # Show initial page
        self._current_tab = "live"
        self._live_page.pack(fill=tk.BOTH, expand=True)
        self._tabbar.initial("live")

    def _apply_ttk_style(self):
        style = ttk.Style()
        style.theme_use("clam")
        style.configure("Vertical.TScrollbar",
                        gripcount=0, background=Theme.BG3,
                        troughcolor=Theme.BG2, bordercolor=Theme.BG2,
                        arrowcolor=Theme.FG3, relief=tk.FLAT)
        style.map("Vertical.TScrollbar",
                  background=[("active", Theme.BG4)])

    def _update_statusbar_hints(self):
        parts = []
        if CRYPTO_AVAILABLE:
            parts.append("Encrypted")
        if CLIPBOARD_AVAILABLE:
            parts.append("Clipboard")
        if PIL_AVAILABLE:
            parts.append("Screenshots")
        hint = "  ·  ".join(parts) + "  —  F12 Hide  F11 Pause  F10 Screenshot"
        self._statusbar.set_right(hint)

    # ── Tab management ─────────────────────────────────────────────────────────

    def _switch_tab(self, tab: str):
        if self._current_tab:
            self.pages_get(self._current_tab).pack_forget()
        page = self.pages_get(tab)
        page.pack(fill=tk.BOTH, expand=True)
        self._current_tab = tab

        if tab == "apps":
            self._apps_view.refresh(self._session.stats, self._session.usage)
        elif tab == "sites":
            self._sites_view.refresh(self._session.unique_sites)

    def pages_get(self, key: str) -> tk.Frame:
        return self._pages[key]

    # ── Session control ────────────────────────────────────────────────────────

    def start_logging(self):
        if self.is_logging:
            return
        try:
            self._root_dir.mkdir(parents=True, exist_ok=True)
            self._session.setup(clipboard_callback=self._on_clipboard)
        except Exception as e:
            messagebox.showerror("Error", f"Cannot start session:\n{e}")
            return

        self.is_logging = True
        self.is_paused = False
        self._current_process = self._current_window = self._current_site = None
        self._keystroke_buffer.clear()
        self._stop_event.clear()
        self._kpm_history.clear()

        self._sidebar.refresh_controls()
        self._sidebar.set_status("logging")
        self._statusbar.set_left("Recording — session started")

        threading.Thread(target=self._keyboard_worker, daemon=True, name="KBLogger").start()
        threading.Thread(target=self._mouse_worker,    daemon=True, name="MSLogger").start()
        notify("KeyStroke Monitor", "Session started")

    def stop_logging(self):
        if not self.is_logging:
            return
        self.is_logging = False
        self.is_paused = False
        self._stop_event.set()

        self._commit_buffer()
        self._session.teardown()

        for listener in (self._kb_listener, self._mouse_listener):
            if listener:
                try:
                    listener.stop()
                except Exception:
                    pass

        self._export_session(silent=True)

        self._sidebar.refresh_controls()
        self._sidebar.set_status("idle")

        if self._session.stats:
            self._statusbar.set_left(
                f"Session ended — {self._session.stats.total_keys:,} keystrokes")
        notify("KeyStroke Monitor",
               f"Session ended — {self._session.stats.total_keys if self._session.stats else 0:,} keystrokes")

    def pause_logging(self):
        if not self.is_logging:
            return
        self.is_paused = not self.is_paused
        state = "paused" if self.is_paused else "logging"
        self._sidebar.set_status(state)
        self._statusbar.set_left("Paused" if self.is_paused else "Recording")

    def toggle_hide(self):
        self.is_hidden = not self.is_hidden
        if self.is_hidden:
            self.root.withdraw()
        else:
            self.root.deiconify()
            self.root.lift()
            self.root.focus_force()

    # ── Actions ────────────────────────────────────────────────────────────────

    def _manual_screenshot(self):
        mgr = self._session.screenshot_mgr
        if not mgr:
            return
        proc = self._current_process or "Manual"
        threading.Thread(target=lambda: mgr.take(proc, "manual", force=True),
                         daemon=True).start()

    def open_folder(self):
        self._root_dir.mkdir(parents=True, exist_ok=True)
        path = str(self._root_dir.resolve())
        try:
            if sys.platform == "win32":
                os.startfile(path)
            elif sys.platform == "darwin":
                subprocess.Popen(["open", path])
            else:
                subprocess.Popen(["xdg-open", path])
        except Exception as e:
            messagebox.showerror("Error", f"Cannot open folder:\n{e}")

    def export_report(self, silent: bool = False):
        s = self._session
        if not s.stats or not s.report_gen:
            if not silent:
                messagebox.showinfo("Export", "No session data. Start logging first.")
            return
        if s.usage:
            s.usage.snapshot()
        shots = s.screenshot_mgr.count if s.screenshot_mgr else 0
        html_path = s.report_gen.generate_html(s.stats, s.usage, s.unique_sites, shots)
        json_path = s.report_gen.generate_json(s.stats, s.usage, s.unique_sites, shots)
        if not silent:
            msg = f"Reports saved:\n{html_path}\n{json_path}"
            if messagebox.askyesno("Export Complete", msg + "\n\nOpen HTML report?"):
                self._open_file(html_path)

    def _export_session(self, silent: bool = True):
        self.export_report(silent=silent)

    def _open_file(self, path: Path):
        try:
            if sys.platform == "win32":
                os.startfile(str(path))
            elif sys.platform == "darwin":
                subprocess.Popen(["open", str(path)])
            else:
                subprocess.Popen(["xdg-open", str(path)])
        except Exception:
            pass

    def _do_search(self, query: str):
        if not query:
            return
        results = self._log_view.search(query)
        self._search_panel.show_results(results)

    # ── Input capture ──────────────────────────────────────────────────────────

    def _keyboard_worker(self):
        def on_press(key):
            if not self.is_logging or self.is_paused:
                return
            try:
                proc, window = ProcessDetector.get_active()

                with self._context_lock:
                    changed = False
                    new_site = None
                    if proc != self._current_process:
                        changed = True
                    elif BrowserDetector.is_browser(proc):
                        new_site = BrowserDetector.extract_site(window)
                        if new_site != self._current_site:
                            changed = True
                    elif window != self._current_window:
                        changed = True

                    if changed:
                        self._commit_buffer_locked(self._current_process, self._current_site)
                        self._current_process = proc
                        self._current_window  = window
                        self._current_site    = new_site if BrowserDetector.is_browser(proc) else None
                        self._on_app_change(proc, window)

                if self._session.idle and self._session.idle.activity():
                    self._enqueue_log("[SYSTEM] Activity resumed after idle", "system")

                key_str = self._process_key(key)
                if not key_str:
                    return

                if self._session.stats:
                    self._session.stats.add_key(proc)

                # Modifier keys: count only, don't buffer
                if key_str in ("[SHIFT]", "[CTRL]", "[ALT]", "[CMD]", "[TAB]"):
                    return

                if key_str == "[BS]":
                    with self._context_lock:
                        if self._keystroke_buffer:
                            self._keystroke_buffer.pop()
                    return

                if key_str == "[ENTER]":
                    self._commit_buffer()
                    if self._current_process and self._session.screenshot_mgr:
                        p = self._current_process
                        mgr = self._session.screenshot_mgr
                        threading.Thread(target=lambda: mgr.take(p, "enter"),
                                         daemon=True).start()
                    return

                with self._context_lock:
                    self._keystroke_buffer.append(key_str)

                self._enqueue_log(f"[{proc}] {key_str}", "keyboard")

            except Exception as e:
                log_error(f"_keyboard_worker.on_press: {e}")

        try:
            self._kb_listener = keyboard.Listener(on_press=on_press)
            self._kb_listener.start()
            self._stop_event.wait()
        except Exception as e:
            log_error(f"_keyboard_worker: {e}")

    def _mouse_worker(self):
        def on_click(x, y, button, pressed):
            if not self.is_logging or self.is_paused or not pressed:
                return
            try:
                if self._session.idle:
                    self._session.idle.activity()
                if self._session.stats:
                    self._session.stats.add_click()
                if button == mouse.Button.left:
                    self._commit_buffer()
                    if self._current_process and self._session.screenshot_mgr:
                        p = self._current_process
                        mgr = self._session.screenshot_mgr
                        threading.Thread(target=lambda: mgr.take(p, "click"),
                                         daemon=True).start()
            except Exception as e:
                log_error(f"_mouse_worker.on_click: {e}")

        def on_scroll(x, y, dx, dy):
            if self.is_logging and not self.is_paused and self._session.idle:
                self._session.idle.activity()

        try:
            self._mouse_listener = mouse.Listener(on_click=on_click, on_scroll=on_scroll)
            self._mouse_listener.start()
            self._stop_event.wait()
        except Exception as e:
            log_error(f"_mouse_worker: {e}")

    def _start_hotkeys(self):
        if not PYNPUT_AVAILABLE:
            return

        def on_press(key):
            try:
                k = str(key).replace("Key.", "").lower()
                if   k == "f12": self._enqueue_ui(self.toggle_hide)
                elif k == "f11": self._enqueue_ui(self.pause_logging)
                elif k == "f10": self._enqueue_ui(self._manual_screenshot)
            except Exception:
                pass

        try:
            self._hotkey_listener = keyboard.Listener(on_press=on_press)
            self._hotkey_listener.start()
        except Exception as e:
            log_error(f"_start_hotkeys: {e}")

    # ── Key / app processing ───────────────────────────────────────────────────

    def _process_key(self, key) -> Optional[str]:
        try:
            if hasattr(key, "char") and key.char:
                return key.char
            k = str(key).replace("Key.", "").upper()
            return KEY_LABEL_MAP.get(k, f"[{k}]")
        except Exception:
            return None

    def _on_app_change(self, proc: str, window: str):
        if self._session.usage:
            self._session.usage.switch(proc)
        if self._session.screenshot_mgr:
            mgr = self._session.screenshot_mgr
            threading.Thread(target=lambda: mgr.take(proc, "appchange"),
                             daemon=True).start()
        if BrowserDetector.is_browser(proc):
            site = BrowserDetector.extract_site(window)
            if site:
                self._session.unique_sites.add(site)
                self._enqueue_log(f"[WEB] {site}  ({proc})", "web")

    def _on_clipboard(self, content: str):
        if not self.is_logging or self.is_paused:
            return
        if self._session.stats:
            self._session.stats.add_clipboard()
        if self._session.app_logger:
            self._session.app_logger.log_clipboard(content)
        preview = content[:80] + ("…" if len(content) > 80 else "")
        self._enqueue_log(f"[CLIPBOARD] {preview}", "clipboard")

    def _commit_buffer_locked(self, proc: Optional[str], site: Optional[str]):
        """Must be called with _context_lock held."""
        if not self._keystroke_buffer or not self._session.app_logger:
            return
        if not proc:
            self._keystroke_buffer.clear()
            return
        text = "".join(self._keystroke_buffer).replace("[SPC]", " ").replace("[ENTER]", "\n").strip()
        self._keystroke_buffer.clear()
        if not text:
            return
        logger = self._session.app_logger
        if BrowserDetector.is_browser(proc) and site:
            logger.log_browser(proc, site, text)
        elif proc in SYSTEM_APPS:
            logger.log_system(proc, text)
        else:
            logger.log_app(proc, text)

    def _commit_buffer(self):
        with self._context_lock:
            self._commit_buffer_locked(self._current_process, self._current_site)

    # ── UI event bus ───────────────────────────────────────────────────────────

    def _enqueue_log(self, entry: str, category: str = "keyboard"):
        ts = datetime.datetime.now().strftime("%H:%M:%S")
        try:
            self._log_queue.put_nowait((f"[{ts}] {entry}", category))
        except queue.Full:
            pass
        self._enqueue_ui(self._flush_log_to_view)

    def _enqueue_ui(self, fn: Callable):
        try:
            self._ui_queue.put_nowait(fn)
        except queue.Full:
            pass

    def _pump_ui_queue(self):
        try:
            limit = 20  # drain up to N items per tick to avoid jank
            while limit and not self._ui_queue.empty():
                fn = self._ui_queue.get_nowait()
                try:
                    fn()
                except Exception:
                    pass
                limit -= 1
        except Exception:
            pass
        if not self._shutdown_event.is_set():
            self.root.after(CONFIG.ui_poll_ms, self._pump_ui_queue)

    def _flush_log_to_view(self):
        entries = []
        while not self._log_queue.empty():
            try:
                entries.append(self._log_queue.get_nowait())
            except queue.Empty:
                break
        if entries:
            self._log_view.append_batch(entries)

    # ── Background workers ─────────────────────────────────────────────────────

    def _start_background_workers(self):
        workers = [
            ("Flusher",   self._worker_flush),
            ("Idle",      self._worker_idle),
            ("Stats",     self._worker_stats),
            ("Usage",     self._worker_usage),
            ("Sparkline", self._worker_sparkline),
        ]
        for name, target in workers:
            threading.Thread(target=target, daemon=True, name=name).start()

    def _worker_flush(self):
        while not self._shutdown_event.wait(1.0):
            try:
                lg = self._session.app_logger
                if self.is_logging and not self.is_paused and lg and lg.should_flush():
                    lg.flush()
            except Exception as e:
                log_error(f"_worker_flush: {e}")

    def _worker_idle(self):
        while not self._shutdown_event.wait(5.0):
            try:
                idle_det = self._session.idle
                if self.is_logging and not self.is_paused and idle_det:
                    if idle_det.check():
                        self._enqueue_log("[SYSTEM] User idle", "system")
            except Exception as e:
                log_error(f"_worker_idle: {e}")

    def _worker_stats(self):
        while not self._shutdown_event.wait(1.0):
            try:
                stats = self._session.stats
                if self.is_logging and not self.is_paused and stats:
                    kpm     = stats.kpm()
                    wpm     = stats.wpm()
                    keys    = stats.total_keys
                    clicks  = stats.total_clicks
                    elapsed = stats.elapsed_str()
                    self._kpm_history.append(kpm)

                    def _update(k=keys, km=kpm, wm=wpm, cl=clicks, t=elapsed):
                        sb = self._sidebar
                        sb.card_keys.update(f"{k:,}")
                        sb.card_kpm.update(f"{km:.0f}")
                        sb.card_wpm.update(f"{wm:.1f}")
                        sb.card_clicks.update(f"{cl:,}")
                        sb.card_time.update(t)
                        self._statusbar.set_left(f"Recording  ·  {k:,} keys  ·  {km:.0f} k/m  ·  {t}")

                    self._enqueue_ui(_update)
            except Exception as e:
                log_error(f"_worker_stats: {e}")

    def _worker_usage(self):
        while not self._shutdown_event.wait(30.0):
            try:
                if self.is_logging and self._session.usage:
                    self._session.usage.snapshot()
            except Exception as e:
                log_error(f"_worker_usage: {e}")

    def _worker_sparkline(self):
        while not self._shutdown_event.wait(2.0):
            try:
                if self._kpm_history:
                    data = list(self._kpm_history)
                    self._enqueue_ui(lambda d=data: self._sparkline.draw(d))
            except Exception as e:
                log_error(f"_worker_sparkline: {e}")

    # ── Shutdown ───────────────────────────────────────────────────────────────

    def _on_close(self):
        self._shutdown_event.set()
        if self.is_logging:
            self.stop_logging()
        for listener in (self._hotkey_listener, self._kb_listener, self._mouse_listener):
            if listener:
                try:
                    listener.stop()
                except Exception:
                    pass
        self.root.after(150, self.root.destroy)


# ══════════════════════════════════════════════════════════════════════════════
# ENTRY POINT
# ══════════════════════════════════════════════════════════════════════════════

def main():
    root = tk.Tk()
    app = KeyStrokeMonitor(root)
    root.mainloop()


if __name__ == "__main__":
    main()
