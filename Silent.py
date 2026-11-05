"""
Silent PC Sender
Invia l'audio del PC (o di un microfono) all'app Android Silent via Wi-Fi.

Installazione (una volta sola):
    pip install pyaudiowpatch numpy

Formato inviato: UDP, PCM 16 bit mono 16 kHz, pacchetti da 512 campioni, porta 5005.
Se il PC non riproduce audio, invia comunque pacchetti di silenzio:
cosi' Silent sa che il PC e' collegato.

Novita' di questa versione:
- "Uscita predefinita": segue da sola i cambi di uscita di Windows (cuffie, casse, HDMI...)
  senza dover riavviare l'invio.
- Se lo stream audio si interrompe (dispositivo scollegato, driver riavviato) si riconnette da solo.
- Ricampionamento continuo e senza deriva (prima ogni blocco veniva ricampionato a parte).
- Controllo dell'IP/nome del tablet prima di avviare, pulsante per aggiornare i dispositivi,
  opzione "Avvia all'apertura", campi bloccati mentre l'invio e' attivo.
- Grafica come l'app Android: logo, cerchio di stato (verde = silenzio, arancione = audio),
  barra del livello, card e pulsanti arrotondati. Si adatta alla scala di Windows (125%, 150%...)
  e la finestra si dimensiona da sola: niente piu' pulsanti tagliati.
"""
import base64
import ctypes
import ctypes.wintypes
import json
import os
import queue
import socket
import struct
import threading
import time
import tkinter as tk
import zlib
from tkinter import ttk

import numpy as np

try:
    import pyaudiowpatch as pyaudio
except ImportError:  # messaggio chiaro invece di un errore criptico
    pyaudio = None

PORT = 5005
OUT_RATE = 16000
PACKET_SAMPLES = 512
CONFIG = os.path.join(os.path.expanduser("~"), ".silent_pc_sender.json")

DEFAULT_LABEL = "Audio del PC - uscita predefinita (consigliato)"

BG = "#0F1420"
CARD = "#1A2132"
TRACK = "#232C42"
WHITE = "#FFFFFF"
GREY = "#6B7690"
ORANGE = "#FF9F43"
GREEN = "#2ED573"


# Logo di Silent (PNG incorporati): icona della finestra e della barra delle applicazioni
ICON_PNGS = (
    (
    "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"
    "AAAAAElFTkSuQmCC"
    ),
    (
    "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"
    "rQAAAABJRU5ErkJggg=="
    ),
    (
    "iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAABCGlDQ1BJQ0MgUHJvZmlsZQAAeJxjYGA8wQAELAYMDLl5JUVB7k4K"
    "EZFRCuwPGBiBEAwSk4sLGHADoKpv1yBqL+viUYcLcKakFicD6Q9ArFIEtBxopAiQLZIOYWuA2EkQtg2IXV5SUAJkB4DYRSFBzkB2"
    "CpCtkY7ETkJiJxcUgdT3ANk2uTmlyQh3M/Ck5oUGA2kOIJZhKGYIYnBncAL5H6IkfxEDg8VXBgbmCQixpJkMDNtbGRgkbiHEVBYw"
    "MPC3MDBsO48QQ4RJQWJRIliIBYiZ0tIYGD4tZ2DgjWRgEL7AwMAVDQsIHG5TALvNnSEfCNMZchhSgSKeDHkMyQx6QJYRgwGDIYMZ"
    "AKbWPz9HbOBQAAAECUlEQVR42sWXTY9URRSGn/dU3RmYYSAzMiIDCCbGBFawMIYdf4AYTVy5deHOuGfBgr0/gB9gNBjj0p07YlzI"
    "ChLZEOZDYJJuCYPMzL11jou+Dd3DdDNfaiWV2/dWqs+p933rfIhXwwAHmJ09+a7n6sPAFiKK9ZYTUHb9lJI7vlI19W/d7p8Pt9rS"
    "4IfZ2YUzkdN1Qp+E0iyIkGMOwigWKAQEIWEeCI3+rsAQTqCgq2h+lJfr3e7KYt+m+j/m5k595JZ+wvKJcKf1MDiYIZDJBKU8tmg+"
    "7nSWfwVMgObmTi+46fdieV4etSAPoHNQI4BGsgr3VYvqUqdzf8WAcHEDVfPyUguqf8F4n+4qotSyNB+qbwChublTp4vSPZSne+KR"
    "Ru0edCu2kDO0K8ZyF7395XkOP59L4jKkI4Q7yLY1LvCA0kTvJYKc9NKfAOqBtZSE6XUnB87iMjsCupw9bMFEjBKcBJtNcCjBWzMJ"
    "j0Ayus8LTbsjCeZnEhE9VT39u7DewETWCCciQoratZAhYSH5NvYlqEtwYibzw5dneO94oqlrcpW5s1jz2c2HKMT3X5zh4tlE2XDS"
    "ROLBk+DTm4usrhVy2g4JoTAFTm553xYrE6zXwYV3Ki69X8F6A5MZFFw5P83JowlCXLkwBc0GTCbAuPiBuHCy4ud7DUezKDFKCoXc"
    "i1gae+UbD3zDodFLEqOJ3skCyoZjiKAlfhNK8fboGqfF8QgMUmEYoV5sEiD5EFIadSPeMOwVAjuIJENkCu0rXBiQsB4CO4i48p65"
    "GLzstg8HHCi7QUCvvccADfvAoewx50QL434i8y41MAyE0L6SpXapgeHb02pA/6UG2EYD8X9rQLj2CoTwPWlgKA44ir3WTT0N7CgS"
    "BuDRhlYJAhyHaCu+Nv9HXxqxE58c20kuCCCZsAlBafNtQMoJmUOINGnQtJExAiZEtlGpeDASviEXeIjDlbj36AV3/iice9to6kKe"
    "MO7cX2Pp6SYK45e7z7h4dpKy6aRKPFje5O6jhkOV8BiHa0Ezx899lbFvHPe2mB9ZkBybSnjLQvd5eZlmk2B2eqAgeeGsNzGmIKEg"
    "mUfzdTb5SoQ0CoaIXmXTBDx5VoZKsqxXZ1kdWEtJ44z3FSiTVnIq5XYtWzNpelQCj+gxZn2LaKjwFFBtXYvx9zfc13KU29bpLC8l"
    "mlvWy63NuF0RA3OHa9v8UyMzGeVWp7O8ZIAsuBbuq5JVEPUBdkRbzhC1lCqKr1pwjbYMV6eztFxCV3F/LMv9xsTbLvMgpvc4zxXu"
    "jy242uksLQNK/by6+eKvpcOHpr5z45jgnLApTAYyZIbYw1P9KYvoEvGtfPPzbnfx7mBzOqY9ZyEibK+tee8aywUrNqI9/weeui1e"
    "iOz9qQAAAABJRU5ErkJggg=="
    ),
)


def load_config():
    try:
        with open(CONFIG, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {}


def save_config(cfg):
    try:
        with open(CONFIG, "w", encoding="utf-8") as f:
            json.dump(cfg, f)
    except Exception:
        pass


def list_devices(p):
    """Ritorna ([(etichetta, info_dispositivo)], indice_predefinito).

    Il primo elemento ha info None: significa "segui l'uscita predefinita di Windows".
    """
    devices = []
    try:
        wasapi = p.get_host_api_info_by_type(pyaudio.paWASAPI)
    except Exception:
        return devices, 0
    devices.append((DEFAULT_LABEL, None))
    for lb in p.get_loopback_device_info_generator():
        devices.append(("Audio del PC - " + lb["name"].replace(" [Loopback]", ""), lb))
    for i in range(p.get_device_count()):
        d = p.get_device_info_by_index(i)
        if (d["hostApi"] == wasapi["index"] and d["maxInputChannels"] > 0
                and not d.get("isLoopbackDevice", False)):
            devices.append(("Microfono - " + d["name"], d))
    return devices, 0


class StreamResampler:
    """Ricampionamento in streaming (media su finestre frazionarie).

    Mantiene la posizione frazionaria tra un blocco e l'altro, quindi non ci sono
    salti ai bordi dei blocchi e il rapporto di campionamento resta esatto nel tempo.
    La media sulla finestra fa anche da filtro anti-aliasing.
    """

    def __init__(self, in_rate, out_rate):
        self.ratio = in_rate / float(out_rate)
        self.buf = np.zeros(0, dtype=np.float64)
        self.pos = 0.0

    def process(self, x):
        self.buf = np.concatenate((self.buf, x.astype(np.float64)))
        n_out = int((len(self.buf) - self.pos) // self.ratio)
        if n_out <= 0:
            return np.zeros(0, dtype=np.float32)
        edges = self.pos + np.arange(n_out + 1) * self.ratio
        csum = np.concatenate(([0.0], np.cumsum(self.buf)))
        ci = np.interp(edges, np.arange(len(csum)), csum)
        out = np.diff(ci) / self.ratio
        end = edges[-1]
        drop = int(end)
        self.buf = self.buf[drop:]
        self.pos = end - drop
        return out.astype(np.float32)


class Sender:
    """Cattura l'audio e lo spedisce in UDP al tablet."""

    def __init__(self):
        self.p = None
        self.stream = None
        self.sock = None
        self.q = queue.Queue(maxsize=256)
        self.thread = None
        self.running = False
        self.level = 0
        self.error = ""        # errori di rete
        self.audio_msg = ""    # stato/errori della cattura audio
        self.device = None
        self.follow_default = False
        self.current_index = None
        self.channels = 2
        self.rate = 48000
        self.resampler = None
        self.target = None

    # ---- ciclo di vita ----
    def start(self, device, ip):
        self.error = ""
        self.audio_msg = ""
        self.device = device
        self.follow_default = device is None
        self.target = (ip, PORT)
        self.q = queue.Queue(maxsize=256)
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self._open_stream()  # se fallisce, l'eccezione arriva alla finestra
        self.running = True
        self.thread = threading.Thread(target=self._send_loop, daemon=True)
        self.thread.start()

    def stop(self):
        self.running = False
        if self.thread is not None:
            self.thread.join(timeout=1.5)
        self._close_stream()
        try:
            if self.sock is not None:
                self.sock.close()
        except Exception:
            pass
        self.sock = self.thread = None
        self.level = 0
        self.audio_msg = ""

    # ---- cattura audio ----
    def _callback(self, in_data, frame_count, time_info, status):
        try:
            self.q.put_nowait(in_data)
        except queue.Full:
            pass  # meglio perdere un blocco che accumulare ritardo
        return (None, pyaudio.paContinue)

    def _open_stream(self):
        self._close_stream()
        p = pyaudio.PyAudio()
        try:
            dev = self.device if self.device is not None else p.get_default_wasapi_loopback()
            channels = max(1, int(dev["maxInputChannels"]))
            rate = int(dev["defaultSampleRate"])
            stream = p.open(
                format=pyaudio.paInt16,
                channels=channels,
                rate=rate,
                frames_per_buffer=1024,
                input=True,
                input_device_index=int(dev["index"]),
                stream_callback=self._callback,
            )
        except Exception:
            p.terminate()
            raise
        self.p = p
        self.stream = stream
        self.channels = channels
        self.rate = rate
        self.current_index = int(dev["index"])
        self.resampler = StreamResampler(rate, OUT_RATE)

    def _close_stream(self):
        try:
            if self.stream is not None:
                self.stream.stop_stream()
                self.stream.close()
        except Exception:
            pass
        try:
            if self.p is not None:
                self.p.terminate()
        except Exception:
            pass
        self.stream = None
        self.p = None

    def _default_index(self):
        p = pyaudio.PyAudio()
        try:
            return int(p.get_default_wasapi_loopback()["index"])
        except Exception:
            return None
        finally:
            p.terminate()

    def _health_check(self):
        """Riapre lo stream se si e' fermato o se l'uscita predefinita di Windows e' cambiata."""
        try:
            reopen = False
            if self.stream is None or not self.stream.is_active():
                reopen = True
            elif self.follow_default:
                idx = self._default_index()
                if idx is not None and idx != self.current_index:
                    reopen = True
            if reopen:
                self.audio_msg = "Riconnessione audio..."
                self._open_stream()
                self.audio_msg = ""
        except Exception as e:
            self.audio_msg = f"Audio non disponibile, riprovo ({e})"

    # ---- invio ----
    def _to_mono(self, data):
        a = np.frombuffer(data, dtype=np.int16)
        if self.channels > 1:
            a = a[: len(a) - len(a) % self.channels].reshape(-1, self.channels)
            return a.astype(np.float32).mean(axis=1)
        return a.astype(np.float32)

    def _send_loop(self):
        buf = np.zeros(0, dtype=np.int16)
        silence = bytes(PACKET_SAMPLES * 2)
        last_check = time.monotonic()
        while self.running:
            now = time.monotonic()
            if now - last_check >= 2.0:
                last_check = now
                self._health_check()
            try:
                data = self.q.get(timeout=0.1)
            except queue.Empty:
                # Il loopback di Windows non produce dati quando non c'e' audio:
                # mando silenzio per far sapere a Silent che sono collegato.
                self.level = 0
                self._send(silence)
                continue
            mono = self._to_mono(data)
            if len(mono) == 0 or self.resampler is None:
                continue
            out = np.clip(self.resampler.process(mono), -32768, 32767).astype(np.int16)
            buf = np.concatenate((buf, out))
            while len(buf) >= PACKET_SAMPLES:
                chunk, buf = buf[:PACKET_SAMPLES], buf[PACKET_SAMPLES:]
                rms = float(np.sqrt(np.mean(chunk.astype(np.float32) ** 2)))
                db = -100.0 if rms < 1.0 else 20.0 * np.log10(rms / 32768.0)
                self.level = int(min(100, max(0, (db + 70.0) / 70.0 * 100.0)))
                self._send(chunk.astype("<i2").tobytes())

    def _send(self, payload):
        try:
            self.sock.sendto(payload, self.target)
            self.error = ""
        except Exception as e:  # rete assente o IP errato
            self.error = str(e)


def resolve_host(text):
    """Accetta un IP o un nome di rete e restituisce l'IP, oppure None."""
    try:
        return socket.gethostbyname(text)
    except Exception:
        return None


# ---------------------------------------------------------------- grafica

def make_icon_png(size):
    """Logo di Silent (pausa arancione su fondo scuro) come PNG RGBA, senza librerie esterne."""
    ss = 4
    n = size * ss
    yy, xx = np.mgrid[0:n, 0:n]
    u = (xx + 0.5) / n * 108.0
    v = (yy + 0.5) / n * 108.0

    def rr(x1, y1, x2, y2, r):
        qx = np.abs(u - (x1 + x2) / 2) - ((x2 - x1) / 2 - r)
        qy = np.abs(v - (y1 + y2) / 2) - ((y2 - y1) / 2 - r)
        d = np.hypot(np.maximum(qx, 0), np.maximum(qy, 0)) + np.minimum(np.maximum(qx, qy), 0) - r
        return (d <= 0).astype(np.float32)

    tile = rr(2, 2, 106, 106, 24)
    bars = np.maximum(rr(33, 27, 51, 81, 4), rr(57, 27, 75, 81, 4)) * tile
    bg = np.array([0x0F, 0x14, 0x20], dtype=np.float32)
    fg = np.array([0xFF, 0x9F, 0x43], dtype=np.float32)
    rgb = bg[None, None, :] * (tile - bars)[:, :, None] + fg[None, None, :] * bars[:, :, None]
    pre = np.concatenate((rgb, (tile * 255.0)[:, :, None]), axis=2)  # colore premoltiplicato
    pre = pre.reshape(size, ss, size, ss, 4).mean(axis=(1, 3))
    a = pre[:, :, 3]
    out = np.zeros((size, size, 4), dtype=np.uint8)
    nz = a > 0
    for c in range(3):
        ch = np.zeros_like(a)
        ch[nz] = pre[:, :, c][nz] / (a[nz] / 255.0)
        out[:, :, c] = np.clip(ch, 0, 255).astype(np.uint8)
    out[:, :, 3] = np.clip(a, 0, 255).astype(np.uint8)

    raw = b"".join(b"\x00" + out[y].tobytes() for y in range(size))

    def chunk(tag, data):
        body = tag + data
        return struct.pack(">I", len(data)) + body + struct.pack(">I", zlib.crc32(body) & 0xFFFFFFFF)

    return (b"\x89PNG\r\n\x1a\n"
            + chunk(b"IHDR", struct.pack(">IIBBBBB", size, size, 8, 6, 0, 0, 0))
            + chunk(b"IDAT", zlib.compress(raw, 9))
            + chunk(b"IEND", b""))


def rrect(c, x1, y1, x2, y2, r, **kw):
    """Rettangolo con angoli arrotondati su un Canvas."""
    r = max(0, min(r, (x2 - x1) / 2.0, (y2 - y1) / 2.0))
    pts = [x1 + r, y1, x2 - r, y1, x2, y1, x2, y1 + r, x2, y2 - r, x2, y2,
           x2 - r, y2, x1 + r, y2, x1, y2, x1, y2 - r, x1, y1 + r, x1, y1]
    return c.create_polygon(pts, smooth=True, **kw)


class Card(tk.Canvas):
    """Contenitore con sfondo arrotondato (come le card dell'app Android). Usa .inner per i widget."""

    def __init__(self, parent, bg, fill, radius, pad):
        super().__init__(parent, bg=bg, highlightthickness=0, bd=0, height=10)
        self.fill, self.radius, self.pad = fill, radius, pad
        self.inner = tk.Frame(self, bg=fill)
        self.win = self.create_window(pad, pad, window=self.inner, anchor="nw")
        self.bind("<Configure>", self._on_canvas)
        self.inner.bind("<Configure>", self._on_inner)

    def _on_inner(self, event):
        h = self.inner.winfo_reqheight() + 2 * self.pad
        if int(self.cget("height")) != h:
            self.config(height=h)

    def _on_canvas(self, event):
        self.delete("bg")
        rrect(self, 0, 0, event.width, event.height, self.radius, fill=self.fill, outline="", tags="bg")
        self.tag_lower("bg")
        self.itemconfig(self.win, width=max(1, event.width - 2 * self.pad))


class RoundButton(tk.Canvas):
    """Pulsante arrotondato."""

    def __init__(self, parent, text, command, fill, fg, bg, height, font, width=None):
        kw = {"width": width} if width else {}
        super().__init__(parent, height=height, bg=bg, highlightthickness=0, bd=0,
                         cursor="hand2", **kw)
        self.text, self.command, self.fill, self.fg, self.font = text, command, fill, fg, font
        self.enabled = True
        self.bind("<Configure>", lambda e: self.redraw())
        self.bind("<Button-1>", self._click)

    def redraw(self):
        self.delete("all")
        w, h = self.winfo_width(), self.winfo_height()
        rrect(self, 0, 0, w, h, h / 2.0, fill=self.fill if self.enabled else TRACK, outline="")
        self.create_text(w / 2.0, h / 2.0, text=self.text,
                         fill=self.fg if self.enabled else GREY, font=self.font)

    def configure_button(self, text=None, fill=None, fg=None):
        if text is not None:
            self.text = text
        if fill is not None:
            self.fill = fill
        if fg is not None:
            self.fg = fg
        self.redraw()

    def set_enabled(self, enabled):
        self.enabled = enabled
        self.config(cursor="hand2" if enabled else "arrow")
        self.redraw()

    def _click(self, event):
        if self.enabled and self.command:
            self.command()


class LevelBar(tk.Canvas):
    """Barra del livello audio arrotondata."""

    def __init__(self, parent, bg, height):
        super().__init__(parent, height=height, bg=bg, highlightthickness=0, bd=0)
        self.level = 0
        self.bind("<Configure>", lambda e: self.draw())

    def set_level(self, level):
        if level != self.level:
            self.level = level
            self.draw()

    def draw(self):
        self.delete("all")
        w, h = self.winfo_width(), self.winfo_height()
        rrect(self, 0, 0, w, h, h / 2.0, fill=TRACK, outline="")
        if self.level > 0:
            fw = max(w * self.level / 100.0, h)
            rrect(self, 0, 0, fw, h, h / 2.0, fill=GREEN if self.level < 40 else ORANGE, outline="")


class StatusCircle(tk.Canvas):
    """Cerchio di stato con icona play / pausa, come nell'app Android."""

    def __init__(self, parent, bg, size):
        super().__init__(parent, width=size, height=size, bg=bg, highlightthickness=0, bd=0)
        self.size = size
        self.state = None

    def set(self, color, icon):
        if self.state == (color, icon):
            return
        self.state = (color, icon)
        self.delete("all")
        s = self.size
        self.create_oval(2, 2, s - 2, s - 2, fill=color, outline="")
        k = s * 0.49 / 24.0
        off = (s - 24 * k) / 2.0

        def p(x, y):
            return (off + x * k, off + y * k)

        if icon == "play":
            self.create_polygon(*p(8, 5), *p(8, 19), *p(19, 12), fill=WHITE, outline="")
        elif icon == "pause":
            self.create_rectangle(*p(6, 5), *p(10, 19), fill=WHITE, outline="")
            self.create_rectangle(*p(14, 5), *p(18, 19), fill=WHITE, outline="")
        else:
            self.create_text(s / 2.0, s / 2.0, text="!", fill=WHITE,
                             font=("Segoe UI", max(12, int(s * 0.16)), "bold"))


def enable_dpi_awareness():
    """Testo nitido sugli schermi con scala diversa da 100%."""
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except Exception:
            pass
    try:  # la barra delle applicazioni mostra il logo di Silent invece di quello di Python
        ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("mdovideo.silent.pcsender")
    except Exception:
        pass


def dark_title_bar(root):
    """Barra del titolo scura (Windows 10 recente / 11); se non supportata non fa nulla."""
    try:
        root.update()
        hwnd = ctypes.windll.user32.GetParent(root.winfo_id())
        for attr, val in ((20, 1), (19, 1)):
            ctypes.windll.dwmapi.DwmSetWindowAttribute(
                hwnd, attr, ctypes.byref(ctypes.c_int(val)), ctypes.sizeof(ctypes.c_int))
        color = ctypes.c_int(0x20140F)  # #0F1420 in formato BGR
        ctypes.windll.dwmapi.DwmSetWindowAttribute(hwnd, 35, ctypes.byref(color), ctypes.sizeof(color))
    except Exception:
        pass


class App:
    def __init__(self, root):
        self.root = root
        self.cfg = load_config()
        self.sender = Sender()
        self.notice = None  # (testo, colore) mostrato quando l'invio e' fermo
        self.compact = False
        self.sc = max(1.0, root.winfo_fpixels("1i") / 96.0)
        S = self.S
        root.title("Silent PC Sender")
        root.configure(bg=BG)
        root.resizable(False, False)

        # logo: icona della finestra e logo in alto
        try:
            self.icons = [tk.PhotoImage(data=d) for d in ICON_PNGS]
            root.iconphoto(True, *self.icons)
        except Exception:
            self.icons = []
        try:
            self.icon_small = tk.PhotoImage(data=base64.b64encode(make_icon_png(S(46))))
        except Exception:
            self.icon_small = None

        style = ttk.Style()
        style.theme_use("clam")
        root.option_add("*TCombobox*Listbox.background", TRACK)
        root.option_add("*TCombobox*Listbox.foreground", WHITE)
        root.option_add("*TCombobox*Listbox.selectBackground", ORANGE)
        root.option_add("*TCombobox*Listbox.selectForeground", BG)
        root.option_add("*TCombobox*Listbox.font", ("Segoe UI", 10))
        style.configure("Silent.TCombobox", fieldbackground=TRACK, background=TRACK,
                        foreground=WHITE, arrowcolor=WHITE, bordercolor=TRACK,
                        lightcolor=TRACK, darkcolor=TRACK, selectbackground=TRACK,
                        selectforeground=WHITE, padding=S(6))
        style.map("Silent.TCombobox",
                  fieldbackground=[("readonly", TRACK), ("disabled", CARD)],
                  foreground=[("readonly", WHITE), ("disabled", GREY)],
                  selectbackground=[("readonly", TRACK)],
                  selectforeground=[("readonly", WHITE)],
                  background=[("active", TRACK), ("readonly", TRACK)],
                  arrowcolor=[("disabled", GREY)])

        outer = tk.Frame(root, bg=BG)
        outer.pack(fill="both", expand=True, padx=S(22), pady=S(12))

        # il pulsante si impacchetta per primo, in basso: resta sempre visibile
        self.btn = RoundButton(outer, "Avvia invio", self.toggle, ORANGE, BG, BG, S(48),
                               ("Segoe UI", 13, "bold"))
        self.btn.pack(side="bottom", fill="x", pady=(S(12), 0))

        self.head = tk.Frame(outer, bg=BG)
        self.head.pack()
        if self.icon_small is not None:
            tk.Label(self.head, image=self.icon_small, bg=BG).pack()
        tk.Label(self.head, text="Silent PC", bg=BG, fg=WHITE,
                 font=("Segoe UI", 20, "bold")).pack()
        tk.Label(self.head, text="Il video va solo quando c'è silenzio", bg=BG, fg=GREY,
                 font=("Segoe UI", 10)).pack()

        self.circle = StatusCircle(outer, BG, S(104))
        self.circle.pack(pady=(S(10), S(6)))
        self.status = tk.Label(outer, text="Fermo", bg=BG, fg=WHITE, height=2,
                               font=("Segoe UI", 12, "bold"), wraplength=S(400), justify="center")
        self.status.pack()
        self.input_lbl = tk.Label(outer, text="Ingresso: -", bg=BG, fg=GREY, font=("Segoe UI", 9))
        self.input_lbl.pack(pady=(0, S(6)))

        self.bar = LevelBar(outer, BG, S(24))
        self.bar.pack(fill="x")

        card = Card(outer, BG, CARD, S(18), S(14))
        card.pack(fill="x", pady=(S(12), 0))
        self.card = card
        c = card.inner

        tk.Label(c, text="IP del tablet (lo vedi nell'app Silent)", bg=CARD, fg=WHITE,
                 font=("Segoe UI", 10)).pack(anchor="w")
        self.ip_var = tk.StringVar(value=self.cfg.get("ip", ""))
        self.ip_entry = tk.Entry(c, textvariable=self.ip_var, bg=TRACK, fg=WHITE,
                                 insertbackground=WHITE, relief="flat",
                                 disabledbackground=TRACK, disabledforeground=GREY,
                                 highlightthickness=S(1), highlightbackground=TRACK,
                                 highlightcolor=ORANGE, font=("Segoe UI", 12))
        self.ip_entry.pack(fill="x", pady=(S(4), S(8)), ipady=S(5))

        row = tk.Frame(c, bg=CARD)
        row.pack(fill="x")
        tk.Label(row, text="Audio da inviare", bg=CARD, fg=WHITE,
                 font=("Segoe UI", 10)).pack(side="left")
        self.refresh_btn = RoundButton(row, "Aggiorna", self.refresh_devices, TRACK, WHITE, CARD,
                                       S(28), ("Segoe UI", 9), width=S(84))
        self.refresh_btn.pack(side="right")

        self.devices = []
        self.combo = ttk.Combobox(c, state="readonly", style="Silent.TCombobox",
                                  font=("Segoe UI", 10))
        self.combo.pack(fill="x", pady=(S(6), S(8)))

        self.autostart_var = tk.BooleanVar(value=bool(self.cfg.get("autostart", False)))
        tk.Checkbutton(c, text="Avvia l'invio all'apertura", variable=self.autostart_var,
                       bg=CARD, fg=WHITE, selectcolor=TRACK, activebackground=CARD,
                       activeforeground=WHITE, font=("Segoe UI", 10), highlightthickness=0,
                       bd=0).pack(anchor="w")

        if pyaudio is None:
            self.notice = ("Manca pyaudiowpatch: pip install pyaudiowpatch numpy", ORANGE)
            self.btn.set_enabled(False)
            self.refresh_btn.set_enabled(False)
        else:
            self.refresh_devices()

        root.protocol("WM_DELETE_WINDOW", self.close)
        dark_title_bar(root)
        self.fit()
        root.after(120, self.fit)
        root.after(500, self.fit)
        self.tick()

        if (pyaudio is not None and self.autostart_var.get()
                and self.ip_var.get().strip() and self.devices):
            root.after(700, self.toggle)

    def S(self, v):
        return int(round(v * self.sc))

    def work_area(self):
        """Area dello schermo non coperta dalla barra delle applicazioni: (x, y, larghezza, altezza)."""
        try:
            r = ctypes.wintypes.RECT()
            ctypes.windll.user32.SystemParametersInfoW(0x0030, 0, ctypes.byref(r), 0)
            return r.left, r.top, r.right - r.left, r.bottom - r.top
        except Exception:
            return 0, 0, self.root.winfo_screenwidth(), self.root.winfo_screenheight() - self.S(60)

    def fit(self):
        """Dimensiona la finestra sul contenuto e la tiene dentro lo schermo: niente pulsanti tagliati."""
        r = self.root
        self.card.config(height=self.card.inner.winfo_reqheight() + 2 * self.card.pad)
        r.update_idletasks()
        x0, y0, aw, ah = self.work_area()
        avail = ah - self.S(40)  # margine per la barra del titolo e i bordi
        if r.winfo_reqheight() > avail and not self.compact:
            self.compact = True  # schermo basso: nascondo logo e sottotitolo
            self.head.pack_forget()
            self.input_lbl.pack_forget()
            self.card.config(height=self.card.inner.winfo_reqheight() + 2 * self.card.pad)
            r.update_idletasks()
        w = self.S(470)
        h = min(r.winfo_reqheight(), avail)
        x = x0 + max(0, (aw - w) // 2)
        y = y0 + max(0, (ah - h) // 2 - self.S(20))
        r.geometry(f"{w}x{h}+{x}+{y}")

    def refresh_devices(self):
        if pyaudio is None:
            return
        keep = self.combo.get() or self.cfg.get("device")
        p = pyaudio.PyAudio()
        try:
            self.devices, default_idx = list_devices(p)
        finally:
            p.terminate()
        names = [d[0] for d in self.devices]
        self.combo["values"] = names
        if keep in names:
            self.combo.current(names.index(keep))
        elif names:
            self.combo.current(default_idx)
        else:
            self.combo.set("")

    def set_locked(self, locked):
        self.ip_entry.config(state="disabled" if locked else "normal")
        self.refresh_btn.set_enabled(not locked)
        self.combo.config(state="disabled" if locked else "readonly")

    def toggle(self):
        if self.sender.running:
            self.sender.stop()
            self.set_locked(False)
            self.btn.configure_button(text="Avvia invio", fill=ORANGE)
            self.notice = None
            return
        text = self.ip_var.get().strip()
        if not text:
            self.notice = ("Inserisci l'IP del tablet", ORANGE)
            return
        ip = resolve_host(text)
        if ip is None:
            self.notice = (f"Indirizzo non valido: {text}", ORANGE)
            return
        sel = self.combo.current()
        if sel < 0:
            self.notice = ("Nessun dispositivo audio", ORANGE)
            return
        try:
            self.sender.start(self.devices[sel][1], ip)
        except Exception as e:
            self.sender.stop()
            self.notice = (f"Errore: {e}", ORANGE)
            return
        self.notice = None
        self.cfg.update({"ip": text, "device": self.devices[sel][0]})
        self.cfg["autostart"] = bool(self.autostart_var.get())
        save_config(self.cfg)
        self.set_locked(True)
        self.btn.configure_button(text="Ferma invio", fill=TRACK, fg=WHITE)

    def tick(self):
        s = self.sender
        if s.running:
            self.bar.set_level(s.level)
            if s.error:
                color, icon, text, fg = ORANGE, "alert", f"Errore rete: {s.error}", ORANGE
            elif s.audio_msg:
                color, icon, text, fg = ORANGE, "alert", s.audio_msg, ORANGE
            elif s.level > 0:
                color, icon, text, fg = ORANGE, "pause", "Audio rilevato: il tablet mette in pausa", WHITE
            else:
                color, icon, text, fg = GREEN, "play", "Silenzio: il video può andare", WHITE
            label = self.combo.get()
            inp = "Ingresso: " + (label if len(label) <= 58 else label[:55] + "...")
        else:
            self.bar.set_level(0)
            color, icon, inp = GREY, "play", "Ingresso: -"
            if self.notice:
                text, fg = self.notice
            else:
                text, fg = "Fermo", WHITE
        self.circle.set(color, icon)
        if self.status.cget("text") != text or self.status.cget("fg") != fg:
            self.status.config(text=text, fg=fg)
        if self.input_lbl.cget("text") != inp:
            self.input_lbl.config(text=inp)
        self.root.after(80, self.tick)

    def close(self):
        self.cfg["autostart"] = bool(self.autostart_var.get())
        save_config(self.cfg)
        self.sender.stop()
        self.root.destroy()


if __name__ == "__main__":
    enable_dpi_awareness()
    root = tk.Tk()
    App(root)
    root.mainloop()
