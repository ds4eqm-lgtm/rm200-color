#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
RM200 측색계 (Pantone CAPSURE / X-Rite RM200 용, 한국어 안전판)
원본: slowsky-netizen/Rm200 (MIT), 기계 통신: raburton/rm200lib (AGPL-3.0)

탭: 측정 비교 / 내 팔레트 / 기계 정보 / 기계 안 파일(읽기) / 견본 책 /
    교정 / 기계 화면 / 실시간 미리보기
기계를 망가뜨릴 수 있는 쓰기·지우기 명령은 rm200_safe 에서 막습니다.
"""

import argparse
import datetime as dt
import json
import math
import os
import struct
import sys
import threading
import time
import tkinter as tk
from tkinter import ttk, messagebox, filedialog, simpledialog

import rm200_safe as rm
import rm200_sync as cloud
import rm200_update as upd
import xrite_sync as xs
rm.confirm = lambda t, x: messagebox.askyesno(t, x)

APP_VERSION = os.environ.get('RM200_APP_VERSION', '0.1')

try:
    from PIL import Image, ImageTk, ImageCms
    HAS_PIL = True
except ImportError:
    HAS_PIL = False


# ==========================================================================
#  ПАРАМЕТРЫ
# ==========================================================================

RECORD_SIZE     = 0x5158
HEADER_SIZE     = 0x0
VALID_ID        = 0x21B76F30

USB_RETRIES     = 5
USB_DELAY       = 2.0
POST_MEAS_PAUSE = 2.0
POLL_INTERVAL   = 1.0

MAX_AGE_SECONDS = 300

REBOOT_TIMEOUT  = 5.0
RECONNECT_MAX   = 15
RECONNECT_DELAY = 2.0

DEFAULT_UNLOCK_PASSWORD = '873gwe31xah1'

PALETTES_FILE = os.environ.get('RM200_PALETTES') or os.path.join(
    os.path.dirname(os.path.abspath(__file__)), 'palettes.json'
)

PSEUDO_CMYK = 'CMYK (기본 내장)'

AP_LABELS = ['0  작게 2mm', '1  중간 4mm', '2  크게 8mm·자동']


# ==========================================================================
#  БЕЗОПАСНЫЕ ВЫЗОВЫ
# ==========================================================================

USB_ERROR_HINTS = (
    'usb', 'device', 'timeout', 'broken', 'pipe',
    'disconnected', 'reset', 'libusb', 'input/output',
)


def _is_usb_error(exc):
    msg = str(exc).lower()
    return any(h in msg for h in USB_ERROR_HINTS)


def safe_command(func, *args, retries=USB_RETRIES, delay=USB_DELAY, **kwargs):
    last_exc = None
    for attempt in range(1, retries + 1):
        try:
            return func(*args, **kwargs)
        except Exception as e:
            last_exc = e
            if not _is_usb_error(e):
                raise
            try:
                rm.Disconnect()
            except Exception:
                pass
            time.sleep(delay)
            try:
                rm.Connect()
            except Exception:
                time.sleep(delay)
    raise RuntimeError(f"{retries}번 시도했지만 명령이 실행되지 않았습니다: {last_exc}")


def try_call(func, *args, **kwargs):
    if func is None:
        return False, RuntimeError("이 기능은 지원하지 않습니다")
    try:
        return True, func(*args, **kwargs)
    except Exception as e:
        return False, e


def _call_with_timeout(func, timeout, *args, **kwargs):
    result = {'ok': False, 'exc': None}

    def target():
        try:
            func(*args, **kwargs)
            result['ok'] = True
        except Exception as e:
            result['exc'] = e

    t = threading.Thread(target=target, daemon=True)
    t.start()
    t.join(timeout)
    if t.is_alive():
        return False, TimeoutError("timeout")
    return result['ok'], result['exc']


# ==========================================================================
#  ПАРСЕР MeasDataV05.dat
# ==========================================================================

def _u16(b, o): return struct.unpack_from('<H', b, o)[0]
def _u32(b, o): return struct.unpack_from('<I', b, o)[0]
def _f32(b, o): return struct.unpack_from('<f', b, o)[0]


def _str_utf16(b, o, max_len):
    end = o
    lim = min(o + max_len, len(b))
    while end + 1 < lim:
        if b[end] == 0 and b[end + 1] == 0:
            break
        end += 2
    return b[o:end].decode('utf-16-le', errors='replace')


def _str_ascii(b, o, max_len):
    end = o
    lim = min(o + max_len, len(b))
    while end < lim and b[end] != 0:
        end += 1
    return b[o:end].decode('ascii', errors='replace')


def _datetime_valid(rec):
    try:
        year   = _u16(rec, 0x08)
        month  = rec[0x0A]
        day    = rec[0x0B]
        hour   = rec[0x0C]
        minute = rec[0x0D]
        second = rec[0x0E]
    except Exception:
        return False
    return (2000 <= year <= 2100 and 1 <= month <= 12 and 1 <= day <= 31
            and hour <= 23 and minute <= 59 and second <= 59)


def _parse_record(rec):
    return {
        'datetime':   (f"{_u16(rec, 0x08):04d}-"
                       f"{rec[0x0A]:02d}-{rec[0x0B]:02d} "
                       f"{rec[0x0C]:02d}:{rec[0x0D]:02d}:{rec[0x0E]:02d}"),
        'id':         _u32(rec, 0x0010),
        'counter':    _u32(rec, 0x0014),
        'name':       _str_utf16(rec, 0x00A4, 0x3C).strip(),
        'fandeck':    _str_ascii(rec, 0x00E0, 0x28).strip(),
        'sample_lab': (_f32(rec, 0x01DC),
                       _f32(rec, 0x01E0),
                       _f32(rec, 0x01E4)),
        'sample_xyz': (_f32(rec, 0x01E8),
                       _f32(rec, 0x01EC),
                       _f32(rec, 0x01F0)),
    }


def parse_measdata(data):
    n = len(data)
    if n < RECORD_SIZE:
        return []
    records = []
    pos = HEADER_SIZE
    while pos + RECORD_SIZE <= n:
        rec = data[pos:pos + RECORD_SIZE]
        if _datetime_valid(rec):
            try:
                r = _parse_record(rec)
                r['offset'] = pos
                records.append(r)
            except struct.error:
                pass
        pos += RECORD_SIZE
    return records


# ---- Ver 0.18: 기계 화면(176x220, RGB565)에서 주황 경고 창 찾기 ----
LCD_W, LCD_H = 176, 220


def lcd_pixels(body):
    px = []
    for i in range(0, LCD_W * LCD_H * 2, 2):
        v = body[i] | (body[i + 1] << 8)
        px.append((((v >> 11) & 31) * 255 // 31, ((v >> 5) & 63) * 255 // 63, (v & 31) * 255 // 31))
    return px


def lcd_image(body):
    im = Image.new('RGB', (LCD_W, LCD_H))
    im.putdata(lcd_pixels(body))
    return im


def lcd_has_alert(body):
    """경고·오류 창: 화면 너비 거의 가득한 주황 띠(6~60줄) + 어두운 본문."""
    if not body or len(body) < LCD_W * LCD_H * 2:
        return False
    px = lcd_pixels(body)
    band = best = dark = 0
    for y in range(LCD_H):
        row = px[y * LCD_W:(y + 1) * LCD_W]
        org = sum(1 for r, g, b in row if r > 200 and 60 < g < 190 and b < 90)
        if org >= LCD_W * 0.7:
            band += 1
            best = max(best, band)
        else:
            band = 0
        if sum(r + g + b for r, g, b in row) / (3 * LCD_W) < 90:
            dark += 1
    return 6 <= best <= 60 and dark >= 15


def newest_record(records):
    if not records:
        return None
    return sorted(records, key=lambda r: (r['datetime'], r['counter']))[-1]


def record_age_seconds(rec):
    try:
        t = dt.datetime.strptime(rec['datetime'], "%Y-%m-%d %H:%M:%S")
        return (dt.datetime.now() - t).total_seconds()
    except Exception:
        return None


def format_age(sec):
    if sec is None:
        return "?"
    if sec < 60:
        return f"{int(sec)}초 전"
    if sec < 3600:
        return f"{int(sec / 60)}분 전"
    return f"{sec / 3600:.1f}시간 전"


# ==========================================================================
#  ЦВЕТОВЫЕ ПРЕОБРАЗОВАНИЯ
# ==========================================================================

def lab_to_rgb(L, a, b):
    fy = (L + 16) / 116
    fx = a / 500 + fy
    fz = fy - b / 200

    def f_inv(t):
        return t ** 3 if t > 6 / 29 else 3 * (6 / 29) ** 2 * (t - 4 / 29)

    X = 0.95047 * f_inv(fx)
    Y = 1.00000 * f_inv(fy)
    Z = 1.08883 * f_inv(fz)

    r  =  3.2406 * X - 1.5372 * Y - 0.4986 * Z
    g  = -0.9689 * X + 1.8758 * Y + 0.0415 * Z
    b_ =  0.0557 * X - 0.2040 * Y + 1.0570 * Z

    def gamma(c):
        c = max(0.0, min(1.0, c))
        return 12.92 * c if c <= 0.0031308 else 1.055 * c ** (1 / 2.4) - 0.055

    return (int(round(gamma(r)  * 255)),
            int(round(gamma(g)  * 255)),
            int(round(gamma(b_) * 255)))


def de2000(l1, a1, b1, l2, a2, b2):
    C1 = math.hypot(a1, b1); C2 = math.hypot(a2, b2); Cb = (C1 + C2) / 2
    G = 0.5 * (1 - math.sqrt(Cb ** 7 / (Cb ** 7 + 25 ** 7)))
    a1p = (1 + G) * a1; a2p = (1 + G) * a2
    C1p = math.hypot(a1p, b1); C2p = math.hypot(a2p, b2)
    h1 = math.degrees(math.atan2(b1, a1p)) % 360 if C1p else 0.0
    h2 = math.degrees(math.atan2(b2, a2p)) % 360 if C2p else 0.0
    dL = l2 - l1; dC = C2p - C1p
    dh = h2 - h1
    if C1p * C2p == 0:
        dh = 0
    elif dh > 180:
        dh -= 360
    elif dh < -180:
        dh += 360
    dH = 2 * math.sqrt(C1p * C2p) * math.sin(math.radians(dh / 2))
    Lb = (l1 + l2) / 2; Cbp = (C1p + C2p) / 2
    if C1p * C2p == 0:
        hb = h1 + h2
    elif abs(h1 - h2) <= 180:
        hb = (h1 + h2) / 2
    else:
        hb = (h1 + h2 + 360) / 2 if h1 + h2 < 360 else (h1 + h2 - 360) / 2
    T = (1 - 0.17 * math.cos(math.radians(hb - 30)) + 0.24 * math.cos(math.radians(2 * hb))
         + 0.32 * math.cos(math.radians(3 * hb + 6)) - 0.20 * math.cos(math.radians(4 * hb - 63)))
    SL = 1 + 0.015 * (Lb - 50) ** 2 / math.sqrt(20 + (Lb - 50) ** 2)
    SC = 1 + 0.045 * Cbp; SH = 1 + 0.015 * Cbp * T
    dt_ = 30 * math.exp(-((hb - 275) / 25) ** 2)
    RC = 2 * math.sqrt(Cbp ** 7 / (Cbp ** 7 + 25 ** 7)); RT = -math.sin(math.radians(2 * dt_)) * RC
    return math.sqrt((dL / SL) ** 2 + (dC / SC) ** 2 + (dH / SH) ** 2 + RT * (dC / SC) * (dH / SH))


_PANTONE = None


def pantone_decks():
    """엑스라이트 서버의 공식 팬톤 팬덱(pantone_fandecks.json)을 읽음."""
    global _PANTONE
    if _PANTONE is None:
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'pantone_fandecks.json')
        try:
            with open(path, encoding='utf-8') as f:
                _PANTONE = json.load(f)['decks']
        except Exception:
            _PANTONE = []
        try:
            upath = os.path.join(os.path.dirname(PALETTES_FILE), 'pantone_update.json')
            with open(upath, encoding='utf-8') as f:
                for nd in json.load(f).get('decks', []):
                    for i, d in enumerate(_PANTONE):
                        if d['sku'] == nd['sku']:
                            _PANTONE[i] = nd
                            break
                    else:
                        _PANTONE.append(nd)
        except Exception:
            pass
    return _PANTONE


PANTONE_PREFIX = '팬톤: '


def srgb_to_lab(r, g, b):
    """sRGB 0..255 -> CIE Lab (D65)."""
    def srgb_to_linear(c):
        c = c / 255.0
        return c / 12.92 if c <= 0.04045 else ((c + 0.055) / 1.055) ** 2.4

    rl = srgb_to_linear(r)
    gl = srgb_to_linear(g)
    bl = srgb_to_linear(b)

    X = rl * 0.4124 + gl * 0.3576 + bl * 0.1805
    Y = rl * 0.2126 + gl * 0.7152 + bl * 0.0722
    Z = rl * 0.0193 + gl * 0.1192 + bl * 0.9505

    Xn, Yn, Zn = 0.95047, 1.00000, 1.08883

    def f(t):
        return t ** (1 / 3) if t > (6 / 29) ** 3 else t / (3 * (6 / 29) ** 2) + 4 / 29

    fx = f(X / Xn)
    fy = f(Y / Yn)
    fz = f(Z / Zn)

    L = 116 * fy - 16
    a = 500 * (fx - fy)
    b_ = 200 * (fy - fz)
    return (L, a, b_)


def cmyk_to_lab(c, m, y, k):
    """
    단순 CMYK -> Lab 변환: 프린터 ICC 프로필이 없으면 대략값입니다.
    c,m,y,k 는 0..100.
    """
    c = c / 100.0
    m = m / 100.0
    y = y / 100.0
    k = k / 100.0
    r = 255.0 * (1 - c) * (1 - k)
    g = 255.0 * (1 - m) * (1 - k)
    b = 255.0 * (1 - y) * (1 - k)
    return srgb_to_lab(r, g, b)


def lab_to_cmyk_heuristic(L, a, b):
    C = 50.0 - 0.5 * a - 0.3 * b
    M = 50.0 + 0.6 * a
    Y = 50.0 + 0.6 * b
    K = max(0.0, 100.0 - L)
    return (C, M, Y, K)


def lab_to_cmyk_icc(L, a, b, icc_path):
    if not HAS_PIL:
        raise RuntimeError("Pillow(그림 부품)가 없습니다")
    Lp = int(round(max(0, min(100, L)) * 255 / 100))
    ap = int(round(max(0, min(255, a + 128))))
    bp = int(round(max(0, min(255, b + 128))))
    img = Image.new("LAB", (1, 1), (Lp, ap, bp))
    lab_p  = ImageCms.createProfile("LAB")
    cmyk_p = ImageCms.getOpenProfile(icc_path)
    tr = ImageCms.buildTransform(lab_p, cmyk_p, "LAB", "CMYK",
                                 renderingIntent=ImageCms.Intent.PERCEPTUAL)
    c, m, y, k = ImageCms.applyTransform(img, tr).getpixel((0, 0))
    return (c / 2.55, m / 2.55, y / 2.55, k / 2.55)


# ==========================================================================
#  СРАВНЕНИЕ: CMYK и палитра
# ==========================================================================

def format_correction(dc, dm, dy, dk, thr=1.0):
    parts = []

    def add(name, val):
        if abs(val) < thr:
            parts.append(f"{name} 그대로")
        elif val > 0:
            parts.append(f"{name} {abs(val):.0f}% 더")
        else:
            parts.append(f"{name} {abs(val):.0f}% 덜")

    add("Cyan", dc)
    add("Magenta", dm)
    add("Yellow", dy)
    add("Black", dk)
    return "보정: " + ", ".join(parts) + "."


def format_result_cmyk(ref_lab, sample_lab, icc_path=None, threshold=1.0):
    Lr, ar, br = ref_lab
    Ls, as_, bs = sample_lab
    dL, da, db = Lr - Ls, ar - as_, br - bs
    dE = (dL ** 2 + da ** 2 + db ** 2) ** 0.5

    lines = []
    lines.append(f"기준색:   L*={Lr:8.3f}  a*={ar:8.3f}  b*={br:8.3f}")
    lines.append(f"비교색:   L*={Ls:8.3f}  a*={as_:8.3f}  b*={bs:8.3f}")
    lines.append(f"ΔL*={dL:+.3f}  Δa*={da:+.3f}  Δb*={db:+.3f}  ΔE76={dE:.3f}")
    lines.append("")

    if icc_path:
        try:
            Cr, Mr, Yr, Kr = lab_to_cmyk_icc(Lr, ar, br, icc_path)
            Cs, Ms, Ys, Ks = lab_to_cmyk_icc(Ls, as_, bs, icc_path)
            lines.append("ICC 프로필로 계산했습니다.")
        except Exception as e:
            lines.append(f"ICC 오류: {e}. 어림 계산으로 바꿉니다.")
            Cr, Mr, Yr, Kr = lab_to_cmyk_heuristic(Lr, ar, br)
            Cs, Ms, Ys, Ks = lab_to_cmyk_heuristic(Ls, as_, bs)
    else:
        Cr, Mr, Yr, Kr = lab_to_cmyk_heuristic(Lr, ar, br)
        Cs, Ms, Ys, Ks = lab_to_cmyk_heuristic(Ls, as_, bs)
        lines.append("어림 계산입니다(ICC 프로필 없음).")

    dc, dm, dy, dk = Cr - Cs, Mr - Ms, Yr - Ys, Kr - Ks

    lines.append(f"기준색 CMYK: C={Cr:6.2f} M={Mr:6.2f} Y={Yr:6.2f} K={Kr:6.2f}")
    lines.append(f"비교색 CMYK: C={Cs:6.2f} M={Ms:6.2f} Y={Ys:6.2f} K={Ks:6.2f}")
    lines.append(f"ΔCMYK:       ΔC={dc:+6.2f} ΔM={dm:+6.2f} ΔY={dy:+6.2f} ΔK={dk:+6.2f}")
    lines.append("")
    lines.append(format_correction(dc, dm, dy, dk, threshold))
    return "\n".join(lines)


def propose_palette_mix(target_lab, entries, n_max):
    """
    (색, 비율) 목록을 돌려준다: 기준색에 가까워지도록
    팔레트에서 가장 가까운 N 개 색을 섞는 제안.
    """
    if not entries:
        return []

    dists = []
    for e in entries:
        L, a, b = e['lab']
        d = math.sqrt((L - target_lab[0]) ** 2 +
                      (a - target_lab[1]) ** 2 +
                      (b - target_lab[2]) ** 2)
        dists.append((d, e))
    dists.sort(key=lambda x: x[0])

    top = dists[:max(1, n_max)]
    if len(top) == 1:
        return [(top[0][1], 100.0)]

    eps = 0.5
    weights = [1.0 / ((d + eps) ** 2) for d, _ in top]
    total = sum(weights)
    probs = [w / total * 100.0 for w in weights]

    # отбрасываем доли меньше 0.1%, перераспределяем
    probs = [p if p >= 0.1 else 0.0 for p in probs]
    s = sum(probs)
    if s <= 0:
        probs = [100.0 / len(top)] * len(top)
    else:
        probs = [p / s * 100.0 for p in probs]

    result = []
    for (d, e), p in zip(top, probs):
        if p > 0:
            result.append((e, p))
    return result


def format_result_palette(ref_lab, sample_lab, palette_name, mix):
    Lr, ar, br = ref_lab
    Ls, as_, bs = sample_lab
    dE = math.sqrt((Lr - Ls) ** 2 + (ar - as_) ** 2 + (br - bs) ** 2)

    lines = []
    lines.append(f"팔레트:  {palette_name}")
    lines.append(f"기준색:   L*={Lr:8.3f}  a*={ar:8.3f}  b*={br:8.3f}")
    lines.append(f"비교색:   L*={Ls:8.3f}  a*={as_:8.3f}  b*={bs:8.3f}  "
                 f"ΔE(기준-비교)={dE:.3f}")
    lines.append("")

    if not mix:
        lines.append("섞을 색을 찾지 못했습니다(자료 없음).")
        return "\n".join(lines)

    # проверим, насколько микс близок к эталону
    Lm = sum(e['lab'][0] * p / 100.0 for e, p in mix)
    am = sum(e['lab'][1] * p / 100.0 for e, p in mix)
    bm = sum(e['lab'][2] * p / 100.0 for e, p in mix)
    dEm = math.sqrt((Lr - Lm) ** 2 + (ar - am) ** 2 + (br - bm) ** 2)

    lines.append(f"기준색에 가까워지는 섞기 제안:")
    for e, p in mix:
        L, a, b = e['lab']
        lines.append(f"  {p:6.2f}%  {e['name']:24}  "
                     f"(L={L:7.3f} a={a:7.3f} b={b:7.3f})")
    lines.append("")
    lines.append(f"섞은 결과 색: L*={Lm:.3f} a*={am:.3f} b*={bm:.3f}")
    lines.append(f"ΔE 섞은 색 ↔ 기준색: {dEm:.3f}")
    return "\n".join(lines)


# ==========================================================================
#  ГЛАВНОЕ ОКНО
# ==========================================================================

class AdvisorApp(tk.Tk):

    def __init__(self, aperture=2, icc=None, timeout=25.0, threshold=1.0,
                 reboot_after=False, reconnect_after=False):
        super().__init__()
        self.title(f"RM200 측색계 Ver {APP_VERSION}  (Pantone CAPSURE)")
        self.geometry("1220x920")
        self.minsize(1000, 720)

        self.aperture        = aperture
        self.icc             = icc
        self.timeout         = timeout
        self.threshold       = threshold
        self.reboot_after    = reboot_after
        self.reconnect_after = reconnect_after

        self.connected = False
        self.busy      = False

        self.device_info = {'fw': None, 'sn': None, 'count': None,
                            'dev_time': None}

        self.state_data = {
            'ref': {'title': '기준색',  'measurements': []},
            'smp': {'title': '비교색', 'measurements': []},
        }
        self.widgets = {'ref': {}, 'smp': {}}

        # Палитры:  name -> {'entries': [{'name': str, 'lab': (L,a,b)}, ...]}
        self.palettes = {}
        self._load_palettes()

        # Live preview
        self.preview_running = False
        self.preview_after_id = None

        self._build_menu()
        self._build_ui()
        self.protocol("WM_DELETE_WINDOW", self._on_close)
        self.after(100, self._connect_async)
        self.after(1500, self._cloud_start)          # Ver 0.26 공용 저장소
        self.after(6000, self._upd_start)            # Ver 0.26 깃허브 새 판
        self.after(2500, self._install_first_ask)    # Ver 0.26 처음 PC면 설치 묻기
        if getattr(self, '_pal_load_error', None):
            self.after(500, lambda: messagebox.showwarning("내 팔레트", self._pal_load_error))

    # ----------------------------------------------------------------- Палитры (load/save)

    def _load_palettes(self):
        self.palettes = {}
        if os.path.exists(PALETTES_FILE):
            try:
                with open(PALETTES_FILE, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                for p in data.get('palettes', []):
                    name = p.get('name', 'Unnamed')
                    ents = []
                    for e in p.get('entries', []):
                        lab = e.get('lab', [0, 0, 0])
                        ents.append({
                            'name': e.get('name', 'Color'),
                            'lab': (float(lab[0]), float(lab[1]), float(lab[2])),
                        })
                    self.palettes[name] = {'entries': ents}
            except Exception as e:
                # 파일이 깨졌으면 덮어쓰기 전에 따로 보관
                import shutil
                keep = PALETTES_FILE + dt.datetime.now().strftime(".손상_%Y%m%d_%H%M%S.json")
                try:
                    shutil.copy2(PALETTES_FILE, keep)
                except Exception:
                    keep = "(보관 실패)"
                self.palettes = {}
                self._pal_load_error = f"팔레트 파일을 읽지 못했습니다: {e}\n원래 파일은 {keep} 로 보관했습니다."

    def _save_palettes(self):
        try:
            data = {'palettes': [
                {
                    'name': n,
                    'entries': [
                        {'name': e['name'], 'lab': list(e['lab'])}
                        for e in p['entries']
                    ],
                }
                for n, p in self.palettes.items()
            ]}
            tmp = PALETTES_FILE + ".tmp"
            with open(tmp, 'w', encoding='utf-8') as f:
                json.dump(data, f, indent=2, ensure_ascii=False)
            if os.path.exists(PALETTES_FILE):
                try:
                    os.replace(PALETTES_FILE, PALETTES_FILE + ".bak")
                except Exception:
                    pass
            os.replace(tmp, PALETTES_FILE)
            self._cloud_kick()
        except Exception as e:
            messagebox.showerror("내 팔레트", f"팔레트를 저장하지 못했습니다:\n{e}")

    def _palette_names_for_compare(self):
        return ([PSEUDO_CMYK] + list(self.palettes.keys())
                + [PANTONE_PREFIX + d['ko'] for d in pantone_decks()])

    def _palette_by_name(self, name):
        if name and name.startswith(PANTONE_PREFIX):
            ko = name[len(PANTONE_PREFIX):]
            for d in pantone_decks():
                if d['ko'] == ko:
                    return {'entries': [{'name': c[0], 'lab': (c[1], c[2], c[3])} for c in d['colors']]}
            return None
        return self.palettes.get(name)

    # ----------------------------------------------------------------- Меню

    # ---- Ver 0.11: 큰 글씨 메뉴 줄(파일·기계·도구·도움말). 고른 메뉴는 파란 바탕 ----
    MENU_FONT = ('맑은 고딕', 12, 'bold')
    ITEM_FONT = ('맑은 고딕', 12)

    def _build_menu(self):
        self._menus = [
            ("파일", [("측정 기록 파일(MeasDataV05.dat) 저장...", self._menu_save_dump), None,
                      ("팔레트 모두 내보내기(JSON)...", self._on_palette_export_all),
                      ("팔레트 가져오기(JSON)...", self._on_palette_import_all), None,
                      ("바탕화면·시작 메뉴 바로가기 (설치 선택)", lambda: self._install_dialog()), None,
                      ("끝내기", self._on_close)]),
            ("기계", [("연결", self._connect_async), ("다시 연결", self._menu_reconnect),
                      ("기계 다시 켜기(재부팅)", self._menu_reboot),
                      ("USB 다시 연결 (뽑았다 꽂은 것처럼)", lambda: self._usb_reset()),
                      ("USB 드라이버 바꾸기 (새 PC에서 한 번)", lambda: self._driver_offer(force=True)), None,
                      ("기계 정보", lambda: self._notebook.select(3))]),
            ("도구", [("기계 화면 사진 저장...", self._menu_screenshot),
                      ("온도 읽기", self._menu_temperature),
                      ("실시간 화면", lambda: self._notebook.select(8)),
                      ("기계 원격 단추 (PC에서 기계 단추 누르기)", lambda: self._open_remote()), None,
                      ("팬톤 색 보기", lambda: self._notebook.select(2)),
                      ("인터넷 표준 시각과 동기화", self._on_sync_time),
                      ("새 판 확인 (깃허브)", lambda: self._upd_check(manual=True)),
                      ("이름 바꾸기 되돌리기", lambda: self._rename_undo()),
                      ("엑스라이트 서버 업데이트 확인", lambda: self._xs_check(manual=True))]),
            ("도움말", [(f"사용설명서 (Ver {APP_VERSION})", self._menu_manual),
                        ("프로그램 정보", self._menu_about)]),
        ]
        self._menubar = tk.Frame(self, bg='#e9edf3')
        self._menubar.pack(fill=tk.X, side=tk.TOP)
        self._menu_lbls = []
        for title, items in self._menus:
            lb = tk.Label(self._menubar, text=title, font=self.MENU_FONT, bg='#e9edf3', fg='#222',
                          padx=18, pady=6, cursor='hand2')
            lb.pack(side=tk.LEFT)
            lb.bind('<Button-1>', lambda e, t=title: self._menu_open(t))
            lb.bind('<Enter>', lambda e, t=title: self._menu_hover(t))
            lb.bind('<Leave>', lambda e: self._menu_paint())
            self._menu_lbls.append((title, lb))
        self._menu_win = None
        self._menu_cur = None
        self.bind_all('<Escape>', lambda e: self._menu_close(), add='+')

    def _menu_paint(self, hover=None):
        for t, lb in self._menu_lbls:
            if t == self._menu_cur:
                lb.config(bg='#1e6fd9', fg='#ffffff')
            elif t == hover:
                lb.config(bg='#cfe0f8', fg='#222')
            else:
                lb.config(bg='#e9edf3', fg='#222')

    def _menu_hover(self, title):
        if self._menu_win is not None and self._menu_cur != title:
            self._menu_open(title)
        else:
            self._menu_paint(hover=title)

    def _menu_close(self):
        if self._menu_win is not None:
            try:
                self._menu_win.destroy()
            except Exception:
                pass
        self._menu_win = None
        self._menu_cur = None
        self._menu_paint()

    def _menu_open(self, title):
        was = self._menu_cur
        self._menu_close()
        if was == title:
            return
        items = dict(self._menus)[title]
        lb = dict(self._menu_lbls)[title]
        w = tk.Toplevel(self)
        w.overrideredirect(True)
        w.configure(bg='#9aa6b8')
        inner = tk.Frame(w, bg='#ffffff')
        inner.pack(padx=1, pady=1)
        for it in items:
            if it is None:
                tk.Frame(inner, height=1, bg='#d5dbe5').pack(fill=tk.X, padx=6, pady=3)
                continue
            text, cmd = it
            row = tk.Label(inner, text=text, font=self.ITEM_FONT, bg='#ffffff', fg='#222',
                           anchor='w', padx=18, pady=7, cursor='hand2')
            row.pack(fill=tk.X)
            row.bind('<Enter>', lambda e, r=row: r.config(bg='#1e6fd9', fg='#ffffff'))
            row.bind('<Leave>', lambda e, r=row: r.config(bg='#ffffff', fg='#222'))
            row.bind('<Button-1>', lambda e, c=cmd: (self._menu_close(), self.after(10, c)))
        w.update_idletasks()
        w.geometry(f"+{lb.winfo_rootx()}+{lb.winfo_rooty() + lb.winfo_height()}")
        w.lift()
        self._menu_win = w
        self._menu_cur = title
        self._menu_paint()
        # 메뉴 바깥을 누르면 닫기
        self.bind('<Button-1>', self._menu_click_out, add='+')

    def _menu_click_out(self, e):
        if self._menu_win is None:
            return
        wdg = e.widget
        try:
            if str(wdg).startswith(str(self._menu_win)) or wdg in dict(self._menu_lbls).values():
                return
        except Exception:
            pass
        self._menu_close()

    def _menu_manual(self):
        root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
        cand = [os.path.join(root, f"사용설명서_Ver{APP_VERSION}.txt")]
        try:
            cand += sorted(os.path.join(root, f) for f in os.listdir(root)
                           if f.startswith("사용설명서") and f.endswith(".txt"))
        except Exception:
            pass
        text = None
        for c in cand:
            try:
                with open(c, encoding='utf-8-sig') as f:
                    text = f.read()
                break
            except Exception:
                continue
        if text is None:
            messagebox.showerror("사용설명서", "프로그램 폴더에서 사용설명서 파일을 찾지 못했습니다.")
            return
        w = tk.Toplevel(self)
        w.title(f"RM200 측색계 사용설명서  Ver {APP_VERSION}")
        w.geometry("900x700")
        fr = ttk.Frame(w); fr.pack(fill=tk.BOTH, expand=True)
        t = tk.Text(fr, wrap='word', font=('맑은 고딕', 11), padx=14, pady=10, spacing1=2, spacing3=2)
        sb = ttk.Scrollbar(fr, command=t.yview); t.configure(yscrollcommand=sb.set)
        sb.pack(side=tk.RIGHT, fill=tk.Y); t.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        t.insert('1.0', text)
        t.configure(state=tk.DISABLED)
        self._manual_win = w

    # ------------------------------------------------------------------ UI

    def _build_ui(self):
        self._build_status_bar()
        self._build_cloud_bar()
        self._build_top_bar()
        # Ver 0.22: 새로 뜨는 창(경고, 원격 단추, 찾기 등)은 늘 프로그램 창이 있는 모니터 한가운데에
        self.bind_class('Toplevel', '<Map>', self._center_new_window, add='+')
        for k, code in (('Up', 2), ('Down', 3), ('Left', 4), ('Right', 5), ('Return', 1), ('KP_Enter', 1)):
            self.bind_all(f'<KeyPress-{k}>', lambda e, c=code: self._remote_key_event(e, c), add='+')

        # 0.6: 탭 대신 큰 단추 줄(열린 탭은 파란 바탕). 윈도우 화면 방식과 상관없이 늘 같은 모양.
        st = ttk.Style(self)
        st.layout('Plain.TNotebook.Tab', [])
        self._tabbar = tk.Frame(self, bg='#dfe4ec')
        self._tabbar.pack(fill=tk.X, padx=6, pady=(6, 0))
        self._notebook = ttk.Notebook(self, style='Plain.TNotebook')
        self._notebook.pack(fill=tk.BOTH, expand=True, padx=6, pady=(0, 0))

        self._tab_measurement(self._notebook)   # 0
        self._tab_palettes(self._notebook)      # 1
        self._tab_device(self._notebook)        # 2
        self._tab_files(self._notebook)         # 3
        self._tab_fandecks(self._notebook)      # 4
        self._tab_calibration(self._notebook)   # 5
        self._tab_screen_keys(self._notebook)   # 6
        self._tab_preview(self._notebook)       # 7
        self._tab_pantone(self._notebook)       # 2 로 끼워 넣음
        self._tab_cm(self._notebook)            # Ver 0.21: 맨 끝 "이색 관리"
        self._build_tab_buttons()

    # ---- 0.4: 윗줄(버전, 연결 불빛, 기계 시각, 표준 시각 맞추기) ----
    def _build_top_bar(self):
        bar = tk.Frame(self, bg='#f4f6fa', bd=0, highlightthickness=1, highlightbackground='#d5dbe5')
        bar.pack(fill=tk.X, side=tk.TOP, padx=6, pady=(6, 0))
        tk.Label(bar, text=f"RM200 측색계  Ver {APP_VERSION}", bg="#f4f6fa", fg="#1e3a5f",
                 font=('맑은 고딕', 11, 'bold')).pack(side=tk.LEFT, padx=(8, 14), pady=6)
        self._led = tk.Canvas(bar, width=22, height=22, bg='#f4f6fa', highlightthickness=0)
        self._led.pack(side=tk.LEFT, pady=6)
        self._led_dot = self._led.create_oval(3, 3, 19, 19, fill='#c62828', outline='')
        self._led_text = tk.Label(bar, text="기계 연결 안 됨", bg='#f4f6fa', fg='#c62828',
                                  font=('맑은 고딕', 10, 'bold'), width=34, anchor='w')
        self._led_text.pack(side=tk.LEFT, padx=(6, 18))
        self._alert_btn = tk.Button(bar, text="경고 보기", command=lambda: self._show_alert_window(
            getattr(self, '_last_lcd', None)), relief=tk.FLAT, padx=10, pady=2,
            font=('맑은 고딕', 10, 'bold'), bg='#c62828', fg='white', activebackground='#9e1f1f',
            activeforeground='white', cursor='hand2')
        self._usb_btn = tk.Button(bar, text="USB 다시 연결", command=lambda: self._usb_reset(),
            relief=tk.FLAT, padx=10, pady=2, font=('맑은 고딕', 10, 'bold'), bg='#ef6c00', fg='white',
            activebackground='#c25700', activeforeground='white', cursor='hand2')
        self._devtime_var = tk.StringVar(value="기계 시각: -")
        self._devtime_lbl = tk.Label(bar, textvariable=self._devtime_var, bg='#f4f6fa', fg='#333',
                                     font=('맑은 고딕', 10, 'bold'), width=42, anchor='w')
        self._devtime_lbl.pack(side=tk.LEFT)
        # Ver 0.10: 동기화 단추는 기계 시각 바로 옆, 맞으면 꺼짐("맞음"), 틀리면 켜짐
        self._sync_btn = tk.Button(bar, text="확인 중", command=self._on_sync_time,
                                   relief=tk.FLAT, padx=12, pady=2, font=('맑은 고딕', 10, 'bold'),
                                   cursor='hand2', state=tk.DISABLED, bg='#d5dbe5', fg='#666',
                                   disabledforeground='#666')
        self._sync_btn.pack(side=tk.LEFT, padx=(8, 0), pady=4)
        self._cal_lbl = tk.Label(bar, text="", bg='#f4f6fa', fg='#555', font=('맑은 고딕', 10, 'bold'))
        self._cal_lbl.pack(side=tk.LEFT, padx=(14, 0))
        self._cal_btn = tk.Button(bar, text="교정하기", command=self._auto_calibrate,
                                  relief=tk.FLAT, padx=10, pady=2, font=('맑은 고딕', 10, 'bold'),
                                  bg='#e65100', fg='white', activebackground='#bf4300',
                                  activeforeground='white', cursor='hand2')
        self._cal_first = None
        # 엑스라이트 서버 상태(오른쪽)
        self._xs_btn = tk.Button(bar, text="업데이트 확인", command=self._on_xs_button,
                                 relief=tk.FLAT, padx=12, pady=2, font=('맑은 고딕', 10, 'bold'),
                                 cursor='hand2', bg='#1e6fd9', fg='white', activebackground='#1559b0',
                                 activeforeground='white', disabledforeground='#666')
        self._xs_btn.pack(side=tk.RIGHT, padx=8, pady=4)
        self._xs_text = tk.Label(bar, text="엑스라이트 서버: 아직 확인 안 함", bg='#f4f6fa', fg='#555',
                                 font=('맑은 고딕', 10))
        self._xs_text.pack(side=tk.RIGHT)
        self._xs_led = tk.Canvas(bar, width=18, height=18, bg='#f4f6fa', highlightthickness=0)
        self._xs_led.pack(side=tk.RIGHT, padx=(0, 4))
        self._xs_dot = self._xs_led.create_oval(2, 2, 16, 16, fill='#b0b6c0', outline='')
        self._xs_state = 'idle'     # idle / talk / ok / new / err
        self._xs_new = []
        self._xs_checked = False
        self._led_phase = 0
        self._led_state = 'off'     # off / ok / talk / lost
        self._hb_fail = 0
        self._hb_n = 0
        self._time_offset = None    # 기계 시각 - PC 시각(초)
        self._time_asked = False
        self._last_ok = time.time()
        self._dev_ref = None        # (기계 시각, 읽은 순간 PC 시각)
        self.after(250, self._led_tick)
        self.after(1000, self._clock_tick)
        self.after(2000, self._heartbeat)

    # Ver 0.12: 기계 시각은 1초마다 같은 자리에서 흘러가게(읽은 값 + 흐른 시간). 주고받는 중에도 그대로.
    def _clock_tick(self):
        try:
            self._paint_devtime()
        except Exception:
            pass
        self.after(1000, self._clock_tick)

    def _paint_devtime(self):
        ref = self._dev_ref
        if ref is None:
            if not self.connected:
                self._devtime_var.set("기계 시각: 연결되면 읽습니다")
            else:
                self._devtime_var.set("기계 시각: 읽는 중" + (" (측정이 끝나면)" if self.busy else ""))
            self._devtime_lbl.config(fg='#888')
            return
        t = ref[0] + (dt.datetime.now() - ref[1])
        txt = "기계 시각: " + t.strftime("%Y-%m-%d %H:%M:%S")
        if not self.connected:
            self._devtime_var.set(txt + "  (마지막으로 읽은 값)")
            self._devtime_lbl.config(fg='#888')
            return
        off = self._time_offset or 0
        if abs(off) >= 120:
            self._devtime_var.set(txt + f"  (PC보다 {self._fmt_gap(off)})")
            self._devtime_lbl.config(fg='#c62828')
        else:
            self._devtime_var.set(txt)
            self._devtime_lbl.config(fg='#2e7d32')

    def _led_tick(self):
        self._led_phase ^= 1
        ph = self._led_phase
        st = self._led_state
        talking = (time.time() - getattr(rm, 'LAST_IO', 0)) < 0.8
        if st == 'gone':
            dot, text, fg = ('#c62828', '#c62828'), "USB가 빠졌습니다 · 꽂으면 저절로 연결", '#c62828'
        elif st == 'lost':
            dot, text, fg = ('#c62828', '#f4b0b0'), "기계가 대답하지 않습니다", '#c62828'
        elif st == 'connecting':
            dot, text, fg = ('#ef6c00', '#ffd2a6'), "기계에 다시 연결하는 중", '#ef6c00'
        elif not self.connected:
            dot, text, fg = ('#c62828', '#c62828'), "기계 연결 안 됨", '#c62828'
        elif getattr(self, '_dev_alert', False) and not self.busy:
            dot, text, fg = ('#c62828', '#ffd2a6'), "기계 화면에 경고가 떠 있습니다", '#c62828'
        elif talking:
            dot, text, fg = ('#39ff14', '#c8ffb8'), "기계와 주고받는 중", '#1a9e00'
        else:
            ago = time.time() - getattr(self, '_last_ok', time.time())
            dot, text, fg = ('#2e7d32', '#2e7d32'), "기계 연결됨", '#2e7d32'
            if ago > 6:
                text = f"기계 연결됨 (마지막 대답 {int(ago)}초 전)"
        try:
            want = (st in ('lost', 'off') or (not self.connected and st != 'gone')) \
                and not getattr(self, '_usb_resetting', False)
            if want and not self._usb_btn.winfo_ismapped():
                self._usb_btn.pack(side=tk.LEFT, padx=(0, 10), pady=4, after=self._led_text)
            elif not want and self._usb_btn.winfo_ismapped():
                self._usb_btn.pack_forget()
        except Exception:
            pass
        if getattr(self, '_usb_resetting', False):
            dot, text, fg = ('#ef6c00', '#ffd2a6'), "USB를 다시 연결하는 중", '#ef6c00'
        try:
            self._led.itemconfig(self._led_dot, fill=dot[ph])
            self._led_text.config(text=text, fg=fg)
            xst = 'talk' if xs.ACTIVE or self._xs_state == 'talk' else self._xs_state
            xcol = {'idle': ('#b0b6c0', '#b0b6c0'), 'talk': ('#39ff14', '#c8ffb8'),
                    'ok': ('#2e7d32', '#2e7d32'), 'new': ('#ef6c00', '#ffd2a6'),
                    'err': ('#c62828', '#c62828')}[xst]
            self._xs_led.itemconfig(self._xs_dot, fill=xcol[ph])
        except Exception:
            return
        self.after(250, self._led_tick)

    def _heartbeat(self):
        """2초마다: USB 꽂힘 확인 → 연결돼 있으면 짧게 물어봄, 빠졌다 꽂히면 저절로 연결."""
        try:
            self._hb_tick()
        finally:
            self.after(2000, self._heartbeat)

    def _hb_tick(self):
        if getattr(self, '_hb_running', False):
            return
        self._hb_running = True
        busy = self.busy or getattr(self, 'preview_running', False)
        connected = self.connected
        self._hb_n += 1
        want_time = (self._hb_n % 8 == 1)
        want_scr = (self._hb_n % 5 == 3) or getattr(self, '_dev_alert', False)

        def worker():
            res = {'present': None, 'ok': None, 't': None, 'reconnected': False, 'err': None}
            try:
                res['present'] = rm.Present()
                if not res['present']:
                    pass
                elif connected and not busy:
                    try:
                        res['ok'] = rm.Ping()
                        if res['ok'] and want_scr:
                            try:
                                with rm.LOCK:
                                    res['lcd'] = rm.GetLcdData()
                                res['alert'] = lcd_has_alert(res['lcd'])
                            except Exception:
                                res['alert'] = None
                        if res['ok'] and want_time:
                            with rm.LOCK:
                                res['t'] = rm.GetTimeDT()
                                try:
                                    res['cal'] = (rm.GetCalibrationState(), rm.GetTimeToCalibExpired())
                                except Exception:
                                    res['cal'] = None
                    except Exception as e:
                        res['ok'] = False
                        res['err'] = e
                elif not connected and not busy and getattr(self, '_auto_connect', True):
                    self.after(0, lambda: setattr(self, '_led_state', 'connecting'))
                    try:
                        rm.Connect()
                        res['reconnected'] = True
                    except Exception as e:
                        res['err'] = e
            finally:
                self.after(0, lambda: self._on_hb(res, busy))
        threading.Thread(target=worker, daemon=True).start()

    def _on_hb(self, res, busy):
        self._hb_running = False
        if busy:
            # 측정·기계 다시 켜기 중: 기계가 잠깐 빠졌다 들어오는 건 정상. 표시만 하고 손대지 않음.
            self._led_state = 'connecting' if res['present'] is False else ('ok' if self.connected else self._led_state)
            return
        if res['present'] is False:
            if self.connected or self._led_state != 'gone':
                try:
                    rm.Disconnect()
                except Exception:
                    pass
            self.connected = False
            self._led_state = 'gone'
            self._paint_devtime()
            self._sync_btn.config(state=tk.DISABLED, text="연결 안 됨", bg='#d5dbe5', disabledforeground='#888')
            return
        if res['reconnected']:
            self.connected = True
            self._hb_fail = 0
            self._last_ok = time.time()
            self._led_state = 'ok'
            self._hb_n = 0
            self._update_status_bar(extra="기계에 다시 연결했습니다")
            self._refresh_file_info_async()
            return
        if not self.connected:
            if res['err'] is not None:
                self._led_state = 'off'
                if self._is_driver_err(res['err']):
                    self._driver_offer()
                    return
                if res['present'] and self._usb_auto_ok():
                    self._usb_reset(auto=True)
            return
        if busy or res['ok'] is None:
            return
        if res['ok']:
            self._hb_fail = 0
            self._last_ok = time.time()
            self._led_state = 'ok'
            if res['t'] is not None:
                self._show_device_time(res['t'])
            if res.get('cal'):
                self._show_calib(*res['cal'])
            if res.get('alert') is not None:
                if res.get('lcd'):
                    self._last_lcd = res['lcd']
                self._set_dev_alert(res['alert'], res.get('lcd'))
            return
        self._hb_fail += 1
        if self._hb_fail >= 2 and self._usb_auto_ok():
            self.connected = False
            self._led_state = 'lost'
            self._usb_reset(auto=True)
            return
        if self._hb_fail >= 2:
            # 꽂혀 있는데 대답이 없음 → 연결을 닫고 다음 차례에 다시 연결
            try:
                rm.Disconnect()
            except Exception:
                pass
            self.connected = False
            self._led_state = 'lost'

    def _set_dev_alert(self, on, lcd=None):
        was = getattr(self, '_dev_alert', False)
        self._dev_alert = bool(on)
        try:
            if on:
                self._alert_btn.pack(side=tk.LEFT, padx=(10, 0), pady=4, after=self._led_text)
            else:
                self._alert_btn.pack_forget()
        except Exception:
            pass
        if on and not was:
            self._show_alert_window(lcd)
        if not on:
            w = getattr(self, '_alert_win', None)
            if w is not None:
                try:
                    w.destroy()
                except Exception:
                    pass
                self._alert_win = None

    def _show_alert_window(self, lcd=None):
        w = getattr(self, '_alert_win', None)
        if w is not None:
            try:
                w.lift()
                return
            except Exception:
                pass
        w = tk.Toplevel(self)
        self._alert_win = w
        w.title("기계 화면에 경고가 떠 있습니다")
        w.configure(bg='#ffffff')
        w.transient(self)
        tk.Label(w, text="기계 화면에 경고(또는 오류) 창이 떠 있습니다", bg='#ffffff', fg='#c62828',
                 font=('맑은 고딕', 13, 'bold')).pack(padx=16, pady=(14, 4))
        tk.Label(w, text="경고가 떠 있는 동안 기계는 측정 명령을 받지 않습니다.\n"
                         "기계 가운데 단추를 한 번 누르거나, 아래 단추로 기계를 다시 켜면 지워집니다.\n"
                         "(다시 켜도 측정 기록·교정 자료는 그대로입니다)",
                 bg='#ffffff', fg='#333', justify=tk.LEFT, font=('맑은 고딕', 10)).pack(padx=16)
        self._alert_img = None
        try:
            if lcd:
                im = lcd_image(lcd).resize((LCD_W * 2, LCD_H * 2), Image.NEAREST)
                self._alert_img = ImageTk.PhotoImage(im)
                tk.Label(w, image=self._alert_img, bg='#ffffff', bd=1, relief=tk.SOLID).pack(pady=10)
        except Exception:
            pass
        bf = tk.Frame(w, bg='#ffffff'); bf.pack(pady=(4, 14))
        self._alert_reboot_btn = tk.Button(
            bf, text="기계 다시 켜서 경고 지우기", command=self._on_alert_reboot, relief=tk.FLAT,
            padx=14, pady=4, font=('맑은 고딕', 11, 'bold'), bg='#1e6fd9', fg='white',
            activebackground='#1559b0', activeforeground='white', cursor='hand2')
        self._alert_reboot_btn.pack(side=tk.LEFT, padx=6)
        tk.Button(bf, text="PC에서 기계 단추 누르기", command=lambda: (w.destroy(), setattr(self, '_alert_win', None),
                                                              self._open_remote()),
                  relief=tk.FLAT, padx=14, pady=4, font=('맑은 고딕', 11, 'bold'), bg='#e65100', fg='white',
                  activebackground='#bf4300', activeforeground='white', cursor='hand2').pack(side=tk.LEFT, padx=6)
        tk.Button(bf, text="USB 다시 연결", command=lambda: self._usb_reset(),
                  relief=tk.FLAT, padx=14, pady=4, font=('맑은 고딕', 11, 'bold'), bg='#ef6c00', fg='white',
                  activebackground='#c25700', activeforeground='white', cursor='hand2').pack(side=tk.LEFT, padx=6)
        tk.Button(bf, text="닫기", command=lambda: (w.destroy(), setattr(self, '_alert_win', None)),
                  relief=tk.FLAT, padx=14, pady=4, font=('맑은 고딕', 11), cursor='hand2').pack(side=tk.LEFT, padx=6)
        w.protocol("WM_DELETE_WINDOW", lambda: (w.destroy(), setattr(self, '_alert_win', None)))

    def _center_new_window(self, e):
        w = e.widget
        try:
            if not isinstance(w, tk.Toplevel) or getattr(w, '_rm_centered', False):
                return
            if w.overrideredirect():      # 메뉴처럼 스스로 자리 잡는 창은 그대로
                return
            w._rm_centered = True
            self.center_on_app(w)
        except Exception:
            pass

    def center_on_app(self, w):
        """창 w 를 프로그램 창 한가운데로(다른 모니터에 있어도 그 모니터로)."""
        w.update_idletasks()
        ww = max(w.winfo_width(), w.winfo_reqwidth())
        wh = max(w.winfo_height(), w.winfo_reqheight())
        ax, ay = self.winfo_rootx(), self.winfo_rooty()
        aw, ah = self.winfo_width(), self.winfo_height()
        x = ax + (aw - ww) // 2
        y = ay + max(0, (ah - wh) // 2)
        w.geometry(f"+{x}+{y}")
        try:
            w.lift(); w.focus_force()
        except Exception:
            pass

    # ==================================================================
    #  Ver 0.26: 공용 저장소 · 깃허브 새 판 · 드라이버 안내 · 설치 선택 · 주소 나눠 주기 · 5초 누르기
    # ==================================================================
    def _build_cloud_bar(self):
        bar = tk.Frame(self, bg='#eef2f7', highlightthickness=1, highlightbackground='#d5dbe5')
        bar.pack(fill=tk.X, side=tk.BOTTOM, padx=6, pady=(2, 2))
        self._cloud_dot = tk.Label(bar, text="●", bg='#eef2f7', fg='#b0b6c0', font=('맑은 고딕', 11))
        self._cloud_dot.pack(side=tk.LEFT, padx=(8, 2))
        self._cloud_lbl = tk.Label(bar, text="공용 저장소: 확인 중", bg='#eef2f7', fg='#555',
                                   font=('맑은 고딕', 9, 'bold'))
        self._cloud_lbl.pack(side=tk.LEFT)
        tk.Label(bar, text="   켜진 PC:", bg='#eef2f7', fg='#555', font=('맑은 고딕', 9)).pack(side=tk.LEFT)
        self._online_fr = tk.Frame(bar, bg='#eef2f7'); self._online_fr.pack(side=tk.LEFT, padx=(4, 0))
        self._online_phase = 0
        sh = tk.Frame(bar, bg='#eef2f7'); sh.pack(side=tk.RIGHT, padx=6, pady=3)
        tk.Label(sh, text="주소 나눠 주기:", bg='#eef2f7', fg='#1e3a5f',
                 font=('맑은 고딕', 9, 'bold')).pack(side=tk.LEFT, padx=(0, 4))

        def sb(txt, cmd, bg):
            tk.Button(sh, text=txt, command=cmd, relief=tk.FLAT, bg=bg, fg='white', cursor='hand2',
                      activebackground=bg, activeforeground='white',
                      font=('맑은 고딕', 9, 'bold'), padx=8, pady=1).pack(side=tk.LEFT, padx=2)
        sb("주소 복사", lambda: self._share('copy'), '#455a64')
        sb("카카오톡", lambda: self._share('kakao'), '#c9a800')
        sb("플로우", lambda: self._share('flow'), '#5b4bd5')
        sb("메일", lambda: self._share('mail'), '#1e6fd9')
        sb("다른 앱", lambda: self._share('other'), '#607d8b')

    # ---- 주소 나눠 주기 ----
    def _share(self, how):
        url = upd.PAGE
        text = f"RM200 측색계 받기(어느 PC든 최신 판): {url}"
        try:
            self.clipboard_clear(); self.clipboard_append(text); self.update()
        except Exception:
            pass
        opened = False
        try:
            if how == 'kakao' and os.name == 'nt':
                os.startfile('kakaotalk://'); opened = True
            elif how == 'flow':
                import webbrowser
                webbrowser.open('https://flow.team'); opened = True
            elif how == 'mail':
                import webbrowser, urllib.parse
                webbrowser.open('mailto:?subject=' + urllib.parse.quote('RM200 측색계')
                                + '&body=' + urllib.parse.quote(text)); opened = True
            elif how == 'other' and os.name == 'nt':
                os.startfile(url); opened = True
        except Exception:
            opened = False
        names = {'copy': '', 'kakao': '카카오톡', 'flow': '플로우', 'mail': '메일', 'other': '받는 곳 페이지'}
        if how == 'copy' or not opened:
            self._set_status(f"주소를 복사했습니다. 보낼 곳에 붙여 넣기(Ctrl+V) 하십시오: {url}")
        else:
            self._set_status(f"주소를 복사하고 {names[how]}을(를) 열었습니다. 대화창에 붙여 넣기(Ctrl+V) 하십시오.")

    # ---- 공용 저장소 ----
    def _cloud_start(self):
        self._cloud_on = not os.environ.get('RM200_NO_CLOUD')
        sd = os.path.join(os.path.dirname(os.path.abspath(PALETTES_FILE)), '.sync')
        try:
            os.makedirs(sd, exist_ok=True)
        except Exception:
            self._cloud_on = False
        self._sync_dir = sd
        pid_path = os.path.join(sd, 'pc_id')
        try:
            self._pc_id = open(pid_path, encoding='utf-8').read().strip()
        except Exception:
            import uuid
            self._pc_id = uuid.uuid4().hex[:12]
            try:
                open(pid_path, 'w', encoding='utf-8').write(self._pc_id)
            except Exception:
                pass
        self._pc_name = cloud.pc_name()
        if not self._cloud_on:
            self._cloud_show('off', "공용 저장소 꺼짐(이 PC에만 저장)")
            return
        self._cdocs = {'palettes': cloud.Doc('palettes', sd), 'cm': cloud.Doc('cm', sd)}
        self._cloud_busy = False
        self._cloud_again = False
        self._cloud_run()
        self._cloud_loop()
        self._presence_loop()

    def _cloud_show(self, st, text):
        col = {'ok': '#2e7d32', 'talk': '#39b81e', 'off': '#b0b6c0', 'err': '#c62828'}[st]
        try:
            self._cloud_dot.config(fg=col); self._cloud_lbl.config(text=text, fg=col if st != 'off' else '#555')
        except Exception:
            pass

    def _cloud_loop(self):
        self.after(30000, self._cloud_loop)
        self._cloud_run()

    def _cloud_kick(self):
        if not getattr(self, '_cloud_on', False) or getattr(self, '_cloud_applying', False):
            return
        if getattr(self, '_cloud_kick_id', None):
            try:
                self.after_cancel(self._cloud_kick_id)
            except Exception:
                pass
        self._cloud_kick_id = self.after(800, self._cloud_run)

    def _cloud_snapshot(self):
        cm = getattr(self, 'cm', None)
        return {'palettes': cloud.pal_to_map(self.palettes),
                'cm': cloud.cm_to_map(cm) if cm is not None else None}

    def _cloud_run(self):
        self._cloud_kick_id = None
        if not getattr(self, '_cloud_on', False):
            return
        if self._cloud_busy:
            self._cloud_again = True
            return
        self._cloud_busy = True
        snap = self._cloud_snapshot()
        self._cloud_show('talk', "공용 저장소와 맞추는 중")

        def worker():
            out, err = {}, None
            try:
                for k, local in snap.items():
                    if local is None:
                        continue
                    out[k] = self._cdocs[k].sync(local, self._pc_name)
            except Exception as e:
                err = e
            self.after(0, lambda: self._cloud_done(snap, out, err))
        threading.Thread(target=worker, daemon=True).start()

    def _cloud_done(self, snap, out, err):
        self._cloud_busy = False
        now = self._cloud_snapshot()
        changed_here = (now != snap)
        if not changed_here:
            self._cloud_applying = True
            try:
                if 'palettes' in out and out['palettes'] != snap['palettes']:
                    cur = self._current_palette_name() if hasattr(self, '_current_palette_name') else None
                    self.palettes = cloud.map_to_pal(out['palettes'])
                    self._save_palettes()
                    try:
                        self._refresh_palette_list()
                        if cur in self.palettes:
                            self.palettes_tab_selector_var.set(cur)
                        self._refresh_palette_entries()
                    except Exception:
                        pass
                if 'cm' in out and snap.get('cm') is not None and out['cm'] != snap['cm']:
                    self.cm = cloud.map_to_cm(out['cm'])
                    self._cm_save()
                    try:
                        self._cm_refresh()
                    except Exception:
                        pass
            finally:
                self._cloud_applying = False
        if err is not None:
            self._cloud_show('err', "공용 저장소 연결 안 됨(이 PC에 저장, 연결되면 맞춤)")
        else:
            self._cloud_show('ok', "공용 저장소: 다른 PC와 같음 " + time.strftime('%H:%M:%S'))
        if changed_here or self._cloud_again:
            self._cloud_again = False
            self._cloud_kick()

    def _presence_loop(self):
        self.after(60000, self._presence_loop)

        def worker():
            lst = None
            try:
                cloud.beat(self._pc_id, self._pc_name, APP_VERSION)
                lst = cloud.online()
            except Exception:
                lst = None
            self.after(0, lambda: self._show_online(lst))
        threading.Thread(target=worker, daemon=True).start()

    def _show_online(self, lst):
        fr = self._online_fr
        for w in fr.winfo_children():
            w.destroy()
        if lst is None:
            tk.Label(fr, text="-", bg='#eef2f7', fg='#888', font=('맑은 고딕', 9)).pack(side=tk.LEFT)
            return
        self._online_dots = []
        for pid, name, ver in lst:
            me = (pid == self._pc_id)
            chip = tk.Frame(fr, bg='#ffffff', highlightthickness=1, highlightbackground='#9ccc9c')
            chip.pack(side=tk.LEFT, padx=2)
            d = tk.Label(chip, text="●", bg='#ffffff', fg='#2e7d32', font=('맑은 고딕', 8))
            d.pack(side=tk.LEFT, padx=(4, 0))
            tk.Label(chip, text=f"{name}{' (이 PC)' if me else ''} {ver}", bg='#ffffff', fg='#1e3a5f',
                     font=('맑은 고딕', 8, 'bold')).pack(side=tk.LEFT, padx=(2, 5))
            self._online_dots.append(d)
        if not getattr(self, '_online_blinking', False):
            self._online_blinking = True
            self._online_blink()

    def _online_blink(self):
        self._online_phase ^= 1
        for d in getattr(self, '_online_dots', []):
            try:
                d.config(fg='#2e7d32' if self._online_phase else '#a5d6a7')
            except Exception:
                pass
        self.after(600, self._online_blink)

    # ---- 깃허브 새 판 ----
    def _upd_start(self):
        if os.environ.get('RM200_NO_UPDATE'):
            return
        self._upd_check()
        self.after(30 * 60 * 1000, self._upd_start)

    def _upd_check(self, manual=False):
        def worker():
            info, err = None, None
            try:
                info = upd.check(APP_VERSION)
            except Exception as e:
                err = e
            self.after(0, lambda: self._upd_found(info, err, manual))
        threading.Thread(target=worker, daemon=True).start()

    def _upd_found(self, info, err, manual):
        if err is not None:
            if manual:
                messagebox.showinfo("새 판 확인", f"깃허브에 연결하지 못했습니다.\n{err}", parent=self)
            return
        if not info:
            if manual:
                messagebox.showinfo("새 판 확인", f"지금 판 {APP_VERSION} 이(가) 최신입니다.", parent=self)
            return
        if info.get('full'):
            self._set_status(f"새 판 {info['ver']}은(는) 새 압축을 받아야 합니다: {upd.PAGE}")
            if manual or not getattr(self, '_upd_full_told', False):
                self._upd_full_told = True
                if messagebox.askyesno("새 판", f"새 판 {info['ver']}은(는) 바탕 부품도 바뀌어 새로 받아야 합니다.\n"
                                       "받는 곳 페이지를 열까요? (내 팔레트·이색 장부는 공용 저장소에 있어 그대로입니다)",
                                       parent=self):
                    import webbrowser
                    webbrowser.open(upd.PAGE)
            return
        self._upd_pending = info
        self._upd_try_apply()

    def _upd_editing(self):
        """측정·교정·창이 떠 있는 동안은 기다림."""
        if self.busy or getattr(self, '_usb_resetting', False):
            return True
        for w in self.winfo_children():
            if isinstance(w, tk.Toplevel) and w.winfo_exists() and w.winfo_viewable():
                return True
        return False

    def _upd_try_apply(self):
        info = getattr(self, '_upd_pending', None)
        if not info:
            return
        if self._upd_editing():
            self._set_status(f"새 판 {info['ver']}이(가) 있습니다. 하던 일이 끝나면 저절로 바꿉니다.")
            self.after(5000, self._upd_try_apply)
            return
        self._upd_pending = None
        self._set_status(f"새 판 {info['ver']}(으)로 바꾸는 중입니다...")

        def worker():
            err = None
            try:
                upd.apply(info)
            except Exception as e:
                err = e
            self.after(0, lambda: self._upd_applied(info, err))
        threading.Thread(target=worker, daemon=True).start()

    def _upd_applied(self, info, err):
        if err is not None:
            self._set_status(f"새 판으로 바꾸지 못했습니다(다음에 다시): {err}")
            return
        self._set_status(f"새 판 {info['ver']}(으)로 바꿨습니다. 다시 엽니다...")
        self.after(800, self._restart_self)

    def _restart_self(self):
        import subprocess
        try:
            exe = sys.executable
            if os.name == 'nt' and exe.lower().endswith('python.exe'):
                w = exe[:-10] + 'pythonw.exe'
                if os.path.exists(w):
                    exe = w
            run = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'run.py')
            subprocess.Popen([exe, run], cwd=os.path.dirname(os.path.dirname(os.path.dirname(run))))
        except Exception as e:
            self._set_status(f"다시 열지 못했습니다. 프로그램을 닫고 다시 켜 주십시오: {e}")
            return
        self._on_close()

    # ---- USB 드라이버 안내 ----
    @staticmethod
    def _is_driver_err(e):
        t = f"{e!r} {e}"
        return ('WinUSB' in t or 'Operation not supported' in t or 'NotImplemented' in t
                or 'LIBUSB_ERROR_NOT_SUPPORTED' in t)

    def _zadig_path(self):
        root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
        return os.path.join(root, 'tools', 'zadig', 'zadig-2.9.exe')

    def _driver_offer(self, force=False):
        if getattr(self, '_drv_win', None) is not None:
            try:
                self._drv_win.lift(); return
            except Exception:
                pass
        if not force and getattr(self, '_drv_told', False):
            return
        self._drv_told = True
        w = tk.Toplevel(self); self._drv_win = w
        w.title("USB 드라이버 바꾸기"); w.configure(bg='#ffffff'); w.transient(self)
        tk.Label(w, text="이 PC에서 RM200을 쓰려면 USB 드라이버를 한 번 바꿔야 합니다", bg='#ffffff',
                 fg='#c62828', font=('맑은 고딕', 13, 'bold')).pack(padx=18, pady=(14, 6), anchor='w')
        tk.Label(w, text="1. [지금 바꾸기]를 누르십시오. \"변경을 허용하시겠습니까?\"가 나오면 [예].\n"
                         "2. 뜨는 창(Zadig)에서 맨 위 칸에 RM200(또는 X-Rite)이 골라져 있고,\n"
                         "   가운데 오른쪽 칸이 WinUSB 인지 보십시오. (보통 저절로 그렇게 되어 있습니다)\n"
                         "   목록에 RM200이 없으면 Options 메뉴 → List All Devices 를 누르고 고르십시오.\n"
                         "3. 큰 단추 [Install Driver](또는 [Replace Driver])를 누르십시오. 1~2분 걸립니다.\n"
                         "4. 끝나면 그 창이 저절로 닫히고 이 프로그램이 기계에 연결됩니다.\n"
                         "PC마다 한 번만 하면 됩니다. 기계 자료는 건드리지 않습니다.",
                 bg='#ffffff', fg='#333', justify=tk.LEFT, font=('맑은 고딕', 11)).pack(padx=18, anchor='w')
        self._drv_state = tk.StringVar(value="")
        tk.Label(w, textvariable=self._drv_state, bg='#ffffff', fg='#1e6fd9',
                 font=('맑은 고딕', 11, 'bold')).pack(padx=18, pady=(8, 0), anchor='w')
        bf = tk.Frame(w, bg='#ffffff'); bf.pack(pady=12)
        tk.Button(bf, text="지금 바꾸기", command=self._driver_run, relief=tk.FLAT, bg='#1e6fd9', fg='white',
                  activebackground='#1557b0', activeforeground='white', cursor='hand2',
                  font=('맑은 고딕', 12, 'bold'), padx=18, pady=6).pack(side=tk.LEFT, padx=6)
        tk.Button(bf, text="닫기", command=self._driver_close, relief=tk.FLAT, padx=14, pady=4,
                  font=('맑은 고딕', 11), cursor='hand2').pack(side=tk.LEFT, padx=6)
        w.protocol("WM_DELETE_WINDOW", self._driver_close)

    def _driver_close(self):
        w = getattr(self, '_drv_win', None); self._drv_win = None
        if w is not None:
            try:
                w.destroy()
            except Exception:
                pass

    def _driver_run(self):
        z = self._zadig_path()
        try:
            ini = os.path.join(os.path.dirname(z), 'zadig.ini')
            with open(ini, 'w', encoding='utf-8') as f:
                f.write("[general]\n  advanced_mode = false\n  exit_on_success = true\n  log_level = 2\n"
                        "[device]\n  list_all = false\n  include_hubs = false\n  trim_whitespaces = true\n"
                        "[driver]\n  default_driver = 0\n  extract_only = false\n")
        except Exception:
            pass
        ok = False
        try:
            if os.name == 'nt':
                import ctypes
                r = ctypes.windll.shell32.ShellExecuteW(None, 'open', z, None, os.path.dirname(z), 1)
                ok = int(r) > 32
        except Exception:
            ok = False
        self._drv_launched = ok
        try:
            self._drv_state.set("Zadig 창에서 [Install Driver]를 누르십시오. 끝나면 저절로 연결됩니다..."
                                if ok else "Zadig을 열지 못했습니다. 프로그램 폴더의 USB드라이버_바꾸기.bat 을 눌러 주십시오.")
        except Exception:
            pass
        self._auto_connect = True
        self._drv_wait(0)

    def _drv_wait(self, n):
        if self.connected:
            self._set_status("USB 드라이버를 바꿨고 기계에 연결했습니다")
            try:
                self._drv_state.set("연결됐습니다. 이 창을 닫으셔도 됩니다.")
            except Exception:
                pass
            self.after(2500, self._driver_close)
            return
        if n < 120 and getattr(self, '_drv_win', None) is not None:
            self.after(3000, lambda: self._drv_wait(n + 1))

    # ---- 설치 선택 ----
    def _install_first_ask(self):
        if os.environ.get('RM200_NO_INSTALL_ASK') or os.name != 'nt':
            return
        sd = os.path.join(os.path.dirname(os.path.abspath(PALETTES_FILE)), '.sync')
        flag = os.path.join(sd, 'installed')
        if os.path.exists(flag):
            return
        try:
            os.makedirs(sd, exist_ok=True)
            open(flag, 'w').write(APP_VERSION)
        except Exception:
            pass
        if messagebox.askyesno("설치", "이 PC에 RM200 측색계를 설치하시겠습니까?\n"
                               "(바탕화면·시작 메뉴 바로가기를 만들고, 원하시면 컴퓨터 켤 때 같이 켭니다)",
                               parent=self):
            self._install_dialog()

    def _install_dialog(self):
        w = tk.Toplevel(self); w.title("설치 선택"); w.configure(bg='#ffffff'); w.transient(self)
        tk.Label(w, text="RM200 측색계 설치", bg='#ffffff', fg='#1e3a5f',
                 font=('맑은 고딕', 14, 'bold')).pack(padx=20, pady=(14, 8), anchor='w')
        v = {k: tk.BooleanVar(value=d) for k, d in
             (('desk', True), ('start', True), ('boot', False), ('task', False))}
        for k, txt in (('desk', "바탕화면에 바로가기"), ('start', "시작 화면(메뉴)에 고정"),
                       ('boot', "컴퓨터 켤 때 같이 시작"), ('task', "작업 표시줄에 고정")):
            tk.Checkbutton(w, text=txt, variable=v[k], bg='#ffffff', font=('맑은 고딕', 12),
                           anchor='w').pack(padx=24, anchor='w')
        msg = tk.StringVar(value="")
        tk.Label(w, textvariable=msg, bg='#ffffff', fg='#555', wraplength=420, justify=tk.LEFT,
                 font=('맑은 고딕', 9)).pack(padx=20, pady=(6, 0), anchor='w')

        def go():
            res = self._make_shortcuts(v['desk'].get(), v['start'].get(), v['boot'].get())
            t = "만들었습니다." if res else "만들지 못했습니다."
            if v['task'].get():
                t += ("\n작업 표시줄 고정은 윈도우가 프로그램이 직접 하는 것을 막아 두었습니다. "
                      "바탕화면의 RM200 측색계 아이콘을 오른쪽 클릭 → [작업 표시줄에 고정]을 눌러 주십시오.")
            msg.set(t)
            b.config(text="닫기", command=w.destroy)
        b = tk.Button(w, text="설치", command=go, relief=tk.FLAT, bg='#1e6fd9', fg='white',
                      activebackground='#1557b0', activeforeground='white', cursor='hand2',
                      font=('맑은 고딕', 12, 'bold'), padx=20, pady=5)
        b.pack(pady=12)

    def _make_shortcuts(self, desk, start, boot):
        if os.name != 'nt':
            return False
        import base64, subprocess
        app = os.path.dirname(os.path.abspath(__file__))
        root = os.path.dirname(os.path.dirname(app))
        pyw = os.path.join(root, 'tools', 'python', 'pythonw.exe')
        run = os.path.join(app, 'run.py')
        icon = os.path.join(app, 'rm200color.ico')
        dirs = []
        if desk:
            dirs.append("[Environment]::GetFolderPath('Desktop')")
        if start:
            dirs.append("[Environment]::GetFolderPath('Programs')")
        if boot:
            dirs.append("[Environment]::GetFolderPath('Startup')")
        if not dirs:
            return True
        q = lambda x: x.replace("'", "''")
        ps = ("$sh=New-Object -ComObject WScript.Shell;"
              f"foreach($d in @({','.join(dirs)})){{"
              "Remove-Item -LiteralPath (Join-Path $d 'RM200 색 비교기.lnk') -ErrorAction SilentlyContinue;"
              "$s=$sh.CreateShortcut((Join-Path $d 'RM200 측색계.lnk'));"
              f"$s.TargetPath='{q(pyw)}';$s.Arguments='\"{q(run)}\"';$s.WorkingDirectory='{q(root)}';"
              f"$s.IconLocation='{q(icon)},0';$s.Description='RM200 측색계';$s.Save()}}")
        enc = base64.b64encode(ps.encode('utf-16-le')).decode()
        try:
            r = subprocess.run(["powershell", "-NoProfile", "-ExecutionPolicy", "Bypass", "-EncodedCommand", enc],
                               creationflags=0x08000000, timeout=60)
            return r.returncode == 0
        except Exception:
            return False

    # ---- 5초 누르기로 이름 바꾸기 ----
    def _hold_bind(self, tree):
        tree.bind('<ButtonPress-1>', lambda e: self._hold_start(tree, e), add='+')
        tree.bind('<ButtonRelease-1>', lambda e: self._hold_stop(), add='+')
        tree.bind('<B1-Motion>', lambda e: self._hold_move(e), add='+')

    def _hold_start(self, tree, e):
        self._hold_stop()
        iid = tree.identify_row(e.y)
        if not iid:
            return
        self._hold = {'tree': tree, 'iid': iid, 't0': time.time(), 'xy': (e.x_root, e.y_root)}
        self._hold_tick()

    def _hold_move(self, e):
        h = getattr(self, '_hold', None)
        if h and (abs(e.x_root - h['xy'][0]) > 12 or abs(e.y_root - h['xy'][1]) > 12):
            self._hold_stop()

    def _hold_stop(self):
        h = getattr(self, '_hold', None)
        self._hold = None
        if h and h.get('aid'):
            try:
                self.after_cancel(h['aid'])
            except Exception:
                pass
            self._set_status("")

    def _hold_tick(self):
        h = getattr(self, '_hold', None)
        if not h:
            return
        el = time.time() - h['t0']
        if el >= 5.0:
            self._hold = None
            self._set_status("")
            self._hold_fire(h['tree'], h['iid'])
            return
        n = int(el / 0.5)
        self._set_status("이름 바꾸기: 계속 누르고 계십시오 " + "■" * n + "□" * (10 - n))
        h['aid'] = self.after(250, self._hold_tick)

    def _hold_fire(self, tree, iid):
        name = iid
        try:
            vals = tree.item(iid, 'values')
            if iid not in self.palettes and vals:
                name = vals[-1]
        except Exception:
            pass
        if name not in self.palettes:
            return
        try:
            self.palettes_tab_selector_var.set(name)
            self._refresh_palette_entries()
        except Exception:
            pass
        before = set(self.palettes)
        self._on_palette_rename()
        after = set(self.palettes)
        if before != after:
            new = (after - before)
            new = sorted(new, key=len)[0] if new else None
            if new:
                self._rename_hist = getattr(self, '_rename_hist', []) + [(name, new)]
                self._set_status(f"'{name}' → '{new}' (되돌리려면 도구 메뉴 → 이름 바꾸기 되돌리기)")

    def _rename_undo(self):
        hist = getattr(self, '_rename_hist', [])
        if not hist:
            messagebox.showinfo("되돌리기", "되돌릴 이름 바꾸기가 없습니다.", parent=self)
            return
        old, new = hist.pop()
        if new not in self.palettes or old in self.palettes:
            return
        items = list(self.palettes.items()); self.palettes = {}
        for k, val in items:
            if k == new:
                k = old
            elif k.startswith(new + '/'):
                k = old + k[len(new):]
            self.palettes[k] = val
        self._save_palettes(); self._refresh_palette_list()
        try:
            self.palettes_tab_selector_var.set(old); self._refresh_palette_entries()
        except Exception:
            pass
        self._set_status(f"이름을 '{old}'(으)로 되돌렸습니다")

    # ---- Ver 0.25: 키보드로 기계 단추 + 기계 설정 한눈에 ----
    def _remote_key_event(self, e, code):
        w = e.widget
        try:
            cls = w.winfo_class()
        except Exception:
            return
        if cls in ('Entry', 'TEntry', 'Text', 'Treeview', 'TCombobox', 'Listbox', 'Spinbox', 'TSpinbox'):
            return
        try:
            top = w.winfo_toplevel()
        except Exception:
            top = None
        P = None
        wp = getattr(self, '_rm_win_panel', None)
        if wp and top is getattr(self, '_remote_win', None):
            P = wp
        elif top is self and self._rm_tab_visible():
            P = getattr(self, '_rm_tab_panel', None)
        if P is None:
            return
        self._remote_press(P, code)
        return 'break'

    DEVMENU_ROWS = [('fw', '펌웨어 · 모델'), ('sn', '일련번호'), ('bat', '배터리'), ('ap', '조리개(측정 구멍)'),
                    ('time', '기계 시각'), ('cal', '교정(0점)'), ('cnt', '측정 기록 수'), ('temp', '온도'),
                    ('de', 'ΔE 설정값'), ('fd', '켜진 팬덱(색 견본 책)')]

    def _devmenu_build(self, parent):
        tk.Label(parent, text="기계 설정 한눈에 (PC에서 읽기)", bg='#ffffff', fg='#1e3a5f',
                 font=('맑은 고딕', 12, 'bold')).pack(anchor='w')
        tv = ttk.Treeview(parent, columns=('k', 'v'), show='headings', height=len(self.DEVMENU_ROWS))
        tv.heading('k', text='항목'); tv.heading('v', text='값')
        tv.column('k', width=150, anchor='w'); tv.column('v', width=330, anchor='w')
        for key, label in self.DEVMENU_ROWS:
            tv.insert('', tk.END, iid=key, values=(label, '-'))
        tv.pack(fill=tk.X, pady=(6, 6))
        self._devmenu_tv = tv
        row = tk.Frame(parent, bg='#ffffff'); row.pack(anchor='w', pady=(0, 6))

        def b(txt, cmd, color='#1e6fd9'):
            tk.Button(row, text=txt, command=cmd, relief=tk.FLAT, bg=color, fg='white',
                      activebackground='#1557b0', activeforeground='white', cursor='hand2',
                      font=('맑은 고딕', 10, 'bold'), padx=8, pady=3).pack(side=tk.LEFT, padx=(0, 6))
        b("다시 읽기", self._devmenu_read)
        b("조리개 바꾸기", lambda: self._notebook.select(3), '#455a64')
        b("기계 시각 맞추기", self._on_sync_time, '#455a64')
        row = tk.Frame(parent, bg='#ffffff'); row.pack(anchor='w', pady=(0, 6))
        b("팬덱 켜기·끄기", lambda: self._notebook.select(5), '#455a64')
        b("0점 맞추기", self._auto_calibrate, '#455a64')
        tk.Label(parent, text="기계 안의 설정(언어, 밝기, 소리, 꺼짐 시간 등)은 PC에서 바로 바꾸는 명령이 없습니다.\n"
                              "왼쪽 기계 화면을 보면서 단추나 키보드로 기계의 설정 메뉴에 들어가 바꾸면 됩니다.\n"
                              "PC 명령이 있는 조리개, 기계 시각, 팬덱 켜기·끄기는 위 단추로 바꿉니다(바꾸기 전에 확인을 묻습니다).",
                 bg='#ffffff', fg='#555', justify=tk.LEFT, wraplength=480,
                 font=('맑은 고딕', 9)).pack(anchor='w')
        self._devmenu_auto = False

    def _devmenu_read(self):
        if not self.connected or getattr(self, '_devmenu_busy', False):
            return
        self._devmenu_busy = True
        tv = self._devmenu_tv

        def worker():
            v = {}

            def g(key, fn):
                try:
                    with rm.LOCK:
                        v[key] = fn()
                except Exception as e:
                    v[key] = f"읽지 못함 ({e})"
            g('fw', lambda: (rm.GetFWInfo() or '').strip())
            g('sn', rm.GetSerialNum)
            g('bat', rm.GetBatteryState)
            g('ap', rm.GetAperture)
            g('time', rm.GetTimeString)
            g('cal', lambda: (rm.GetCalibrationState(), rm.GetTimeToCalibExpired()))
            g('cnt', rm.GetNumberOfEntries)
            g('temp', rm.MeasureTemperature)
            g('de', rm.GetDeltaEParameter)
            g('fd', rm.GetFandecks)
            self.after(0, lambda: show(v))

        def fmt(key, x):
            if isinstance(x, str) and x.startswith('읽지 못함'):
                return x
            try:
                if key == 'bat' and isinstance(x, (list, tuple)):
                    return f"{x[0]}% ({x[1]:.2f} V)"
                if key == 'ap':
                    return {0: '작게', 1: '보통', 2: '크게/자동'}.get(x, str(x))
                if key == 'cal':
                    return "교정 됨" if x[0] == 1 and x[1] not in (0, None) else "교정 필요"
                if key == 'temp' and isinstance(x, (int, float)):
                    return f"{x:.1f} ℃"
                if key == 'fd' and isinstance(x, list):
                    on = [f[0] for f in x if len(f) > 1 and f[1] in (1, 2)]
                    return f"{len(on)}/{len(x)}개: " + ", ".join(on)
                if isinstance(x, (list, tuple)):
                    return ", ".join(str(y) for y in x)
            except Exception:
                pass
            return '-' if x is None else str(x)

        def show(v):
            self._devmenu_busy = False
            for key, label in self.DEVMENU_ROWS:
                try:
                    tv.item(key, values=(label, fmt(key, v.get(key))))
                except Exception:
                    pass
            self._set_status("기계 설정을 읽었습니다")
        threading.Thread(target=worker, daemon=True).start()

    # ---- Ver 0.24: USB 다시 연결 (선을 뽑았다 꽂은 것처럼) ----
    def _usb_auto_ok(self):
        """저절로 다시 연결은 1분에 한 번만."""
        if getattr(self, '_usb_resetting', False) or self.busy:
            return False
        return time.time() - getattr(self, '_usb_auto_t', 0) > 60

    def _usb_windows_restart(self):
        """윈도우에서 장치를 껐다 켬(장치 관리자의 '사용 안 함 → 사용'과 같음). 관리자 허락 창이 뜸."""
        if os.name != 'nt':
            return False
        import base64, ctypes
        ps = ("$d = Get-PnpDevice -PresentOnly | Where-Object { $_.InstanceId -like 'USB\\VID_0765&PID_6001*' }; "
              "foreach ($x in $d) { Disable-PnpDevice -InstanceId $x.InstanceId -Confirm:$false; "
              "Start-Sleep -Seconds 2; Enable-PnpDevice -InstanceId $x.InstanceId -Confirm:$false }")
        enc = base64.b64encode(ps.encode('utf-16le')).decode('ascii')
        try:
            r = ctypes.windll.shell32.ShellExecuteW(None, 'runas', 'powershell.exe',
                                                    f'-NoProfile -WindowStyle Hidden -EncodedCommand {enc}',
                                                    None, 0)
            return int(r) > 32
        except Exception:
            return False

    def _usb_reset(self, auto=False):
        if getattr(self, '_usb_resetting', False) or self.busy:
            return
        self._usb_resetting = True
        if auto:
            self._usb_auto_t = time.time()
        self._set_busy(True, "USB를 다시 연결하는 중입니다(선을 뽑았다 꽂은 것처럼)...")
        log = self._meas_log

        def ping():
            try:
                return bool(rm.Ping())
            except Exception:
                return False

        def worker():
            how = None
            log("[USB 다시 연결] " + ("저절로" if auto else "단추"))
            try:
                rm.ResetUsb()
                if ping():
                    how = 'usb'
            except Exception as e:
                log(f"  1단계(USB 초기화) 실패 {e!r}")
            if how is None and not auto and self._usb_windows_restart():
                log("  2단계: 윈도우 장치 껐다 켜기")
                for _ in range(10):
                    time.sleep(1.5)
                    try:
                        rm.Connect()
                        if ping():
                            how = 'pnp'
                            break
                    except Exception:
                        pass
            log("  결과 " + (how or "실패"))
            self.after(0, lambda: done(how))

        def done(how):
            self._usb_resetting = False
            self._set_busy(False)
            self._hb_n = 0
            if how:
                self.connected = True
                self._hb_fail = 0
                self._last_ok = time.time()
                self._led_state = 'ok'
                self._update_status_bar(extra="USB를 다시 연결했습니다")
                self._set_status("USB를 다시 연결했습니다")
                try:
                    self._refresh_file_info_async()
                except Exception:
                    pass
            else:
                self.connected = False
                self._led_state = 'off'
                self._set_status("USB를 다시 연결하지 못했습니다")
                if not auto:
                    messagebox.showwarning(
                        "USB 다시 연결",
                        "PC에서 USB를 다시 붙이지 못했습니다.\n\n"
                        "USB 선을 기계에서 뽑았다가 다시 꽂아 주십시오.\n"
                        "꽂으면 저절로 연결됩니다.", parent=self)
        threading.Thread(target=worker, daemon=True).start()

    # ---- Ver 0.23: PC에서 0점 맞추기(교정) ----
    def _auto_calibrate(self, need=False):
        if not self.connected:
            messagebox.showinfo("0점 맞추기", "기계가 연결되어 있지 않습니다.")
            return
        w = getattr(self, '_cal_win', None)
        if w is not None:
            try:
                w.lift(); return
            except Exception:
                pass
        w = tk.Toplevel(self); self._cal_win = w
        w.title("교정이 필요합니다" if need else "0점 맞추기(교정)")
        w.configure(bg='#ffffff'); w.transient(self)
        C = {'run': False, 'alive': True}
        self._cal_C = C
        tk.Label(w, text=("기계가 교정(0점 맞추기)을 원합니다." if need else "PC에서 0점 맞추기(교정)"),
                 bg='#ffffff', fg='#c62828' if need else '#1e3a5f',
                 font=('맑은 고딕', 14, 'bold')).pack(padx=18, pady=(14, 4), anchor='w')
        tk.Label(w, text="1. 기계를 덮개 안쪽 흰 교정판 위에 올려 놓으십시오(덮개를 닫은 상태).\n"
                         "2. 아래 [0점 맞추기 시작]을 누르십시오. 기계 단추는 누르지 않아도 됩니다.\n"
                         "3. 끝나면 \"0점 맞추기 끝\"이 나옵니다. 그 뒤 측정하면 됩니다.",
                 bg='#ffffff', fg='#333', justify=tk.LEFT,
                 font=('맑은 고딕', 11)).pack(padx=18, pady=(0, 8), anchor='w')
        body = tk.Frame(w, bg='#ffffff'); body.pack(padx=18, pady=4, anchor='w')
        C['canvas'] = tk.Canvas(body, width=LCD_W, height=LCD_H, bg='#222',
                                highlightthickness=1, highlightbackground='#888')
        C['canvas'].pack(side=tk.LEFT)
        right = tk.Frame(body, bg='#ffffff'); right.pack(side=tk.LEFT, padx=(16, 0), fill=tk.Y)
        C['state'] = tk.StringVar(value="준비되면 [0점 맞추기 시작]을 누르십시오.")
        C['lbl'] = tk.Label(right, textvariable=C['state'], bg='#ffffff', fg='#1e3a5f', wraplength=300,
                            justify=tk.LEFT, font=('맑은 고딕', 12, 'bold'))
        C['lbl'].pack(anchor='w', pady=(4, 10))
        C['go'] = tk.Button(right, text="0점 맞추기 시작", command=lambda: self._cal_start(C),
                            font=('맑은 고딕', 13, 'bold'), bg='#1e6fd9', fg='white', relief=tk.FLAT,
                            activebackground='#1557b0', activeforeground='white', cursor='hand2',
                            padx=18, pady=8)
        C['go'].pack(anchor='w')
        tk.Button(right, text="단추로 직접 하기(기계 화면 칸)", command=lambda: self._cal_manual(),
                  relief=tk.FLAT, fg='#1e6fd9', bg='#ffffff', cursor='hand2',
                  font=('맑은 고딕', 10, 'underline')).pack(anchor='w', pady=(14, 0))
        tk.Button(w, text="닫기", command=self._cal_close, relief=tk.FLAT, padx=16, pady=3,
                  font=('맑은 고딕', 11), cursor='hand2').pack(pady=(8, 12))
        w.protocol("WM_DELETE_WINDOW", self._cal_close)
        self._cal_peek(C)

    def _cal_close(self):
        C = getattr(self, '_cal_C', None)
        if C:
            C['alive'] = False
        w = getattr(self, '_cal_win', None); self._cal_win = None
        if w is not None:
            try:
                w.destroy()
            except Exception:
                pass

    def _cal_manual(self):
        self._cal_close()
        try:
            self._notebook.select(self._rm_tab_id)
        except Exception:
            self._open_remote(calib=True)

    def _cal_draw(self, C, lcd):
        if not C.get('alive') or not lcd:
            return
        try:
            C['img'] = ImageTk.PhotoImage(lcd_image(lcd))
            C['canvas'].delete('all')
            C['canvas'].create_image(0, 0, anchor='nw', image=C['img'])
        except Exception:
            pass

    def _cal_peek(self, C):
        """시작 전 기계 화면 한 번 보여 주기."""
        def worker():
            lcd = None
            try:
                with rm.LOCK:
                    lcd = rm.GetLcdData()
            except Exception:
                pass
            self.after(0, lambda: self._cal_draw(C, lcd))
        threading.Thread(target=worker, daemon=True).start()

    def _cal_start(self, C):
        if C.get('run') or self.busy:
            return
        C['run'] = True
        C['go'].config(state=tk.DISABLED, text="맞추는 중...")
        self._set_busy(True, "0점 맞추기(교정) 중입니다. 기계를 움직이지 마십시오")

        def say(t, color='#1e3a5f'):
            self.after(0, lambda: (C['state'].set(t), C['lbl'].config(fg=color)) if C.get('alive') else None)

        def look():
            lcd = None
            try:
                with rm.LOCK:
                    lcd = rm.GetLcdData()
            except Exception:
                pass
            self.after(0, lambda: self._cal_draw(C, lcd))
            return lcd

        def calibrated():
            try:
                with rm.LOCK:
                    cs = rm.GetCalibrationState()
                    left = rm.GetTimeToCalibExpired()
            except Exception:
                return None, None, None
            return (cs == 1 and left not in (0, None)), cs, left

        def press_center():
            with rm.LOCK:
                rm.REMOTE_KEYS = True
                try:
                    rm.PressKey(1)
                finally:
                    rm.REMOTE_KEYS = False

        def worker():
            ok = False
            log = self._meas_log
            log("[0점 맞추기] 시작")
            try:
                done, cs, left = calibrated()
                log(f"  처음 교정 상태 {cs!r}, 남은 값 {left!r}")
                # 기계가 할 일: (가) 옆 측정 단추로 교정 찍기 → (나) 확인 창이면 가운데 단추
                steps = ['trigger', 'center', 'trigger', 'center', 'trigger']
                for i, st in enumerate(steps):
                    if not C.get('alive'):
                        break
                    lcd = look()
                    if lcd and lcd_has_alert(lcd):
                        say("기계 화면의 경고 창을 닫는 중...")
                        log("  경고 창 → 가운데 단추")
                        press_center(); time.sleep(2.0)
                        continue
                    if st == 'trigger':
                        say(f"교정판을 재는 중입니다 ({i // 2 + 1}번째)...")
                        log("  옆 측정 단추(7835)")
                        with rm.LOCK:
                            rm.TriggerMeasurement(self.aperture)
                    else:
                        say("기계 화면의 확인을 누르는 중...")
                        log("  가운데 단추(확인)")
                        press_center()
                    t0 = time.time()
                    while time.time() - t0 < 12 and C.get('alive'):
                        time.sleep(1.5)
                        look()
                        done, cs, left = calibrated()
                        if done:
                            break
                    log(f"  교정 상태 {cs!r}, 남은 값 {left!r}")
                    if done:
                        ok = True
                        break
            except Exception as e:
                log(f"  오류 {e!r}")
                say(f"오류: {e}", '#c62828')
            finally:
                rm.REMOTE_KEYS = False
            log("[0점 맞추기] " + ("끝(성공)" if ok else "끝나지 않음"))

            def fin():
                self._set_busy(False)
                C['run'] = False
                try:
                    with rm.LOCK:
                        cs2 = rm.GetCalibrationState(); left2 = rm.GetTimeToCalibExpired()
                    self._show_calib(cs2, left2)
                except Exception:
                    pass
                if not C.get('alive'):
                    return
                if ok:
                    C['state'].set("0점 맞추기 끝. 이제 측정하면 됩니다."); C['lbl'].config(fg='#2e7d32')
                    C['go'].config(text="끝났습니다", state=tk.DISABLED, bg='#2e7d32')
                    self._set_status("0점 맞추기(교정)를 마쳤습니다")
                else:
                    C['state'].set("PC로는 끝나지 않았습니다. 기계가 교정판 위에 있는지 확인하고 다시 누르시거나, "
                                   "[단추로 직접 하기]에서 기계 화면 안내대로 눌러 주십시오.")
                    C['lbl'].config(fg='#c62828')
                    C['go'].config(text="다시 해 보기", state=tk.NORMAL)
                    self._set_status("0점 맞추기가 끝나지 않았습니다")
            self.after(0, fin)
        threading.Thread(target=worker, daemon=True).start()

    # ---- Ver 0.19/0.22: 기계 원격 단추 (따로 뜨는 창 + "기계 화면" 칸 안 단추판) ----
    def _rm_build(self, parent, head):
        """원격 단추판 하나를 parent 안에 만들고 그 판의 상태 dict 를 돌려줌."""
        P = {'last': 0.0, 'reading': False, 'alive': True}
        tk.Label(parent, text=head, bg='#ffffff', fg='#1e3a5f', justify=tk.LEFT,
                 font=('맑은 고딕', 11, 'bold')).pack(padx=14, pady=(12, 6), anchor='w')
        body = tk.Frame(parent, bg='#ffffff'); body.pack(padx=14, pady=6, anchor='w')
        P['canvas'] = tk.Canvas(body, width=LCD_W * 2, height=LCD_H * 2, bg='#222',
                                highlightthickness=1, highlightbackground='#888')
        P['canvas'].pack(side=tk.LEFT)
        P['canvas'].bind('<MouseWheel>', lambda e: self._remote_press(P, 2 if e.delta > 0 else 3))
        P['canvas'].bind('<Button-4>', lambda e: self._remote_press(P, 2))
        P['canvas'].bind('<Button-5>', lambda e: self._remote_press(P, 3))
        P['canvas'].create_text(LCD_W, LCD_H, text="기계 화면 읽는 중", fill='#ddd',
                                font=('맑은 고딕', 12))
        pad = tk.Frame(body, bg='#ffffff'); pad.pack(side=tk.LEFT, padx=(18, 0))
        P['btns'] = []

        def kb(txt, key, r, c, big=False):
            b = tk.Button(pad, text=txt, width=6 if not big else 8, height=2,
                          command=lambda: self._remote_press(P, key), relief=tk.RAISED,
                          font=('맑은 고딕', 12, 'bold'), bg='#eef1f6', activebackground='#1e6fd9',
                          activeforeground='white', cursor='hand2', state=tk.DISABLED)
            b.grid(row=r, column=c, padx=4, pady=4)
            P['btns'].append(b)
        kb("▲\n위", 2, 0, 1); kb("◀\n왼쪽", 4, 1, 0); kb("●\n가운데", 1, 1, 1, big=True)
        kb("▶\n오른쪽", 5, 1, 2); kb("▼\n아래", 3, 2, 1)
        mb = tk.Button(pad, text="옆 측정 단추\n(측정·교정 찍기)", command=lambda: self._remote_measure(P),
                       relief=tk.RAISED, font=('맑은 고딕', 11, 'bold'), bg='#e65100', fg='white',
                       activebackground='#bf4300', activeforeground='white', cursor='hand2',
                       state=tk.DISABLED, height=2)
        mb.grid(row=3, column=0, columnspan=3, sticky='we', padx=4, pady=(16, 4))
        P['btns'].append(mb)
        P['state'] = tk.StringVar(value="기계 화면이 보이면 단추가 켜집니다")
        tk.Label(pad, textvariable=P['state'], bg='#ffffff', fg='#555', wraplength=230,
                 justify=tk.LEFT, font=('맑은 고딕', 9)).grid(row=4, column=0, columnspan=3, pady=(8, 0))
        return P

    def _open_remote(self, calib=False):
        if not self.connected:
            messagebox.showinfo("기계 원격 단추", "기계가 연결되어 있지 않습니다.")
            return
        w = getattr(self, '_remote_win', None)
        if w is not None:
            try:
                w.lift()
                return
            except Exception:
                pass
        w = tk.Toplevel(self)
        self._remote_win = w
        w.title("기계 원격 단추")
        w.configure(bg='#ffffff')
        w.transient(self)
        head = ("교정하기: 기계를 덮개 안 흰 교정판에 올려 놓으십시오.\n"
                "기계 화면 안내를 보면서 PC의 단추를 누르면 됩니다 (기계는 손으로 누르지 않아도 됩니다)."
                if calib else
                "왼쪽은 지금 기계 화면입니다(1초마다 새로 고침).\n"
                "화면을 보면서 오른쪽 단추를 누르면 기계 단추를 누른 것과 같습니다.")
        P = self._rm_build(w, head)
        P['win'] = w
        self._rm_win_panel = P
        tk.Button(w, text="닫기", command=self._close_remote, relief=tk.FLAT, padx=16, pady=3,
                  font=('맑은 고딕', 11), cursor='hand2').pack(pady=(4, 12))
        w.protocol("WM_DELETE_WINDOW", self._close_remote)
        self._remote_poll(P)

    # 예전 이름(시험·다른 곳에서 씀)
    @property
    def _rm_btns(self):
        P = getattr(self, '_rm_win_panel', None) or getattr(self, '_rm_tab_panel', None)
        return P['btns'] if P else []

    @property
    def _rm_state(self):
        P = getattr(self, '_rm_win_panel', None) or getattr(self, '_rm_tab_panel', None)
        return P['state']

    def _close_remote(self):
        P = getattr(self, '_rm_win_panel', None)
        if P:
            P['alive'] = False
        self._rm_win_panel = None
        self._rm_keys_update()
        w = getattr(self, '_remote_win', None)
        self._remote_win = None
        if w is not None:
            try:
                w.destroy()
            except Exception:
                pass

    def _rm_panel_fresh(self, P):
        return P and P.get('alive') and (time.time() - P['last']) < 3.0

    def _rm_keys_update(self):
        """원격 누르기는 화면이 막 보인 단추판이 하나라도 있을 때만 허용."""
        panels = [getattr(self, '_rm_win_panel', None)]
        tp = getattr(self, '_rm_tab_panel', None)
        if tp and self._rm_tab_visible():
            panels.append(tp)
        rm.REMOTE_KEYS = bool(self.connected and any(self._rm_panel_fresh(P) for P in panels if P))

    def _rm_tab_first_read(self):
        if self._rm_tab_visible() and not getattr(self, '_devmenu_auto', True) and self.connected:
            self._devmenu_auto = True
            self._devmenu_read()

    def _rm_tab_visible(self):
        try:
            return str(self._notebook.select()) == str(self._rm_tab_id)
        except Exception:
            return False

    def _remote_buttons(self, P, on):
        for b in P.get('btns', []):
            try:
                b.config(state=tk.NORMAL if on else tk.DISABLED)
            except Exception:
                pass

    def _remote_poll(self, P):
        if not P.get('alive'):
            return
        is_tab = P is getattr(self, '_rm_tab_panel', None)
        active = (not is_tab) or self._rm_tab_visible()
        if is_tab and active:
            self._rm_tab_first_read()
        if not active:
            P['last'] = 0.0
        self._rm_keys_update()
        self._remote_buttons(P, self._rm_panel_fresh(P) and self.connected and not self.busy and active)
        if active and not P['reading'] and self.connected and not self.busy:
            P['reading'] = True

            def worker():
                lcd = None
                try:
                    with rm.LOCK:
                        lcd = rm.GetLcdData()
                except Exception:
                    lcd = None
                self.after(0, lambda: self._remote_show(P, lcd))
            threading.Thread(target=worker, daemon=True).start()
        self.after(1000, lambda: self._remote_poll(P))

    def _remote_show(self, P, lcd):
        P['reading'] = False
        if not P.get('alive') or not lcd:
            return
        try:
            im = lcd_image(lcd).resize((LCD_W * 2, LCD_H * 2), Image.NEAREST)
            P['img'] = ImageTk.PhotoImage(im)
            P['canvas'].delete('all')
            P['canvas'].create_image(0, 0, anchor='nw', image=P['img'])
            P['last'] = time.time()
            alert = lcd_has_alert(lcd)
            if getattr(self, '_dev_alert', False) and not alert:
                self._set_dev_alert(False)
            P['state'].set("경고 창이 떠 있습니다. [● 가운데]를 누르면 넘어갑니다." if alert
                           else "기계 화면이 보입니다. 단추를 누르십시오.")
            self._rm_keys_update()
            self._remote_buttons(P, self.connected and not self.busy)
        except Exception:
            pass

    def _rm_after_press(self, P):
        P['last'] = 0.0
        self._rm_keys_update()

    def _remote_press(self, P, key):
        self._rm_keys_update()
        if not rm.REMOTE_KEYS or self.busy or not self._rm_panel_fresh(P):
            return
        names = {1: '가운데', 2: '위', 3: '아래', 4: '왼쪽', 5: '오른쪽'}

        def worker():
            err = None
            try:
                with rm.LOCK:
                    rm.PressKey(key)
            except Exception as e:
                err = e
            self.after(0, lambda: (self._rm_after_press(P), P['state'].set(
                f"{names[key]} 단추를 눌렀습니다" if err is None else f"누르지 못했습니다: {err}")))
        self._remote_buttons(P, False)   # 누른 뒤 새 화면을 보고 나서 다시 누르게
        threading.Thread(target=worker, daemon=True).start()

    def _remote_measure(self, P):
        self._rm_keys_update()
        if not rm.REMOTE_KEYS or self.busy or not self._rm_panel_fresh(P):
            return

        def worker():
            err = None
            try:
                with rm.LOCK:
                    rm.TriggerMeasurement(self.aperture)
            except Exception as e:
                err = e
            self.after(0, lambda: (self._rm_after_press(P), P['state'].set(
                "옆 측정 단추를 눌렀습니다(교정 화면이면 교정을 찍습니다)" if err is None
                else f"누르지 못했습니다: {err}")))
        self._remote_buttons(P, False)
        threading.Thread(target=worker, daemon=True).start()

    def _on_alert_reboot(self):
        if self.busy:
            return
        self._set_busy(True, "기계를 다시 켜서 경고를 지우는 중입니다(10초쯤)...")
        try:
            self._alert_reboot_btn.config(state=tk.DISABLED, text="다시 켜는 중...")
        except Exception:
            pass

        def worker():
            ok = self._reboot_device()
            alert = None
            if ok:
                try:
                    time.sleep(1.0)
                    with rm.LOCK:
                        lcd = rm.GetLcdData()
                    alert = lcd_has_alert(lcd)
                except Exception:
                    alert = None

            def done():
                self._set_busy(False)
                self._hb_n = 0
                if ok and not alert:
                    self._set_dev_alert(False)
                    self._set_status("기계를 다시 켰습니다. 경고가 지워졌습니다")
                elif ok:
                    self._set_status("기계를 다시 켰지만 화면에 아직 경고가 있습니다. 기계 가운데 단추를 눌러 주십시오")
                    try:
                        self._alert_reboot_btn.config(state=tk.NORMAL, text="기계 다시 켜서 경고 지우기")
                    except Exception:
                        pass
                else:
                    self._set_status("기계를 다시 켠 뒤 연결하지 못했습니다. USB 선을 뺐다 꽂아 주십시오")
            self.after(0, done)
        threading.Thread(target=worker, daemon=True).start()

    def _show_calib(self, state, left):
        """교정 상태. 남은 값의 단위는 기계마다 달라 두 번 읽어 줄어드는 빠르기로 시간을 셈."""
        if state == 0 or left == 0:
            self._cal_lbl.config(text="교정 필요", fg='#c62828')
            self._cal_first = None
            try:
                if not self._cal_btn.winfo_ismapped():
                    self._cal_btn.pack(side=tk.LEFT, padx=(6, 0), pady=4, after=self._cal_lbl)
            except Exception:
                pass
            return
        try:
            self._cal_btn.pack_forget()
        except Exception:
            pass
        if left is None:
            self._cal_lbl.config(text="교정 됨", fg='#2e7d32')
            return
        now = time.time()
        f = self._cal_first
        if f is None or left > f[1]:
            self._cal_first = (now, left)
            f = self._cal_first
        txt = "교정 됨"
        el = now - f[0]
        d = f[1] - left
        if el >= 50 and d > 0:
            secs = left * el / d
            if secs >= 86400:
                txt = f"교정 됨 (만료까지 약 {secs / 86400:.0f}일)"
            elif secs >= 3600:
                txt = f"교정 됨 (만료까지 약 {secs / 3600:.0f}시간)"
            else:
                txt = f"교정 됨 (만료까지 약 {max(1, secs / 60):.0f}분)"
        self._cal_lbl.config(text=txt, fg='#2e7d32')

    def _show_device_time(self, t):
        self._time_offset = (t - dt.datetime.now()).total_seconds()
        off = abs(self._time_offset)
        self._dev_ref = (t, dt.datetime.now())
        self._paint_devtime()
        self._time_btn_state(off >= 120)
        if off >= 120 and not self._time_asked:
            self._time_asked = True
            self.after(300, lambda: self._on_sync_time(auto=True))

    def _time_btn_state(self, wrong):
        if wrong:
            self._sync_btn.config(state=tk.NORMAL, text="인터넷 표준 시각과 동기화", bg='#e65100', fg='white',
                                  activebackground='#bf4300', activeforeground='white')
        else:
            self._sync_btn.config(state=tk.DISABLED, text="맞음", bg='#dcefdc', fg='#2e7d32',
                                  disabledforeground='#2e7d32')

    @staticmethod
    def _fmt_gap(sec):
        s = int(abs(sec))
        d, s = divmod(s, 86400)
        h, s = divmod(s, 3600)
        m, s = divmod(s, 60)
        parts = []
        if d:
            parts.append(f"{d}일")
        if h:
            parts.append(f"{h}시간")
        if m and not d:
            parts.append(f"{m}분")
        if not parts:
            parts.append(f"{s}초")
        return " ".join(parts) + (" 늦음" if sec < 0 else " 빠름")

    def _on_sync_time(self, auto=False):
        if not self.connected:
            if not auto:
                messagebox.showerror("기계 시각", "기계가 연결되어 있지 않습니다")
            return
        self._sync_btn.config(state=tk.DISABLED, text="표준 시각 가져오는 중", bg='#d5dbe5', disabledforeground='#666')

        def worker():
            err = None
            dev_t = std_t = src = None
            try:
                with rm.LOCK:
                    dev_t = rm.GetTimeDT()
            except Exception as e:
                err = e
            try:
                std_t, src = rm.internet_time()
            except Exception as e:
                std_t, src = dt.datetime.now(), "PC 시계(인터넷 시각을 못 가져옴)"
            self._std_pc_mark = dt.datetime.now()
            self.after(0, lambda: self._sync_time_ask(dev_t, std_t, src, err, auto))
        threading.Thread(target=worker, daemon=True).start()

    def _sync_time_ask(self, dev_t, std_t, src, err, auto):
        self._time_btn_state(abs(self._time_offset or 0) >= 120)
        dev_s = dev_t.strftime("%Y-%m-%d %H:%M:%S") if dev_t else "읽지 못함"
        std_s = std_t.strftime("%Y-%m-%d %H:%M:%S")
        gap = ""
        if dev_t:
            g = (dev_t - std_t).total_seconds()
            gap = f"\n차이: {self._fmt_gap(g)}" if abs(g) >= 2 else "\n차이: 없음(맞음)"
        head = "기계 시각이 인터넷 표준 시각과 다릅니다.\n\n" if auto else ""
        if not messagebox.askyesno(
                "기계 시각 동기화",
                f"{head}기계 시각: {dev_s}\n표준 시각: {std_s}\n(출처: {src}){gap}\n\n"
                "기계 시각을 표준 시각과 동기화하시겠습니까?\n"
                "(기계 안 시계만 바뀌고 측정 기록·교정 자료는 그대로입니다)"):
            return
        # 사용자가 방금 [예]를 눌렀으므로 안전 층 확인 창은 한 번 건너뜀
        prev = rm.confirm
        rm.confirm = lambda t, x: True
        try:
            # 가져온 뒤 흐른 시간만큼 더해서 보냄
            now_std = std_t + (dt.datetime.now() - self._sync_pc_ref(std_t))
            ok, val = try_call(rm.SetTime, now_std.year, now_std.month, now_std.day,
                               now_std.hour, now_std.minute, now_std.second)
        finally:
            rm.confirm = prev
        if ok and val:
            self._hb_n = 0
            try:
                with rm.LOCK:
                    t = rm.GetTimeDT()
                if t:
                    self._show_device_time(t)
            except Exception:
                pass
            self._set_status(f"기계 시각을 {now_std.strftime('%Y-%m-%d %H:%M:%S')} 로 맞췄습니다")
            messagebox.showinfo("기계 시각 동기화", "기계 시각을 표준 시각으로 맞췄습니다.")
        else:
            messagebox.showerror("기계 시각 동기화", f"맞추지 못했습니다: {val}")

    def _sync_pc_ref(self, std_t):
        # 표준 시각을 받은 순간의 PC 시각(대략): 지금 PC 시각에서 PC-표준 차이를 빼지 않고,
        # 받은 직후 바로 묻기 때문에 묻는 동안 흐른 시간만 더하도록 받은 시점 PC 시각을 기록
        return getattr(self, '_std_pc_mark', dt.datetime.now())

    TAB_FONT = ('맑은 고딕', 12, 'bold')

    def _build_tab_buttons(self):
        nb = self._notebook
        self._tab_btns = []
        for i, tid in enumerate(nb.tabs()):
            text = nb.tab(tid, 'text')
            lb = tk.Label(self._tabbar, text=text, font=self.TAB_FONT, padx=16, pady=9,
                          bg='#eef1f6', fg='#333333', cursor='hand2', bd=0)
            lb.pack(side=tk.LEFT, padx=(0, 2), pady=(2, 0))
            lb.bind('<Button-1>', lambda e, t=tid: nb.select(t))
            lb.bind('<Enter>', lambda e, w=lb: self._tab_hover(w, True))
            lb.bind('<Leave>', lambda e, w=lb: self._tab_hover(w, False))
            self._tab_btns.append((tid, lb))
        nb.bind('<<NotebookTabChanged>>', lambda e: self._paint_tabs(), add='+')
        self._paint_tabs()

    def _paint_tabs(self):
        try:
            cur = self._notebook.select()
        except Exception:
            return
        for tid, lb in self._tab_btns:
            if str(tid) == str(cur):
                lb.config(bg='#1e6fd9', fg='#ffffff')
            else:
                lb.config(bg='#eef1f6', fg='#333333')

    def _tab_hover(self, w, on):
        for tid, lb in self._tab_btns:
            if lb is w and str(tid) != str(self._notebook.select()):
                lb.config(bg='#cfe0f8' if on else '#eef1f6')

    # ---- Ver 0.10: 엑스라이트 서버 확인과 업데이트 ----
    def _xs_store(self):
        d = os.path.dirname(PALETTES_FILE)
        os.makedirs(d, exist_ok=True)
        return os.path.join(d, 'pantone_update.json')

    def _xs_set(self, state, text):
        self._xs_state = state
        col = {'idle': '#555', 'talk': '#1a9e00', 'ok': '#2e7d32', 'new': '#ef6c00', 'err': '#c62828'}[state]
        self._xs_text.config(text="엑스라이트 서버: " + text, fg=col)
        if state == 'new':
            self._xs_btn.config(state=tk.NORMAL, text=f"업데이트 ({len(self._xs_new)}개)", bg='#ef6c00',
                                activebackground='#c75a00')
        elif state == 'talk':
            self._xs_btn.config(state=tk.DISABLED, text="주고받는 중", bg='#d5dbe5')
        elif state == 'ok':
            self._xs_btn.config(state=tk.NORMAL, text="다시 확인", bg='#1e6fd9', activebackground='#1559b0')
        else:
            self._xs_btn.config(state=tk.NORMAL, text="업데이트 확인", bg='#1e6fd9', activebackground='#1559b0')

    def _on_xs_button(self):
        if self._xs_state == 'new':
            self._xs_update()
        else:
            self._xs_check(manual=True)

    def _xs_check(self, manual=False):
        if not self.connected:
            if manual:
                messagebox.showinfo("엑스라이트 서버", "기계를 연결해야 서버에 이 기계 번호로 물어볼 수 있습니다.")
            return
        self._xs_set('talk', "확인하는 중...")

        def worker():
            try:
                with rm.LOCK:
                    serial = rm.GetSerialNum()
                    chip = rm.GetChipId()
                    try:
                        vers = rm.ReadVersionsDotDat() or []
                    except Exception:
                        vers = []
                dev = {}
                for f in vers:
                    try:
                        dev[f[1]] = f[5]
                    except Exception:
                        pass
                sess = xs.open_session(serial, xs.chip_key(chip))
                files = xs.available_files(sess)
                self.after(0, lambda: self._xs_checked_done(files, dev, None, manual))
            except Exception as e:
                self.after(0, lambda e=e: self._xs_checked_done(None, None, e, manual))
        threading.Thread(target=worker, daemon=True).start()

    def _xs_checked_done(self, files, dev, err, manual):
        now = dt.datetime.now().strftime('%H:%M')
        if err:
            self._xs_set('err', f"연결 실패 ({now})")
            if manual:
                messagebox.showerror("엑스라이트 서버", f"서버와 통신하지 못했습니다:\n{err}")
            return
        pc = {d['sku']: d['version'] for d in pantone_decks()}
        self._xs_files = files
        new = []
        dev_new = []
        for f in files:
            if f['FileType'] != 'Fandeck' or not f['Description'].startswith('PANTONE'):
                continue
            if f['SKU'] not in pc or xs.vkey(f['VersionString']) > xs.vkey(pc[f['SKU']]):
                new.append(f)
            dv = dev.get(f['SKU'])
            if dv and xs.vkey(f['VersionString']) > xs.vkey(dv):
                dev_new.append(f)
        self._xs_new = new
        self._xs_dev_new = dev_new
        if new:
            self._xs_set('new', f"새 판 {len(new)}개 있음 ({now} 확인)")
            if manual:
                messagebox.showinfo("엑스라이트 서버",
                                    "새 판 팬덱이 있습니다:\n" + "\n".join(f"{f['Description']} {f['VersionString']}" for f in new)
                                    + "\n\n[업데이트]를 누르면 이 프로그램의 팬톤 색 자료를 새 판으로 바꿉니다.")
        else:
            self._xs_set('ok', f"최신입니다 ({now} 확인)")
            if manual:
                msg = "이 프로그램의 팬톤 팬덱은 모두 최신입니다."
                if dev:
                    msg += ("\n기계 안 팬덱도 서버와 같은 판입니다." if not dev_new else
                            "\n기계 안 팬덱 중 서버에 새 판이 있는 것: " + ", ".join(f['Description'] for f in dev_new)
                            + "\n(기계에 넣는 일은 기계 쓰기라서 이 프로그램에서는 하지 않습니다)")
                messagebox.showinfo("엑스라이트 서버", msg)

    def _xs_update(self):
        files = list(self._xs_new)
        if not files:
            return
        if not messagebox.askyesno("업데이트",
                                   "엑스라이트 서버에서 새 판 팬덱을 받아 이 프로그램의 팬톤 색 자료를 바꿀까요?\n"
                                   + "\n".join(f"{f['Description']} {f['VersionString']}" for f in files)
                                   + "\n\n기계에는 아무것도 쓰지 않습니다."):
            return
        self._xs_set('talk', "받는 중...")
        store = self._xs_store()

        def worker():
            try:
                try:
                    with open(store, encoding='utf-8') as fp:
                        upd = json.load(fp)
                except Exception:
                    upd = {'decks': []}
                tmpdir = os.path.dirname(store)
                for i, f in enumerate(files):
                    path = os.path.join(tmpdir, f"_{f['SKU']}.fdk")
                    self.after(0, lambda i=i, f=f: self._xs_set('talk', f"받는 중 {i + 1}/{len(files)} {f['Description']}"))
                    xs.download(f['FileURL'], path)
                    cols = xs.parse_fdk(path)
                    try:
                        os.remove(path)
                    except Exception:
                        pass
                    if not cols:
                        raise Exception(f"{f['Description']} 파일에서 색을 읽지 못했습니다")
                    ko = next((d['ko'] for d in pantone_decks() if d['sku'] == f['SKU']), f['Description'])
                    upd['decks'] = [d for d in upd['decks'] if d['sku'] != f['SKU']] + [{
                        'sku': f['SKU'], 'name': f['Description'], 'ko': ko, 'version': f['VersionString'],
                        'date': f['VersionDate'].split()[0], 'edited': '', 'colors': cols}]
                with open(store + '.tmp', 'w', encoding='utf-8') as fp:
                    json.dump(upd, fp, ensure_ascii=False, separators=(',', ':'))
                os.replace(store + '.tmp', store)
                self.after(0, lambda: self._xs_update_done(files, None))
            except Exception as e:
                self.after(0, lambda e=e: self._xs_update_done(files, e))
        threading.Thread(target=worker, daemon=True).start()

    def _xs_update_done(self, files, err):
        global _PANTONE
        if err:
            self._xs_set('err', "업데이트 실패")
            messagebox.showerror("업데이트", f"업데이트하지 못했습니다:\n{err}")
            return
        _PANTONE = None
        try:
            self._pt_fill()
            self.compare_palette_combo['values'] = self._palette_names_for_compare()
        except Exception:
            pass
        self._xs_new = []
        self._xs_set('ok', "업데이트됐습니다 (최신)")
        messagebox.showinfo("업데이트", "업데이트됐습니다.\n" + "\n".join(
            f"{f['Description']} → {f['VersionString']}" for f in files))

    def _build_status_bar(self):
        self.status_var = tk.StringVar(value="준비 중...")
        status_bar = ttk.Label(self, textvariable=self.status_var,
                               relief=tk.SUNKEN, anchor=tk.W, padding=(6, 3))
        status_bar.pack(fill=tk.X, side=tk.BOTTOM)

    def _set_status(self, text):
        self.status_var.set(text)

    def _set_busy(self, busy, text=None):
        self.busy = busy
        state = tk.DISABLED if busy else tk.NORMAL
        for side in ('ref', 'smp'):
            try:
                self.widgets[side]['measure_btn'].config(state=state)
            except Exception:
                pass
        if text:
            self._set_status(text)

    def _update_status_bar(self, extra=None):
        parts = []
        parts.append("연결됨." if self.connected else "연결 안 됨.")
        if self.device_info.get('fw'):
            parts.append(f"FW: {self.device_info['fw']}")
        if self.device_info.get('sn'):
            parts.append(f"SN: {self.device_info['sn']}")
        if self.device_info.get('count') is not None:
            parts.append(f"기록 수: {self.device_info['count']}")
        if self.device_info.get('dev_time'):
            parts.append(f"기계 시각: {self.device_info['dev_time']}")
        if extra:
            parts.append(extra)
        self._set_status("  ".join(parts))

    # ======================================================================
    #  ВКЛАДКА 1. ИЗМЕРЕНИЯ
    # ======================================================================

    def _tab_measurement(self, nb):
        frame = ttk.Frame(nb, padding=8)
        nb.add(frame, text="측정·비교")

        top = ttk.Frame(frame)
        top.pack(fill=tk.BOTH, expand=True)

        self._build_panel(top, 'ref').pack(side=tk.LEFT, fill=tk.BOTH,
                                           expand=True, padx=(0, 5))
        self._build_panel(top, 'smp').pack(side=tk.LEFT, fill=tk.BOTH,
                                           expand=True, padx=(5, 0))

        # ---- 비교 방식 ----
        cmp_frame = ttk.LabelFrame(frame, text="비교 방식")
        cmp_frame.pack(fill=tk.X, pady=(10, 0))

        row1 = ttk.Frame(cmp_frame)
        row1.pack(fill=tk.X, padx=4, pady=4)

        ttk.Label(row1, text="팔레트:").pack(side=tk.LEFT, padx=4)
        self.compare_palette_var = tk.StringVar(value=PSEUDO_CMYK)
        self.compare_palette_combo = ttk.Combobox(
            row1, textvariable=self.compare_palette_var,
            values=self._palette_names_for_compare(),
            width=28, state='readonly')
        self.compare_palette_combo.pack(side=tk.LEFT, padx=4)
        self.compare_palette_combo.bind(
            '<<ComboboxSelected>>', lambda e: self._on_palette_changed())

        ttk.Label(row1, text="섞을 색 수(N):").pack(side=tk.LEFT, padx=(16, 4))
        self.n_mix_var = tk.StringVar(value="3")
        self.n_mix_spin = ttk.Spinbox(row1, from_=1, to=20, width=5,
                                      textvariable=self.n_mix_var)
        self.n_mix_spin.pack(side=tk.LEFT, padx=4)

        # ---- Источник эталона ----
        row2 = ttk.Frame(cmp_frame)
        row2.pack(fill=tk.X, padx=4, pady=4)

        ttk.Label(row2, text="기준색:").pack(side=tk.LEFT, padx=4)
        self.ref_source_var = tk.StringVar(value='measure')
        ttk.Radiobutton(row2, text="측정값으로", value='measure',
                        variable=self.ref_source_var,
                        command=self._on_ref_source_changed).pack(side=tk.LEFT, padx=4)
        ttk.Radiobutton(row2, text="CMYK 직접 입력", value='cmyk',
                        variable=self.ref_source_var,
                        command=self._on_ref_source_changed).pack(side=tk.LEFT, padx=4)
        ttk.Radiobutton(row2, text="RGB 직접 입력", value='rgb',
                        variable=self.ref_source_var,
                        command=self._on_ref_source_changed).pack(side=tk.LEFT, padx=4)

        # ---- Поля ручного CMYK ----
        self.manual_cmyk_frame = ttk.Frame(cmp_frame)
        self.manual_cmyk_frame.pack(fill=tk.X, padx=4, pady=2)
        self.man_c_var = tk.StringVar(value="0")
        self.man_m_var = tk.StringVar(value="0")
        self.man_y_var = tk.StringVar(value="0")
        self.man_k_var = tk.StringVar(value="0")
        for label, var in (("C %", self.man_c_var), ("M %", self.man_m_var),
                           ("Y %", self.man_y_var), ("K %", self.man_k_var)):
            ttk.Label(self.manual_cmyk_frame, text=label).pack(side=tk.LEFT, padx=(4, 0))
            ttk.Entry(self.manual_cmyk_frame, textvariable=var, width=7).pack(
                side=tk.LEFT, padx=2)

        # ---- Поля ручного RGB ----
        self.manual_rgb_frame = ttk.Frame(cmp_frame)
        self.manual_rgb_frame.pack(fill=tk.X, padx=4, pady=2)
        self.man_r_var = tk.StringVar(value="128")
        self.man_g_var = tk.StringVar(value="128")
        self.man_b_var = tk.StringVar(value="128")
        for label, var in (("R", self.man_r_var), ("G", self.man_g_var),
                           ("B", self.man_b_var)):
            ttk.Label(self.manual_rgb_frame, text=label).pack(side=tk.LEFT, padx=(4, 0))
            ttk.Entry(self.manual_rgb_frame, textvariable=var, width=5).pack(
                side=tk.LEFT, padx=2)

        # ---- Кнопки ----
        actions = ttk.Frame(frame)
        actions.pack(fill=tk.X, pady=(8, 0))

        ttk.Button(actions, text="계산하기",
                   command=self._on_calculate).pack(side=tk.LEFT)
        ttk.Button(actions, text="기계에서 최근 2개 가져오기(양쪽)",
                   command=self._on_import_both).pack(side=tk.LEFT, padx=5)
        ttk.Button(actions, text="RM200 다시 연결",
                   command=self._connect_async).pack(side=tk.LEFT, padx=5)

        res_frame = ttk.LabelFrame(frame, text="결과")
        res_frame.pack(fill=tk.BOTH, expand=False, pady=(8, 0))
        self.result_text = tk.Text(res_frame, height=12, wrap=tk.NONE,
                                   font=("Consolas", 10))
        self.result_text.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        self._on_ref_source_changed()
        self._on_palette_changed()

    def _on_ref_source_changed(self):
        src = self.ref_source_var.get()
        # Скрываем всё
        self.manual_cmyk_frame.pack_forget()
        self.manual_rgb_frame.pack_forget()
        if src == 'cmyk':
            self.manual_cmyk_frame.pack(fill=tk.X, padx=4, pady=2)
        elif src == 'rgb':
            self.manual_rgb_frame.pack(fill=tk.X, padx=4, pady=2)

    def _on_palette_changed(self):
        pal = self.compare_palette_var.get()
        if pal == PSEUDO_CMYK:
            self.n_mix_spin.config(state=tk.DISABLED)
        else:
            self.n_mix_spin.config(state=tk.NORMAL)

    def _build_panel(self, parent, side):
        data = self.state_data[side]
        w = self.widgets[side]

        frame = ttk.LabelFrame(parent, text=data['title'], padding=10)

        # Ver 0.15: 색 칸을 크게(칸 너비 가득, 높이 220). 창 크기에 맞춰 다시 그림
        w['swatch'] = tk.Canvas(frame, width=300, height=220, bg='white',
                                highlightthickness=1,
                                highlightbackground='#888')
        w['swatch'].pack(fill=tk.X)
        w['swatch'].create_text(150, 110, text="자료 없음", fill="#888")
        w['swatch'].bind('<Configure>', lambda e, s=side: self._update_panel(s))

        w['lab_var'] = tk.StringVar(value="—")
        ttk.Label(frame, textvariable=w['lab_var'],
                  font=("Consolas", 11)).pack(pady=(6, 2))

        # Ver 0.13: 잰 색(평균)과 가장 가까운 팬톤을 바로 보여 줌. 누르면 팬톤 색 보기로 감
        ptr = tk.Frame(frame, bg='#eef4ff', cursor='hand2', highlightthickness=1,
                       highlightbackground='#9bbcf0')
        ptr.pack(fill=tk.X, pady=(2, 4))
        w['pt_chip'] = tk.Canvas(ptr, width=34, height=34, bg='#eef4ff', highlightthickness=0,
                                 cursor='hand2')
        w['pt_chip'].pack(side=tk.LEFT, padx=(4, 6), pady=3)
        w['pt_var'] = tk.StringVar(value="가장 가까운 팬톤: 측정하면 여기에 나옵니다")
        lb = tk.Label(ptr, textvariable=w['pt_var'], bg='#eef4ff', fg='#1e3a5f', anchor='w',
                      justify=tk.LEFT, font=('맑은 고딕', 10, 'bold'), cursor='hand2')
        lb.pack(side=tk.LEFT, fill=tk.X, expand=True)
        for wd in (ptr, w['pt_chip'], lb):
            wd.bind('<Button-1>', lambda e, s=side: self._goto_pantone(s))

        list_frame = ttk.LabelFrame(frame, text="측정값 목록", padding=4)
        list_frame.pack(fill=tk.BOTH, expand=True, pady=5)
        w['listbox'] = tk.Text(list_frame, height=4, width=40,
                               font=("Consolas", 9), state=tk.DISABLED)
        w['listbox'].pack(fill=tk.BOTH, expand=True)

        btns = ttk.Frame(frame)
        btns.pack(fill=tk.X, pady=(5, 0))
        w['measure_btn'] = ttk.Button(btns, text="측정",
                                      command=lambda: self._on_measure(side))
        w['measure_btn'].pack(side=tk.LEFT, padx=(0, 3))
        ttk.Button(btns, text="가져오기",
                   command=lambda: self._on_import_latest(side)).pack(side=tk.LEFT, padx=3)
        ttk.Button(btns, text="지우기",
                   command=lambda: self._on_clear(side)).pack(side=tk.LEFT, padx=3)
        tk.Button(btns, text="우리 물건에서 찾기", command=lambda: self._find_own(side),
                  relief=tk.FLAT, padx=10, font=('맑은 고딕', 10, 'bold'), cursor='hand2',
                  bg='#2e7d32', fg='white', activebackground='#1b5e20',
                  activeforeground='white').pack(side=tk.RIGHT, padx=3)
        tk.Button(btns, text="팬톤에서 찾기", command=lambda: self._goto_pantone(side),
                  relief=tk.FLAT, padx=10, font=('맑은 고딕', 10, 'bold'), cursor='hand2',
                  bg='#1e6fd9', fg='white', activebackground='#1559b0',
                  activeforeground='white').pack(side=tk.LEFT, padx=3)

        return frame

    # ======================================================================
    #  ВКЛАДКА 2. ПАЛИТРЫ
    # ======================================================================

    def _tab_palettes(self, nb):
        frame = ttk.Frame(nb, padding=10)
        nb.add(frame, text="내 팔레트")

        # --- Верхняя панель: выбор палитры + операции ---
        top = ttk.Frame(frame)
        top.pack(fill=tk.X, pady=(0, 6))

        ttk.Label(top, text="팔레트:").pack(side=tk.LEFT, padx=4)
        self.palettes_tab_selector_var = tk.StringVar()
        self.palettes_tab_selector = ttk.Combobox(
            top, textvariable=self.palettes_tab_selector_var,
            values=list(self.palettes.keys()), width=30, state='readonly')
        self.palettes_tab_selector.pack(side=tk.LEFT, padx=4)
        self.palettes_tab_selector.bind(
            '<<ComboboxSelected>>', lambda e: self._refresh_palette_entries())

        ttk.Button(top, text="팔레트 추가",
                   command=self._on_palette_add).pack(side=tk.LEFT, padx=4)
        ttk.Button(top, text="자식 폴더 추가",
                   command=self._on_palette_add_child).pack(side=tk.LEFT, padx=4)
        ttk.Button(top, text="이름 바꾸기",
                   command=self._on_palette_rename).pack(side=tk.LEFT, padx=4)
        ttk.Button(top, text="지우기",
                   command=self._on_palette_delete).pack(side=tk.LEFT, padx=4)

        # --- Список цветов (Treeview) ---
        mid = ttk.Frame(frame)
        mid.pack(fill=tk.BOTH, expand=True)
        # Ver 0.20: 왼쪽 폴더 나무 ("LVT/시리즈A" → LVT 아래 시리즈A)
        ff = ttk.Frame(mid)
        ff.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 8))
        ttk.Label(ff, text="폴더", font=('맑은 고딕', 10, 'bold')).pack(anchor='w')
        self.pal_folder_tree = ttk.Treeview(ff, show='tree', selectmode='browse', height=18)
        self.pal_folder_tree.column('#0', width=220)
        self.pal_folder_tree.pack(fill=tk.Y, expand=True)
        self.pal_folder_tree.bind('<<TreeviewSelect>>', self._on_pal_folder_select)
        self._hold_bind(self.pal_folder_tree)
        tree_frame = ttk.Frame(mid)
        tree_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        columns = ('sw', 'name', 'L', 'a', 'b')
        self.palette_tree = ttk.Treeview(tree_frame, columns=columns,
                                         show='headings', selectmode='extended')
        self.palette_tree.heading('sw', text='색')
        self.palette_tree.column('sw', width=60, anchor='center')
        self.palette_tree.heading('name', text='이름')
        self.palette_tree.heading('L', text='L*')
        self.palette_tree.heading('a', text='a*')
        self.palette_tree.heading('b', text='b*')
        self.palette_tree.column('name', width=260, anchor='w')
        self.palette_tree.column('L', width=90, anchor='e')
        self.palette_tree.column('a', width=90, anchor='e')
        self.palette_tree.column('b', width=90, anchor='e')

        scrollbar = ttk.Scrollbar(tree_frame, orient=tk.VERTICAL,
                                  command=self.palette_tree.yview)
        self.palette_tree.configure(yscrollcommand=scrollbar.set)
        self.palette_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        # --- Нижняя панель: операции с цветами ---
        bottom = ttk.Frame(frame)
        bottom.pack(fill=tk.X, pady=(6, 0))

        ttk.Button(bottom, text="새 색 측정해 넣기",
                   command=self._on_palette_measure).pack(side=tk.LEFT, padx=3)
        ttk.Button(bottom, text="직접 입력",
                   command=self._on_palette_manual).pack(side=tk.LEFT, padx=3)
        ttk.Button(bottom, text="색 이름 바꾸기",
                   command=self._on_palette_entry_rename).pack(side=tk.LEFT, padx=3)
        ttk.Button(bottom, text="색 지우기",
                   command=self._on_palette_entry_delete).pack(side=tk.LEFT, padx=3)
        ttk.Button(bottom, text="색 복사",
                   command=self._on_palette_entry_dup).pack(side=tk.LEFT, padx=3)

        self.palettes_status = tk.StringVar(value="")
        ttk.Label(frame, textvariable=self.palettes_status,
                  padding=(0, 6, 0, 0), foreground="#555").pack(anchor=tk.W)

        # Инициализация
        if self.palettes:
            first = sorted(self.palettes.keys())[0]
            self.palettes_tab_selector_var.set(first)
        self._refresh_palette_entries()
        self._refresh_pal_folders()

    def _refresh_palette_list(self):
        # обновляем оба комбобокса
        try:
            self.palettes_tab_selector['values'] = sorted(self.palettes.keys())
        except Exception:
            pass
        self._refresh_pal_folders()
        try:
            self.compare_palette_combo['values'] = self._palette_names_for_compare()
        except Exception:
            pass

    # ---- Ver 0.20: 폴더 나무 ----
    @staticmethod
    def _pal_folders(names):
        """'LVT/시리즈A' 같은 이름에서 모든 폴더 경로(중간 폴더 포함)를 정렬해서."""
        out = set()
        for n in names:
            parts = [x for x in n.split('/')]
            for i in range(1, len(parts) + 1):
                out.add('/'.join(parts[:i]))
        return sorted(out)

    def _refresh_pal_folders(self):
        t = getattr(self, 'pal_folder_tree', None)
        if t is None:
            return
        cur = self._current_palette_name()
        t.delete(*t.get_children())
        for path in self._pal_folders(self.palettes.keys()):
            parent = path.rsplit('/', 1)[0] if '/' in path else ''
            label = path.rsplit('/', 1)[-1]
            n = len(self.palettes[path]['entries']) if path in self.palettes else 0
            t.insert(parent, 'end', iid=path, text=f"{label}  ({n})", open=True)
        if cur and t.exists(cur):
            t.selection_set(cur)
            t.see(cur)

    def _on_pal_folder_select(self, e=None):
        sel = self.pal_folder_tree.selection()
        if not sel:
            return
        name = sel[0]
        if name not in self.palettes:
            # 이름만 있는 중간 폴더 → 빈 팔레트로 만들어 둠
            self.palettes[name] = {'entries': []}
            self._save_palettes()
        if self.palettes_tab_selector_var.get() != name:
            self.palettes_tab_selector_var.set(name)
            self._refresh_palette_entries()

    def _on_palette_add_child(self):
        cur = self._current_palette_name()
        if not cur:
            messagebox.showinfo("자식 폴더", "먼저 왼쪽에서 부모 폴더(팔레트)를 고르십시오.")
            return
        name = simpledialog.askstring("자식 폴더 추가", f"'{cur}' 아래에 만들 폴더 이름:", parent=self)
        if not name or not name.strip():
            return
        full = cur + '/' + name.strip().strip('/')
        if full in self.palettes:
            messagebox.showwarning("내 팔레트", "같은 이름의 폴더가 이미 있습니다.")
            return
        self.palettes[full] = {'entries': []}
        self._save_palettes()
        self.palettes_tab_selector_var.set(full)
        self._refresh_palette_list()
        self._refresh_palette_entries()

    def _current_palette_name(self):
        return self.palettes_tab_selector_var.get()

    def _current_palette(self):
        n = self._current_palette_name()
        return self.palettes.get(n)

    def _refresh_palette_entries(self):
        for item in self.palette_tree.get_children():
            self.palette_tree.delete(item)

        p = self._current_palette()
        if not p:
            self.palettes_status.set("팔레트를 고르지 않았습니다.")
            return

        for i, e in enumerate(p['entries']):
            L, a, b = e['lab']
            rgb = '#%02x%02x%02x' % lab_to_rgb(L, a, b)
            tag = 'c' + rgb[1:]
            try:
                self.palette_tree.tag_configure(tag, background=rgb,
                                                foreground='#000' if L > 55 else '#fff')
            except Exception:
                pass
            self.palette_tree.insert('', 'end', iid=str(i), tags=(tag,),
                                     values=('', e['name'],
                                             f"{L:.3f}", f"{a:.3f}", f"{b:.3f}"))
        self.palettes_status.set(f"팔레트 색 수: {len(p['entries'])}")
        try:
            t = self.pal_folder_tree
            cur = self._current_palette_name()
            if t.exists(cur):
                t.item(cur, text=f"{cur.rsplit('/', 1)[-1]}  ({len(p['entries'])})")
        except Exception:
            pass

    def _selected_palette_indices(self):
        sel = self.palette_tree.selection()
        return [int(i) for i in sel]

    # --- операции с палитрами ---

    def _on_palette_add(self):
        name = simpledialog.askstring("새 팔레트",
                                      "팔레트 이름:",
                                      parent=self)
        if not name:
            return
        name = name.strip()
        if not name:
            return
        if name in self.palettes:
            messagebox.showwarning("내 팔레트", "같은 이름의 팔레트가 이미 있습니다.")
            return
        self.palettes[name] = {'entries': []}
        self._save_palettes()
        self._refresh_palette_list()
        self.palettes_tab_selector_var.set(name)
        self._refresh_palette_entries()

    def _on_palette_rename(self):
        old = self._current_palette_name()
        if old not in self.palettes:
            return
        new = simpledialog.askstring("팔레트 이름 바꾸기",
                                     "새 이름:",
                                     initialvalue=old, parent=self)
        if not new:
            return
        new = new.strip()
        if not new or new == old:
            return
        if new in self.palettes:
            messagebox.showwarning("내 팔레트", "같은 이름의 팔레트가 이미 있습니다.")
            return
        # сохраняем порядок
        items = list(self.palettes.items())
        self.palettes = {}
        for k, v in items:
            if k == old:
                k = new
            elif k.startswith(old + '/'):
                k = new + k[len(old):]   # Ver 0.20: 자식 폴더도 함께
            self.palettes[k] = v
        self._save_palettes()
        self._refresh_palette_list()
        self.palettes_tab_selector_var.set(new)
        self._refresh_palette_entries()

    def _on_palette_delete(self):
        name = self._current_palette_name()
        if name not in self.palettes:
            return
        if not messagebox.askyesno("팔레트 지우기",
                                   f"팔레트 '{name}' 을(를) 지울까요? "
                                   f"({len(self.palettes[name]['entries'])} 개 색)?"):
            return
        del self.palettes[name]
        self._save_palettes()
        self._refresh_palette_list()
        if self.palettes:
            self.palettes_tab_selector_var.set(list(self.palettes.keys())[0])
        else:
            self.palettes_tab_selector_var.set('')
        self._refresh_palette_entries()

    # --- операции с цветами палитры ---

    def _auto_entry_name(self, p):
        used = {e['name'] for e in p['entries']}
        i = 1
        while True:
            n = f"Color {i}"
            if n not in used:
                return n
            i += 1

    def _add_entry_to_current_palette(self, lab, name=None):
        p = self._current_palette()
        if not p:
            messagebox.showwarning("내 팔레트",
                                   "먼저 팔레트를 만들거나 고르십시오.")
            return
        if name is None:
            name = self._auto_entry_name(p)
        p['entries'].append({'name': name, 'lab': tuple(lab)})
        self._save_palettes()
        self._refresh_palette_entries()

    def _on_palette_measure(self):
        if not self.connected:
            messagebox.showerror("오류", "RM200 과 연결되어 있지 않습니다")
            return
        if self.busy:
            return
        if self._current_palette() is None:
            messagebox.showwarning("내 팔레트",
                                   "먼저 팔레트를 만들거나 고르십시오.")
            return

        self._set_busy(True, "측정 중입니다... RM200 을 측정할 곳에 대고 기다리십시오.")

        def worker():
            try:
                prev_count = safe_command(rm.GetNumberOfEntries) or 0
                safe_command(rm.TriggerMeasurement, self.aperture)

                deadline = time.time() + self.timeout
                got = False
                while time.time() < deadline:
                    try:
                        cnt = safe_command(rm.GetNumberOfEntries)
                    except Exception:
                        cnt = None
                    if cnt is not None and cnt > prev_count:
                        got = True
                        break
                    time.sleep(POLL_INTERVAL)

                if not got:
                    raise TimeoutError("정해진 시간 안에 측정이 끝나지 않았습니다")

                time.sleep(POST_MEAS_PAUSE)

                if self.reconnect_after:
                    self._reconnect_device()

                data = safe_command(rm.FetchFile, "MeasDataV05.dat")
                records = parse_measdata(data)
                if not records:
                    raise RuntimeError("기록 파일에 쓸 수 있는 측정값이 없습니다")

                self.after(0, lambda: self._on_palette_pick_records(records, None))
            except Exception as e:
                self.after(0, lambda e=e: self._on_palette_pick_records(None, e))

        threading.Thread(target=worker, daemon=True).start()

    def _on_palette_pick_records(self, records, error):
        self._set_busy(False)
        if error:
            self._set_status(f"측정 오류: {error}")
            messagebox.showerror("측정 오류", str(error))
            return
        chosen = self._show_pick_record_dialog('ref', records)
        if chosen is None:
            self._set_status("팔레트에 넣지 않았습니다")
            return
        self._add_entry_to_current_palette(chosen['sample_lab'])
        self._set_status("팔레트에 색을 넣었습니다")

    def _on_palette_manual(self):
        if self._current_palette() is None:
            messagebox.showwarning("내 팔레트",
                                   "먼저 팔레트를 만들거나 고르십시오.")
            return
        lab = self._ask_manual_color("팔레트에 넣을 새 색")
        if lab is None:
            return
        self._add_entry_to_current_palette(lab)

    def _on_palette_entry_rename(self):
        idxs = self._selected_palette_indices()
        if not idxs:
            return
        p = self._current_palette()
        if not p:
            return
        i = idxs[0]
        if i < 0 or i >= len(p['entries']):
            return
        old = p['entries'][i]['name']
        new = simpledialog.askstring("색 이름 바꾸기",
                                     "새 이름:",
                                     initialvalue=old, parent=self)
        if not new:
            return
        new = new.strip()
        if not new:
            return
        p['entries'][i]['name'] = new
        self._save_palettes()
        self._refresh_palette_entries()

    def _on_palette_entry_dup(self):
        idxs = self._selected_palette_indices()
        if not idxs:
            return
        p = self._current_palette()
        if not p:
            return
        i = idxs[0]
        if i < 0 or i >= len(p['entries']):
            return
        src = p['entries'][i]
        dup = {'name': self._auto_entry_name(p), 'lab': tuple(src['lab'])}
        p['entries'].append(dup)
        self._save_palettes()
        self._refresh_palette_entries()

    def _on_palette_entry_delete(self):
        idxs = sorted(self._selected_palette_indices(), reverse=True)
        if not idxs:
            return
        p = self._current_palette()
        if not p:
            return
        if not messagebox.askyesno("지우기",
                                   f"색 {len(idxs)}개를 지울까요?"):
            return
        for i in idxs:
            if 0 <= i < len(p['entries']):
                del p['entries'][i]
        self._save_palettes()
        self._refresh_palette_entries()

    # --- импорт/экспорт ---

    def _on_palette_export(self):
        name = self._current_palette_name()
        if name not in self.palettes:
            return
        target = filedialog.asksaveasfilename(
            title="팔레트 내보내기",
            initialfile=f"{name}.json",
            defaultextension=".json",
            filetypes=[("JSON", "*.json")])
        if not target:
            return
        try:
            data = {
                'name': name,
                'entries': [
                    {'name': e['name'], 'lab': list(e['lab'])}
                    for e in self.palettes[name]['entries']
                ],
            }
            with open(target, 'w', encoding='utf-8') as f:
                json.dump(data, f, indent=2, ensure_ascii=False)
            self.palettes_status.set(f"{target} 로 내보냈습니다")
        except Exception as e:
            messagebox.showerror("오류", str(e))

    def _on_palette_import(self):
        src = filedialog.askopenfilename(
            title="팔레트 가져오기",
            filetypes=[("JSON", "*.json"), ("모든 파일", "*.*")])
        if not src:
            return
        try:
            with open(src, 'r', encoding='utf-8') as f:
                data = json.load(f)
            name = data.get('name') or os.path.splitext(os.path.basename(src))[0]
            entries = data.get('entries', [])
            if name in self.palettes:
                if not messagebox.askyesno(
                        "가져오기",
                        f"팔레트 '{name}' 이(가) 이미 있습니다. 덮어쓸까요?"):
                    return
            self.palettes[name] = {'entries': [
                {'name': e.get('name', 'Color'),
                 'lab': (float(e['lab'][0]), float(e['lab'][1]), float(e['lab'][2]))}
                for e in entries if 'lab' in e
            ]}
            self._save_palettes()
            self._refresh_palette_list()
            self.palettes_tab_selector_var.set(name)
            self._refresh_palette_entries()
            self.palettes_status.set(f"가져왔습니다: {name}")
        except Exception as e:
            messagebox.showerror("오류", str(e))

    def _on_palette_export_all(self):
        target = filedialog.asksaveasfilename(
            title="팔레트 모두 내보내기",
            initialfile="palettes.json",
            defaultextension=".json",
            filetypes=[("JSON", "*.json")])
        if not target:
            return
        try:
            data = {'palettes': [
                {
                    'name': n,
                    'entries': [
                        {'name': e['name'], 'lab': list(e['lab'])}
                        for e in p['entries']
                    ],
                }
                for n, p in self.palettes.items()
            ]}
            with open(target, 'w', encoding='utf-8') as f:
                json.dump(data, f, indent=2, ensure_ascii=False)
            self._set_status(f"{target} 로 내보냈습니다")
        except Exception as e:
            messagebox.showerror("오류", str(e))

    def _on_palette_import_all(self):
        src = filedialog.askopenfilename(
            title="팔레트 가져오기",
            filetypes=[("JSON", "*.json"), ("모든 파일", "*.*")])
        if not src:
            return
        try:
            with open(src, 'r', encoding='utf-8') as f:
                data = json.load(f)
            count = 0
            for p in data.get('palettes', []):
                name = p.get('name', 'Unnamed')
                self.palettes[name] = {'entries': [
                    {'name': e.get('name', 'Color'),
                     'lab': (float(e['lab'][0]), float(e['lab'][1]), float(e['lab'][2]))}
                    for e in p.get('entries', []) if 'lab' in e
                ]}
                count += 1
            self._save_palettes()
            self._refresh_palette_list()
            self._set_status(f"팔레트 {count}개를 가져왔습니다")
        except Exception as e:
            messagebox.showerror("오류", str(e))

    # --- Диалог ручного ввода цвета ---

    def _ask_manual_color(self, title="색 입력", initial=None):
        """
        Lab 값 또는 None 을 돌려준다.
        """
        dlg = tk.Toplevel(self)
        dlg.title(title)
        dlg.transient(self)
        dlg.grab_set()
        dlg.geometry("380x220")

        mode_var = tk.StringVar(value='cmyk')

        ttk.Radiobutton(dlg, text="CMYK", value='cmyk',
                        variable=mode_var).grid(row=0, column=0, padx=8, pady=8, sticky='w')
        ttk.Radiobutton(dlg, text="RGB", value='rgb',
                        variable=mode_var).grid(row=0, column=1, padx=8, pady=8, sticky='w')

        c_var = tk.StringVar(value="0")
        m_var = tk.StringVar(value="0")
        y_var = tk.StringVar(value="0")
        k_var = tk.StringVar(value="0")
        r_var = tk.StringVar(value="128")
        g_var = tk.StringVar(value="128")
        b_var = tk.StringVar(value="128")

        def build_fields():
            for w in dlg.grid_slaves():
                info = w.grid_info()
                if int(info.get('row', -1)) >= 1:
                    w.grid_forget()

            if mode_var.get() == 'cmyk':
                for i, (label, var) in enumerate(
                        (("C %", c_var), ("M %", m_var),
                         ("Y %", y_var), ("K %", k_var))):
                    ttk.Label(dlg, text=label).grid(row=1, column=i*2, padx=4,
                                                    pady=8, sticky='e')
                    ttk.Entry(dlg, textvariable=var, width=8).grid(
                        row=1, column=i*2+1, padx=4, pady=8)
            else:
                for i, (label, var) in enumerate(
                        (("R", r_var), ("G", g_var), ("B", b_var))):
                    ttk.Label(dlg, text=label).grid(row=1, column=i*2, padx=4,
                                                    pady=8, sticky='e')
                    ttk.Entry(dlg, textvariable=var, width=8).grid(
                        row=1, column=i*2+1, padx=4, pady=8)

        mode_var.trace_add('write', lambda *a: build_fields())
        build_fields()

        result = {'lab': None}

        def on_ok():
            try:
                if mode_var.get() == 'cmyk':
                    c = float(c_var.get())
                    m = float(m_var.get())
                    y = float(y_var.get())
                    k = float(k_var.get())
                    result['lab'] = cmyk_to_lab(c, m, y, k)
                else:
                    r = int(r_var.get())
                    g = int(g_var.get())
                    b = int(b_var.get())
                    result['lab'] = srgb_to_lab(r, g, b)
            except Exception as e:
                messagebox.showerror("오류", f"값이 잘못됐습니다: {e}",
                                     parent=dlg)
                return
            dlg.destroy()

        def on_cancel():
            dlg.destroy()

        btns = ttk.Frame(dlg)
        btns.grid(row=3, column=0, columnspan=8, pady=10)
        ttk.Button(btns, text="OK", command=on_ok).pack(side=tk.LEFT, padx=6)
        ttk.Button(btns, text="취소", command=on_cancel).pack(side=tk.LEFT, padx=6)

        self.wait_window(dlg)
        return result['lab']

    # ======================================================================
    #  ВКЛАДКА 3. УСТРОЙСТВО
    # ======================================================================

    def _tab_device(self, nb):
        frame = ttk.Frame(nb, padding=10)
        nb.add(frame, text="기계 정보")

        info = ttk.LabelFrame(frame, text="정보")
        info.pack(fill=tk.X, pady=(0, 8))

        self.dev_text = tk.Text(info, height=12, font=("Consolas", 10),
                                state=tk.DISABLED, wrap=tk.NONE)
        self.dev_text.pack(fill=tk.X, padx=4, pady=4)

        row = ttk.Frame(info)
        row.pack(fill=tk.X, padx=4, pady=(0, 4))
        ttk.Button(row, text="모두 읽기",
                   command=self._on_device_read_all).pack(side=tk.LEFT, padx=2)
        ttk.Button(row, text="배터리",
                   command=self._on_device_battery).pack(side=tk.LEFT, padx=2)
        ttk.Button(row, text="온도",
                   command=self._menu_temperature).pack(side=tk.LEFT, padx=2)
        ttk.Button(row, text="ΔE 설정값",
                   command=self._on_device_deltae).pack(side=tk.LEFT, padx=2)

        mode = ttk.LabelFrame(frame, text="기계 동작 모드(보기만)")
        mode.pack(fill=tk.X, pady=(0, 8))
        self.mode_var = tk.StringVar(value="?")
        ttk.Entry(mode, textvariable=self.mode_var, width=30).pack(side=tk.LEFT, padx=4, pady=4)
        ttk.Button(mode, text="읽기",
                   command=self._on_device_get_mode).pack(side=tk.LEFT, padx=2)

        time_frame = ttk.LabelFrame(frame, text="기계 시각")
        time_frame.pack(fill=tk.X, pady=(0, 8))
        self.time_var = tk.StringVar(value="")
        ttk.Entry(time_frame, textvariable=self.time_var, width=30).pack(
            side=tk.LEFT, padx=4, pady=4)
        ttk.Button(time_frame, text="읽기",
                   command=self._on_device_get_time).pack(side=tk.LEFT, padx=2)
        ttk.Button(time_frame, text="지금 시각으로 맞추기",
                   command=self._on_device_set_time_now).pack(side=tk.LEFT, padx=2)

        ap = ttk.LabelFrame(frame, text="조리개(측정 구멍 크기)")
        ap.pack(fill=tk.X, pady=(0, 8))
        self.ap_var = tk.StringVar(value=AP_LABELS[self.aperture])
        ttk.Combobox(ap, textvariable=self.ap_var,
                     values=AP_LABELS, width=22,
                     state="readonly").pack(side=tk.LEFT, padx=4, pady=4)
        ttk.Button(ap, text="읽기",
                   command=self._on_device_get_aperture).pack(side=tk.LEFT, padx=2)
        ttk.Button(ap, text="맞추기",
                   command=self._on_device_set_aperture).pack(side=tk.LEFT, padx=2)

        svc = ttk.LabelFrame(frame, text="기타")
        svc.pack(fill=tk.X, pady=(0, 8))
        ttk.Button(svc, text="칩 번호",
                   command=self._on_device_chipid).pack(side=tk.LEFT, padx=2)

        self._device_log("준비됐습니다. [모두 읽기]를 누르십시오.")

    def _device_log(self, text, append=True):
        self.dev_text.config(state=tk.NORMAL)
        if not append:
            self.dev_text.delete('1.0', tk.END)
        self.dev_text.insert(tk.END, text + "\n")
        self.dev_text.see(tk.END)
        self.dev_text.config(state=tk.DISABLED)

    def _on_device_read_all(self):
        if not self.connected:
            messagebox.showerror("오류", "연결되어 있지 않습니다")
            return
        self._device_log("--- 모두 읽기 ---", append=False)

        def worker():
            results = []
            checks = [
                ("GetInfo",               "GetInfo"),
                ("GetSerialNum",          "GetSerialNum"),
                ("GetFWInfo",             "GetFWInfo"),
                ("GetBLInfo",             "GetBLInfo"),
                ("GetChipId",             "GetChipId"),
                ("GetBatteryState",       "GetBatteryState"),
                ("GetDeviceMode",         "GetDeviceMode"),
                ("GetTime",               "GetTime"),
                ("GetTimeString",         "GetTimeString"),
                ("GetAperture",           "GetAperture"),
                ("GetCalibrationState",   "GetCalibrationState"),
                ("GetTimeToCalibExpired", "GetTimeToCalibExpired"),
                ("GetDeltaEParameter",    "GetDeltaEParameter"),
                ("MeasureTemperature",    "MeasureTemperature"),
            ]
            for label, fname in checks:
                fn = getattr(rm, fname, None)
                ok, val = try_call(fn)
                if fn is None:
                    results.append(f"{label:24} : <지원 안 함>")
                elif ok:
                    results.append(f"{label:24} : {val!r}")
                else:
                    results.append(f"{label:24} : 오류: {val}")

            self.after(0, lambda: self._device_log("\n".join(results), append=False))
            self.after(0, lambda: self._set_status("기계 정보를 읽었습니다"))

        threading.Thread(target=worker, daemon=True).start()

    def _on_device_battery(self):
        ok, val = try_call(getattr(rm, "GetBatteryState", None))
        self._device_log(f"Battery: {val!r}" if ok else f"Battery: 오류 {val}")

    def _on_device_deltae(self):
        ok, val = try_call(getattr(rm, "GetDeltaEParameter", None))
        self._device_log(f"DeltaE: {val!r}" if ok else f"DeltaE: 오류 {val}")

    def _on_device_get_mode(self):
        ok, val = try_call(getattr(rm, "GetDeviceMode", None))
        if ok:
            self.mode_var.set(str(val))
            self._device_log(f"Mode = {val!r}")
        else:
            self._device_log(f"GetMode: 오류 {val}")

    def _on_device_set_mode(self):
        mode = self.mode_var.get().strip()
        if not mode:
            return
        ok, val = try_call(getattr(rm, "SetDeviceMode", None), mode)
        self._device_log(f"SetMode({mode!r}) -> "
                         + ("OK" if ok else f"오류 {val}"))

    def _on_device_get_time(self):
        ok, val = try_call(getattr(rm, "GetTimeString", None))
        if not ok:
            ok, val = try_call(getattr(rm, "GetTime", None))
        if ok:
            self.time_var.set(str(val))
            self._device_log(f"Time = {val!r}")
        else:
            self._device_log(f"GetTime: 오류 {val}")

    def _on_device_set_time(self):
        t = self.time_var.get().strip()
        if not t:
            return
        ok, val = try_call(getattr(rm, "SetTime", None), t)
        self._device_log(f"SetTime({t!r}) -> " + ("OK" if ok else f"오류 {val}"))

    def _on_device_set_time_now(self):
        now = dt.datetime.now()
        ok, val = try_call(getattr(rm, "SetTime", None), now.year, now.month,
                           now.day, now.hour, now.minute, now.second)
        s = now.strftime("%Y-%m-%d %H:%M:%S")
        if ok and val:
            self.time_var.set(s)
            self._device_log(f"기계 시각을 {s} 로 맞췄습니다")
        else:
            self._device_log(f"기계 시각 맞추기 실패: {val}")

    def _on_device_get_aperture(self):
        ok, val = try_call(getattr(rm, "GetAperture", None))
        if ok:
            if isinstance(val, int) and 0 <= val <= 2:
                self.ap_var.set(AP_LABELS[val])
            self._device_log(f"조리개 = {AP_LABELS[val] if isinstance(val, int) and 0 <= val <= 2 else val!r}")
        else:
            self._device_log(f"GetAperture: 오류 {val}")

    def _on_device_set_aperture(self):
        try:
            ap = int(self.ap_var.get().split()[0])
        except Exception:
            return
        ok, val = try_call(getattr(rm, "SetAperture", None), ap)
        if ok:
            self.aperture = ap
        self._device_log(f"SetAperture({ap}) -> " + ("OK" if ok else f"오류 {val}"))

    def _on_device_chipid(self):
        ok, val = try_call(getattr(rm, "GetChipId", None))
        self._device_log(f"ChipID: {val!r}" if ok else f"ChipID: 오류 {val}")

    # ======================================================================
    #  ВКЛАДКА 4. ФАЙЛЫ
    # ======================================================================

    def _tab_files(self, nb):
        frame = ttk.Frame(nb, padding=10)
        nb.add(frame, text="기계 파일")

        top = ttk.Frame(frame)
        top.pack(fill=tk.X, pady=(0, 6))
        ttk.Button(top, text="목록 새로 고침",
                   command=self._on_files_refresh).pack(side=tk.LEFT, padx=2)
        ttk.Button(top, text="고른 파일 PC로 저장...",
                   command=self._on_files_download).pack(side=tk.LEFT, padx=2)
        ttk.Button(top, text="측정 기록 파일 저장...",
                   command=self._menu_save_dump).pack(side=tk.LEFT, padx=2)

        list_frame = ttk.Frame(frame)
        list_frame.pack(fill=tk.BOTH, expand=True)

        scrollbar = ttk.Scrollbar(list_frame, orient=tk.VERTICAL)
        self.files_list = tk.Listbox(list_frame, font=("Consolas", 10),
                                     yscrollcommand=scrollbar.set)
        scrollbar.config(command=self.files_list.yview)
        self.files_list.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        self.files_status = tk.StringVar(value="[목록 새로 고침]을 누르십시오.")
        ttk.Label(frame, textvariable=self.files_status,
                  padding=(0, 6, 0, 0)).pack(anchor=tk.W)

    def _on_files_refresh(self):
        if not self.connected:
            messagebox.showerror("오류", "연결되어 있지 않습니다")
            return

        def worker():
            fn = getattr(rm, "FileDir", None)
            ok, val = try_call(fn)
            self.after(0, lambda: self._on_files_list(ok, val))

        threading.Thread(target=worker, daemon=True).start()

    def _on_files_list(self, ok, val):
        self.files_list.delete(0, tk.END)
        if not ok:
            self.files_status.set(f"오류: {val}")
            return

        files = val
        if isinstance(files, str):
            lines = files.splitlines()
        elif isinstance(files, (list, tuple)):
            lines = []
            for item in files:
                if isinstance(item, str):
                    lines.append(item)
                elif isinstance(item, dict):
                    size = item.get('size', '')
                    name = item.get('name', item.get('file', ''))
                    lines.append(f"{size:>12}  {name}" if size != '' else str(name))
                else:
                    lines.append(str(item))
        else:
            lines = [str(files)]

        for line in lines:
            self.files_list.insert(tk.END, line)

        self.files_status.set(f"파일 수: {len(lines)}")

    def _get_selected_filename(self):
        sel = self.files_list.curselection()
        if not sel:
            return None
        line = self.files_list.get(sel[0])
        parts = line.strip().split()
        if not parts:
            return None
        return parts[-1]

    def _on_files_download(self):
        name = self._get_selected_filename()
        if not name:
            messagebox.showwarning("파일", "목록에서 파일을 고르십시오")
            return
        target = filedialog.asksaveasfilename(
            title="다른 이름으로 저장", initialfile=name)
        if not target:
            return

        def worker():
            fn = getattr(rm, "FetchFile", None) or getattr(rm, "DownloadFile", None)
            ok, val = try_call(fn, name)
            if not ok:
                self.after(0, lambda: messagebox.showerror("오류", str(val)))
                return
            try:
                with open(target, 'wb') as f:
                    f.write(val)
                self.after(0, lambda: self.files_status.set(
                    f"{len(val)} 바이트를 {target} 에 저장했습니다"))
            except Exception as e:
                self.after(0, lambda e=e: messagebox.showerror("오류", str(e)))

        threading.Thread(target=worker, daemon=True).start()

    def _on_files_upload(self):
        src = filedialog.askopenfilename(title="올릴 파일 고르기")
        if not src:
            return
        name = os.path.basename(src)
        if not messagebox.askyesno("올리기",
                                   f"{name} 을(를) RM200 에 올릴까요?\n"
                                   f"(같은 이름 파일을 덮어쓸 수 있습니다)"):
            return

        def worker():
            try:
                with open(src, 'rb') as f:
                    data = f.read()
            except Exception as e:
                self.after(0, lambda e=e: messagebox.showerror("오류", str(e)))
                return
            fn = getattr(rm, "PutFile", None) or getattr(rm, "UploadFile", None)
            if fn is None:
                self.after(0, lambda: messagebox.showerror(
                    "오류", "올리기 기능 없음"))
                return
            try:
                if fn.__name__ == "PutFile":
                    ok, val = try_call(fn, name, data)
                else:
                    ok, val = try_call(fn, name)
                self.after(0, lambda: self.files_status.set(
                    f"올리기 {name}: " + ("OK" if ok else f"오류 {val}")))
            except Exception as e:
                self.after(0, lambda e=e: messagebox.showerror("오류", str(e)))

        threading.Thread(target=worker, daemon=True).start()

    def _on_files_delete(self):
        name = self._get_selected_filename()
        if not name:
            messagebox.showwarning("파일", "목록에서 파일을 고르십시오")
            return
        if not messagebox.askyesno("지우기", f"기계에서 {name} 을(를) 지울까요?"):
            return
        ok, val = try_call(getattr(rm, "FileDelete", None), name)
        self.files_status.set(f"지우기 {name}: " + ("OK" if ok else f"오류 {val}"))

    # ======================================================================
    #  ВКЛАДКА 5. FAN DECKS
    # ======================================================================

    def _tab_fandecks(self, nb):
        frame = ttk.Frame(nb, padding=10)
        nb.add(frame, text="팬덱(색 견본 책)")

        top = ttk.Frame(frame)
        top.pack(fill=tk.X, pady=(0, 6))
        ttk.Button(top, text="목록 새로 고침",
                   command=self._on_fd_refresh).pack(side=tk.LEFT, padx=2)
        ttk.Button(top, text="고른 팬덱 켜기",
                   command=self._on_fd_activate).pack(side=tk.LEFT, padx=2)
        ttk.Button(top, text="고른 팬덱 끄기",
                   command=self._on_fd_deactivate).pack(side=tk.LEFT, padx=2)

        list_frame = ttk.Frame(frame)
        list_frame.pack(fill=tk.BOTH, expand=True)

        scrollbar = ttk.Scrollbar(list_frame, orient=tk.VERTICAL)
        self.fd_list = tk.Listbox(list_frame, font=("Consolas", 10),
                                  yscrollcommand=scrollbar.set)
        scrollbar.config(command=self.fd_list.yview)
        self.fd_list.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        self.fd_status = tk.StringVar(value="[목록 새로 고침]을 누르십시오.")
        ttk.Label(frame, textvariable=self.fd_status,
                  padding=(0, 6, 0, 0)).pack(anchor=tk.W)

    def _on_fd_refresh(self):
        if not self.connected:
            messagebox.showerror("오류", "연결되어 있지 않습니다")
            return

        def worker():
            ok, val = try_call(getattr(rm, "GetFandecks", None))
            self.after(0, lambda: self._on_fd_list(ok, val))

        threading.Thread(target=worker, daemon=True).start()

    def _on_fd_list(self, ok, val):
        self.fd_list.delete(0, tk.END)
        if not ok:
            self.fd_status.set(f"오류: {val}")
            return
        items = val if isinstance(val, (list, tuple)) else [val]
        for it in items:
            self.fd_list.insert(tk.END, str(it))
        self.fd_status.set(f"Fan decks: {len(items)}")

    def _selected_fd(self):
        sel = self.fd_list.curselection()
        if not sel:
            return None
        return self.fd_list.get(sel[0]).strip().split()[-1]

    def _on_fd_activate(self):
        name = self._selected_fd()
        if not name:
            return
        ok, val = try_call(getattr(rm, "SetFandeckActive", None), name, True)
        self.fd_status.set(f"켜기 {name}: " + ("OK" if ok else f"오류 {val}"))
        self._on_fd_refresh()

    def _on_fd_deactivate(self):
        name = self._selected_fd()
        if not name:
            return
        ok, val = try_call(getattr(rm, "SetFandeckActive", None), name, False)
        self.fd_status.set(f"끄기 {name}: " + ("OK" if ok else f"오류 {val}"))
        self._on_fd_refresh()

    def _on_fd_delete(self):
        name = self._selected_fd()
        if not name:
            return
        if not messagebox.askyesno("지우기", f"견본 책 {name} 을(를) 지울까요?"):
            return
        ok, val = try_call(getattr(rm, "DeleteFandeck", None), name)
        self.fd_status.set(f"지우기 {name}: " + ("OK" if ok else f"오류 {val}"))
        self._on_fd_refresh()

    def _on_fd_add(self):
        src = filedialog.askopenfilename(
            title="팬덱 파일(.fdk) 고르기",
            filetypes=[("Fan Deck", "*.fdk"), ("모든 파일", "*.*")])
        if not src:
            return
        name = os.path.basename(src)
        if not messagebox.askyesno("팬덱 추가",
                                   f"'{name}' 을(를) RM200 에 올릴까요?"):
            return

        def worker():
            try:
                with open(src, 'rb') as f:
                    data = f.read()
            except Exception as e:
                self.after(0, lambda e=e: messagebox.showerror("오류", str(e)))
                return

            fn = getattr(rm, "PutFile", None)
            if fn is None:
                self.after(0, lambda: messagebox.showerror(
                    "오류", "올리기 기능 없음"))
                return

            ok, val = try_call(fn, name, data)
            if ok:
                self.after(0, lambda: self.fd_status.set(
                    f"팬덱 '{name}' 을(를) 올렸습니다. [목록 새로 고침]을 누르십시오."))
                self.after(0, self._on_fd_refresh)
            else:
                self.after(0, lambda: self.fd_status.set(
                    f"올리기 오류: {val}"))

        threading.Thread(target=worker, daemon=True).start()

    # ======================================================================
    #  ВКЛАДКА 6. КАЛИБРОВКА
    # ======================================================================

    def _tab_calibration(self, nb):
        frame = ttk.Frame(nb, padding=10)
        nb.add(frame, text="교정")

        info = ttk.LabelFrame(frame, text="상태")
        info.pack(fill=tk.X, pady=(0, 8))

        self.cal_text = tk.Text(info, height=10, font=("Consolas", 10),
                                state=tk.DISABLED, wrap=tk.NONE)
        self.cal_text.pack(fill=tk.X, padx=4, pady=4)

        row = ttk.Frame(info)
        row.pack(fill=tk.X, padx=4, pady=(0, 4))
        ttk.Button(row, text="교정 상태 보기",
                   command=self._on_cal_state).pack(side=tk.LEFT, padx=2)
        ttk.Button(row, text="교정 만료까지 남은 시간",
                   command=self._on_cal_expiry).pack(side=tk.LEFT, padx=2)
        tk.Button(frame, text="PC에서 0점 맞추기(교정)", command=self._auto_calibrate,
                  font=('맑은 고딕', 13, 'bold'), bg='#1e6fd9', fg='white', relief=tk.FLAT,
                  activebackground='#1557b0', activeforeground='white', cursor='hand2',
                  padx=18, pady=8).pack(anchor='w', pady=(0, 10))


        vers = ttk.LabelFrame(frame, text="Versions.dat")
        vers.pack(fill=tk.X, pady=(0, 8))
        ttk.Button(vers, text="버전 목록(Versions.dat) 읽기",
                   command=self._on_cal_read_versions).pack(side=tk.LEFT, padx=2)

        self._cal_log("준비됐습니다.")

    def _cal_log(self, text, append=True):
        self.cal_text.config(state=tk.NORMAL)
        if not append:
            self.cal_text.delete('1.0', tk.END)
        self.cal_text.insert(tk.END, text + "\n")
        self.cal_text.see(tk.END)
        self.cal_text.config(state=tk.DISABLED)

    def _on_cal_state(self):
        ok, val = try_call(getattr(rm, "GetCalibrationState", None))
        self._cal_log(f"CalibState: {val!r}" if ok else f"오류: {val}")

    def _on_cal_expiry(self):
        ok, val = try_call(getattr(rm, "GetTimeToCalibExpired", None))
        self._cal_log(f"TimeToCalibExpired: {val!r}" if ok else f"오류: {val}")

    def _on_cal_backup(self):
        try:
            mode = int(self.cal_mode_var.get())
        except Exception:
            mode = 0
        ok, val = try_call(getattr(rm, "BackupCalibData", None), mode)
        self._cal_log(f"BackupCalibData({mode}) -> "
                      + ("OK" if ok else f"오류 {val}"))

    def _on_cal_read_versions(self):
        def worker():
            fn = getattr(rm, "ReadVersionsDotDat", None)
            ok, val = try_call(fn)
            if not ok:
                self.after(0, lambda: self._cal_log(f"오류: {val}"))
                return
            self.after(0, lambda: self._cal_log(repr(val)[:2000], append=False))

        threading.Thread(target=worker, daemon=True).start()

    # ======================================================================
    #  ВКЛАДКА 7. ЭКРАН И КЛАВИАТУРА
    # ======================================================================

    def _tab_screen_keys(self, nb):
        frame = ttk.Frame(nb, padding=10)
        nb.add(frame, text="기계 화면")

        screen = ttk.LabelFrame(frame, text="기계 화면(LCD)")
        screen.pack(fill=tk.X, pady=(0, 8))
        ttk.Button(screen, text="화면 사진 저장...",
                   command=self._on_screen_screenshot).pack(side=tk.LEFT, padx=4, pady=4)
        ttk.Button(screen, text="화면 원자료(기록창)",
                   command=self._on_screen_lcd_data).pack(side=tk.LEFT, padx=4, pady=4)
        ttk.Button(screen, text="화면 사진 창으로 보기",
                   command=self._on_screen_show).pack(side=tk.LEFT, padx=4, pady=4)

        # Ver 0.22: 이 칸 안에서 기계 화면 보며 단추 누르기
        rbox = tk.Frame(frame, bg='#ffffff', highlightthickness=1, highlightbackground='#d5dbe5')
        rbox.pack(fill=tk.X, pady=(0, 8))
        self._rm_tab_id = str(frame)
        rleft = tk.Frame(rbox, bg='#ffffff'); rleft.pack(side=tk.LEFT, anchor='n')
        self._rm_tab_panel = self._rm_build(
            rleft, "기계 원격 단추: 기계 화면이 1초마다 보입니다.\n"
                   "단추, 키보드 화살표·Enter, 화면 위 마우스 휠로 기계 메뉴(설정·찾기·팬덱 등)를 움직입니다.")
        rright = tk.Frame(rbox, bg='#ffffff'); rright.pack(side=tk.LEFT, fill=tk.BOTH, expand=True,
                                                           padx=(6, 12), pady=10)
        self._devmenu_build(rright)
        self.after(1500, lambda: self._remote_poll(self._rm_tab_panel))
        self.keys_log = tk.Text(frame, height=4, font=("Consolas", 10),
                                state=tk.DISABLED, wrap=tk.NONE)
        self.keys_log.pack(fill=tk.BOTH, expand=True)

    def _keys_print(self, text):
        self.keys_log.config(state=tk.NORMAL)
        self.keys_log.insert(tk.END, text + "\n")
        self.keys_log.see(tk.END)
        self.keys_log.config(state=tk.DISABLED)

    def _on_screen_screenshot(self):
        target = filedialog.asksaveasfilename(
            title="화면 사진 저장", initialfile="screenshot.png",
            defaultextension=".png",
            filetypes=[("PNG", "*.png"), ("BMP", "*.bmp"), ("모든 파일", "*.*")])
        if not target:
            return

        def worker():
            fn = getattr(rm, "SaveScreenshot", None)
            ok, val = try_call(fn, target)
            if not ok:
                self.after(0, lambda: self._keys_print(f"SaveScreenshot: {val}"))
                return
            self.after(0, lambda: self._keys_print(f"Screenshot: {target}"))

        threading.Thread(target=worker, daemon=True).start()

    def _on_screen_show(self):
        if not HAS_PIL:
            messagebox.showerror("오류", "Pillow(그림 부품)가 없습니다")
            return

        target = filedialog.asksaveasfilename(
            title="임시 화면 사진", initialfile="temp_screen.bmp",
            defaultextension=".bmp",
            filetypes=[("BMP", "*.bmp")])
        if not target:
            return

        def worker():
            fn = getattr(rm, "SaveScreenshot", None)
            ok, val = try_call(fn, target)
            if not ok:
                self.after(0, lambda: messagebox.showerror("오류", str(val)))
                return

            try:
                img = Image.open(target)
                img = img.resize((640, 480), Image.NEAREST)
                photo = ImageTk.PhotoImage(img)

                top = tk.Toplevel(self)
                top.title("기계 화면 사진")
                label = ttk.Label(top, image=photo)
                label.image = photo
                label.pack()
            except Exception as e:
                self.after(0, lambda e=e: messagebox.showerror("오류", str(e)))

        threading.Thread(target=worker, daemon=True).start()

    def _on_screen_lcd_data(self):
        def worker():
            fn = getattr(rm, "GetLcdData", None)
            ok, val = try_call(fn)
            if ok:
                if isinstance(val, (bytes, bytearray)):
                    self.after(0, lambda: self._keys_print(
                        f"화면 원자료: {len(val)} 바이트"))
                else:
                    self.after(0, lambda: self._keys_print(
                        f"GetLcdData: {str(val)[:500]}"))
            else:
                self.after(0, lambda: self._keys_print(f"오류: {val}"))

        threading.Thread(target=worker, daemon=True).start()

    def _on_key_press(self, code):
        def worker():
            fn = getattr(rm, "GenerateKeyboardEvent", None)
            ok, val = try_call(fn, code)
            if ok:
                self.after(0, lambda: self._keys_print(
                    f"GenerateKeyboardEvent({code}) -> OK"))
            else:
                self.after(0, lambda: self._keys_print(
                    f"GenerateKeyboardEvent({code}) -> 오류: {val}"))

        threading.Thread(target=worker, daemon=True).start()

    def _on_keys_get_code(self):
        fn = getattr(rm, "GetKeyCode", None)
        ok, val = try_call(fn)
        if ok:
            self._keys_print(f"GetKeyCode: {val:#x} ({val})")
        else:
            self._keys_print(f"단추 상태 오류: {val}")

    # ======================================================================
    #  ВКЛАДКА 8. PREVIEW
    # ======================================================================

    # ======================================================================
    #  Ver 0.9: 팬톤 색 보기
    # ======================================================================
    SW_W, SW_H, SW_GAP = 86, 64, 6

    # ======================================================================
    #  Ver 0.21: 이색 관리 장부 (CM 기준색 대비 입고마다 ΔE 기록)
    # ======================================================================
    CM_FILE = None

    def _cm_path(self):
        return os.path.join(os.path.dirname(os.path.abspath(PALETTES_FILE)), 'cm_log.json')

    def _cm_load(self):
        import shutil
        self.cm = {'items': []}
        path = self._cm_path()
        if os.path.exists(path):
            try:
                with open(path, encoding='utf-8') as f:
                    self.cm = json.load(f)
            except Exception:
                try:
                    shutil.copy2(path, path + dt.datetime.now().strftime('.손상_%Y%m%d_%H%M%S.json'))
                except Exception:
                    pass
                self.cm = {'items': []}

    def _cm_save(self):
        path = self._cm_path()
        try:
            tmp = path + '.tmp'
            with open(tmp, 'w', encoding='utf-8') as f:
                json.dump(self.cm, f, indent=1, ensure_ascii=False)
            if os.path.exists(path):
                try:
                    os.replace(path, path + '.bak')
                except Exception:
                    pass
            os.replace(tmp, path)
            self._cloud_kick()
        except Exception as e:
            messagebox.showerror("이색 관리", f"저장하지 못했습니다: {e}")

    def _tab_cm(self, nb):
        self._cm_load()
        frame = ttk.Frame(nb, padding=8)
        nb.add(frame, text="이색 관리")
        top = ttk.Frame(frame); top.pack(fill=tk.X)
        ttk.Label(top, text="관리 색:", font=('맑은 고딕', 11)).pack(side=tk.LEFT)
        self.cm_var = tk.StringVar()
        self.cm_combo = ttk.Combobox(top, textvariable=self.cm_var, state='readonly', width=26,
                                     font=('맑은 고딕', 11))
        self.cm_combo.pack(side=tk.LEFT, padx=(4, 10))
        self.cm_combo.bind('<<ComboboxSelected>>', lambda e: self._cm_refresh())
        ttk.Button(top, text="관리 색 추가 (왼쪽 기준색으로)", command=self._cm_add_item).pack(side=tk.LEFT, padx=3)
        ttk.Button(top, text="관리 색 지우기", command=self._cm_del_item).pack(side=tk.LEFT, padx=3)
        ttk.Label(top, text="   합격 ΔE ≤", font=('맑은 고딕', 11)).pack(side=tk.LEFT)
        self.cm_ok = tk.StringVar(value="1.0")
        ttk.Entry(top, textvariable=self.cm_ok, width=5).pack(side=tk.LEFT, padx=2)
        ttk.Label(top, text=" 주의 ≤", font=('맑은 고딕', 11)).pack(side=tk.LEFT)
        self.cm_warn = tk.StringVar(value="2.0")
        ttk.Entry(top, textvariable=self.cm_warn, width=5).pack(side=tk.LEFT, padx=2)
        ttk.Button(top, text="기준 저장", command=self._cm_save_tol).pack(side=tk.LEFT, padx=3)
        act = ttk.Frame(frame); act.pack(fill=tk.X, pady=(8, 4))
        tk.Button(act, text="오른쪽 비교색(새 입고)을 장부에 기록", command=self._cm_record,
                  relief=tk.FLAT, padx=14, pady=4, font=('맑은 고딕', 11, 'bold'), bg='#1e6fd9', fg='white',
                  activebackground='#1559b0', activeforeground='white', cursor='hand2').pack(side=tk.LEFT)
        ttk.Button(act, text="고른 기록 지우기", command=self._cm_del_rec).pack(side=tk.LEFT, padx=8)
        ttk.Button(act, text="엑셀로 내보내기...", command=self._cm_export).pack(side=tk.LEFT, padx=3)
        self.cm_info = tk.StringVar(value="")
        ttk.Label(frame, textvariable=self.cm_info, font=('맑은 고딕', 10), foreground='#555').pack(anchor='w')
        body = ttk.Frame(frame); body.pack(fill=tk.BOTH, expand=True, pady=(4, 0))
        cols = ('date', 'lot', 'n', 'dE', 'dL', 'da', 'db', 'verdict', 'dir')
        self.cm_tree = ttk.Treeview(body, columns=cols, show='headings', height=9, selectmode='extended')
        for c, t, w in (('date', '날짜', 140), ('lot', '입고 번호·메모', 150), ('n', '잰 횟수', 60),
                        ('dE', 'ΔE2000', 70), ('dL', 'ΔL 밝기', 70), ('da', 'Δa 빨강', 70),
                        ('db', 'Δb 노랑', 70), ('verdict', '판정', 60), ('dir', '어느 쪽으로', 220)):
            self.cm_tree.heading(c, text=t)
            self.cm_tree.column(c, width=w, anchor='w' if c in ('date', 'lot', 'dir') else 'center')
        for tg, bg in (('ok', '#e6f4e6'), ('warn', '#fff3e0'), ('bad', '#fde4e4')):
            self.cm_tree.tag_configure(tg, background=bg)
        self.cm_tree.pack(side=tk.TOP, fill=tk.X)
        self.cm_chart = tk.Canvas(body, height=210, bg='#ffffff', highlightthickness=1,
                                  highlightbackground='#d5dbe5')
        self.cm_chart.pack(side=tk.TOP, fill=tk.BOTH, expand=True, pady=(8, 0))
        self.cm_chart.bind('<Configure>', lambda e: self._cm_draw_chart())
        self._cm_fill_combo()

    def _cm_item(self):
        n = self.cm_var.get()
        for it in self.cm['items']:
            if it['name'] == n:
                return it
        return None

    def _cm_fill_combo(self, select=None):
        names = [it['name'] for it in self.cm['items']]
        self.cm_combo['values'] = names
        if select in names:
            self.cm_var.set(select)
        elif self.cm_var.get() not in names:
            self.cm_var.set(names[0] if names else '')
        self._cm_refresh()

    def _cm_tol(self, it=None):
        it = it or self._cm_item() or {}
        return float(it.get('ok', 1.0)), float(it.get('warn', 2.0))

    @staticmethod
    def _cm_dir(dL, da, db):
        out = []
        if abs(dL) >= 0.5:
            out.append("더 밝음" if dL > 0 else "더 어두움")
        if abs(da) >= 0.5:
            out.append("더 붉음" if da > 0 else "더 초록빛")
        if abs(db) >= 0.5:
            out.append("더 누러움" if db > 0 else "더 푸름")
        return ", ".join(out) or "거의 같음"

    def _cm_refresh(self):
        it = self._cm_item()
        self.cm_tree.delete(*self.cm_tree.get_children())
        if not it:
            self.cm_info.set("관리 색이 없습니다. 측정·비교 왼쪽에 기준 견본(마스터)을 재 넣고 [관리 색 추가]를 누르십시오.")
            self._cm_draw_chart()
            return
        ok, warn = self._cm_tol(it)
        self.cm_ok.set(f"{ok:g}"); self.cm_warn.set(f"{warn:g}")
        L, a, b = it['master']
        self.cm_info.set(f"기준(마스터) {it['name']}: L {L:.2f}  a {a:.2f}  b {b:.2f}   "
                         f"(등록 {it.get('created', '')})   기록 {len(it['records'])}개")
        for i, r in enumerate(it['records']):
            v = '합격' if r['dE'] <= ok else '주의' if r['dE'] <= warn else '불합격'
            tg = {'합격': 'ok', '주의': 'warn', '불합격': 'bad'}[v]
            self.cm_tree.insert('', 'end', iid=str(i), tags=(tg,), values=(
                r['date'], r.get('lot', ''), r.get('n', 1), f"{r['dE']:.2f}", f"{r['dL']:+.2f}",
                f"{r['da']:+.2f}", f"{r['db']:+.2f}", v, self._cm_dir(r['dL'], r['da'], r['db'])))
        self._cm_draw_chart()

    def _cm_draw_chart(self):
        c = getattr(self, 'cm_chart', None)
        if c is None:
            return
        c.delete('all')
        it = self._cm_item()
        W = max(300, c.winfo_width()); H = max(150, c.winfo_height())
        if not it or not it['records']:
            c.create_text(W / 2, H / 2, text="기록이 쌓이면 여기에 ΔE 변화 그래프가 나옵니다",
                          fill='#999', font=('맑은 고딕', 11))
            return
        ok, warn = self._cm_tol(it)
        rs = it['records']
        ymax = max(warn * 1.5, max(r['dE'] for r in rs) * 1.15, 1.0)
        x0, x1, y0, y1 = 60, W - 20, 20, H - 30

        def Y(v):
            return y1 - (y1 - y0) * v / ymax
        c.create_rectangle(x0, Y(ok), x1, y1, fill='#eef8ee', outline='')
        c.create_rectangle(x0, Y(warn), x1, Y(ok), fill='#fff6e6', outline='')
        c.create_rectangle(x0, y0, x1, Y(warn), fill='#fdeeee', outline='')
        c.create_line(x0, y1, x1, y1, fill='#888'); c.create_line(x0, y0, x0, y1, fill='#888')
        for v, t in ((0, '0'), (ok, f"합격 {ok:g}"), (warn, f"주의 {warn:g}")):
            c.create_line(x0, Y(v), x1, Y(v), fill='#bbb', dash=(3, 3))
            c.create_text(x0 - 4, Y(v), text=t, anchor='e', font=('맑은 고딕', 8), fill='#555')
        n = len(rs)
        pts = []
        for i, r in enumerate(rs):
            x = x0 + 20 + (x1 - x0 - 40) * (i / max(1, n - 1)) if n > 1 else (x0 + x1) / 2
            pts.append((x, Y(r['dE'])))
        if n > 1:
            c.create_line(*[v for p in pts for v in p], fill='#1e6fd9', width=2)
        for (x, y), r in zip(pts, rs):
            col = '#2e7d32' if r['dE'] <= ok else '#ef6c00' if r['dE'] <= warn else '#c62828'
            c.create_oval(x - 5, y - 5, x + 5, y + 5, fill=col, outline='white')
            c.create_text(x, y1 + 12, text=r['date'][5:10], font=('맑은 고딕', 8), fill='#555')
        c.create_text(x0, 8, anchor='w', text="입고마다 기준색과의 차이 ΔE2000 (낮을수록 같음)",
                      font=('맑은 고딕', 9, 'bold'), fill='#1e3a5f')

    def _cm_add_item(self):
        ms = self.state_data['ref']['measurements']
        if not ms:
            messagebox.showinfo("관리 색 추가",
                                "먼저 [측정·비교] 왼쪽 기준색에 처음 승인받은 견본(마스터)을\n"
                                "여러 군데 재서 넣으십시오. 그 평균이 기준이 됩니다.")
            return
        name = simpledialog.askstring("관리 색 추가", "관리 색 이름 (예: CM-A 오크):", parent=self)
        if not name or not name.strip():
            return
        name = name.strip()
        if any(it['name'] == name for it in self.cm['items']):
            messagebox.showwarning("관리 색 추가", "같은 이름이 이미 있습니다.")
            return
        L, a, b = (sum(m[i] for m in ms) / len(ms) for i in range(3))
        self.cm['items'].append({'name': name, 'master': [L, a, b], 'n': len(ms),
                                 'created': dt.datetime.now().strftime('%Y-%m-%d %H:%M'),
                                 'ok': 1.0, 'warn': 2.0, 'records': []})
        self._cm_save()
        self._cm_fill_combo(select=name)
        self._set_status(f"관리 색 '{name}' 을(를) 기준 {len(ms)}회 평균으로 등록했습니다")

    def _cm_del_item(self):
        it = self._cm_item()
        if not it:
            return
        if not messagebox.askyesno("관리 색 지우기",
                                   f"'{it['name']}' 과 기록 {len(it['records'])}개를 지울까요?"):
            return
        self.cm['items'].remove(it)
        self._cm_save()
        self._cm_fill_combo()

    def _cm_save_tol(self):
        it = self._cm_item()
        if not it:
            return
        try:
            ok = float(self.cm_ok.get()); warn = float(self.cm_warn.get())
            if not (0 < ok <= warn):
                raise ValueError
        except Exception:
            messagebox.showerror("이색 관리", "합격 값은 0보다 크고 주의 값보다 작거나 같아야 합니다.")
            return
        it['ok'], it['warn'] = ok, warn
        self._cm_save()
        self._cm_refresh()

    def _cm_record(self):
        it = self._cm_item()
        if not it:
            messagebox.showinfo("이색 관리", "먼저 관리 색을 추가하거나 고르십시오.")
            return
        ms = self.state_data['smp']['measurements']
        if not ms:
            messagebox.showinfo("이색 관리", "[측정·비교] 오른쪽 비교색에 새로 들어온 물건을 재 넣으십시오.")
            return
        lot = simpledialog.askstring("장부에 기록", "입고 번호나 메모 (없으면 비워 두십시오):", parent=self)
        if lot is None:
            return
        L, a, b = (sum(m[i] for m in ms) / len(ms) for i in range(3))
        mL, ma, mb = it['master']
        dE = de2000(mL, ma, mb, L, a, b)
        it['records'].append({'date': dt.datetime.now().strftime('%Y-%m-%d %H:%M'), 'lot': lot.strip(),
                              'lab': [L, a, b], 'n': len(ms), 'dE': dE,
                              'dL': L - mL, 'da': a - ma, 'db': b - mb})
        self._cm_save()
        self._cm_refresh()
        ok, warn = self._cm_tol(it)
        v = '합격' if dE <= ok else '주의' if dE <= warn else '불합격'
        self._set_status(f"'{it['name']}' 장부에 기록했습니다: ΔE {dE:.2f} ({v})")

    def _cm_del_rec(self):
        it = self._cm_item()
        sel = sorted((int(i) for i in self.cm_tree.selection()), reverse=True)
        if not it or not sel:
            return
        if not messagebox.askyesno("기록 지우기", f"고른 기록 {len(sel)}개를 지울까요?"):
            return
        for i in sel:
            del it['records'][i]
        self._cm_save()
        self._cm_refresh()

    def _cm_export(self, path=None):
        it = self._cm_item()
        if not it:
            return
        if path is None:
            path = filedialog.asksaveasfilename(
                title="엑셀로 내보내기", defaultextension=".csv",
                initialfile=f"이색관리_{it['name']}_{dt.datetime.now():%Y%m%d}.csv",
                filetypes=[("엑셀에서 열리는 CSV", "*.csv")])
        if not path:
            return
        import csv
        ok, warn = self._cm_tol(it)
        with open(path, 'w', encoding='utf-8-sig', newline='') as f:
            w = csv.writer(f)
            L, a, b = it['master']
            w.writerow(['관리 색', it['name'], '기준 L', f"{L:.3f}", '기준 a', f"{a:.3f}", '기준 b', f"{b:.3f}",
                        '합격 ΔE≤', ok, '주의 ΔE≤', warn])
            w.writerow([])
            w.writerow(['날짜', '입고 번호·메모', '잰 횟수', 'L', 'a', 'b', 'ΔE2000', 'ΔL', 'Δa', 'Δb', '판정', '어느 쪽으로'])
            for r in it['records']:
                v = '합격' if r['dE'] <= ok else '주의' if r['dE'] <= warn else '불합격'
                w.writerow([r['date'], r.get('lot', ''), r.get('n', 1)] + [f"{x:.3f}" for x in r['lab']] +
                           [f"{r['dE']:.2f}", f"{r['dL']:+.2f}", f"{r['da']:+.2f}", f"{r['db']:+.2f}", v,
                            self._cm_dir(r['dL'], r['da'], r['db'])])
        self._set_status(f"내보냈습니다: {path}")

    def _tab_pantone(self, nb):
        frame = ttk.Frame(nb, padding=8)
        nb.add(frame, text="팬톤 색 보기")
        nb.insert(2, frame)
        decks = pantone_decks()
        top = ttk.Frame(frame); top.pack(fill=tk.X)
        ttk.Label(top, text="팬덱:", font=('맑은 고딕', 11)).pack(side=tk.LEFT)
        names = ['모든 팬덱'] + [f"{d['ko']}  ({len(d['colors'])}색)" for d in decks]
        self.pt_deck_var = tk.StringVar(value=names[1] if len(names) > 1 else names[0])
        cb = ttk.Combobox(top, textvariable=self.pt_deck_var, values=names, state='readonly',
                          width=34, font=('맑은 고딕', 11))
        cb.pack(side=tk.LEFT, padx=(4, 14))
        cb.bind('<<ComboboxSelected>>', lambda e: self._pt_fill())
        ttk.Label(top, text="번호·이름 찾기:", font=('맑은 고딕', 11)).pack(side=tk.LEFT)
        self.pt_q = tk.StringVar()
        ent = ttk.Entry(top, textvariable=self.pt_q, width=18, font=('맑은 고딕', 11))
        ent.pack(side=tk.LEFT, padx=4)
        ent.bind('<Return>', lambda e: self._pt_fill())
        ttk.Button(top, text="찾기", command=self._pt_fill).pack(side=tk.LEFT, padx=(0, 14))
        ttk.Button(top, text="비교색과 가장 가까운 팬톤", command=lambda: self._pt_nearest('smp')).pack(side=tk.LEFT, padx=2)
        ttk.Button(top, text="기준색과 가장 가까운 팬톤", command=lambda: self._pt_nearest('ref')).pack(side=tk.LEFT, padx=2)
        self.pt_info = tk.StringVar(value="")
        ttk.Label(frame, textvariable=self.pt_info, font=('맑은 고딕', 10), foreground='#555').pack(fill=tk.X, pady=(6, 2))
        body = ttk.Frame(frame); body.pack(fill=tk.BOTH, expand=True)
        self.pt_canvas = tk.Canvas(body, bg='#ffffff', highlightthickness=0)
        sb = ttk.Scrollbar(body, orient=tk.VERTICAL, command=self.pt_canvas.yview)
        self.pt_canvas.configure(yscrollcommand=sb.set)
        sb.pack(side=tk.RIGHT, fill=tk.Y); self.pt_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.pt_canvas.bind('<Configure>', lambda e: self._pt_layout())
        self.pt_canvas.bind_all('<MouseWheel>', self._pt_wheel, add='+')
        side = tk.Frame(body, width=260, bg='#f4f6fa'); side.pack(side=tk.RIGHT, fill=tk.Y, padx=(8, 0))
        side.pack_propagate(False)
        self.pt_big = tk.Canvas(side, width=240, height=150, bg='#ffffff', highlightthickness=1,
                                highlightbackground='#ccc')
        self.pt_big.pack(padx=10, pady=(10, 6))
        self.pt_sel_var = tk.StringVar(value="색 칸을 누르면\n여기에 자세히 나옵니다")
        tk.Label(side, textvariable=self.pt_sel_var, bg='#f4f6fa', justify=tk.LEFT, anchor='w',
                 font=('맑은 고딕', 10), wraplength=240).pack(fill=tk.X, padx=10)
        for txt, cmd in (("기준색으로 넣기", lambda: self._pt_put('ref')),
                         ("비교색으로 넣기", lambda: self._pt_put('smp')),
                         ("내 팔레트에 넣기", self._pt_to_palette)):
            ttk.Button(side, text=txt, command=cmd).pack(fill=tk.X, padx=10, pady=3)
        tk.Label(side, text="화면 색은 모니터에 따라 조금 달라 보입니다.\n"
                            "비교 숫자는 공식 L·a·b 값으로 계산합니다.",
                 bg='#f4f6fa', fg='#777', justify=tk.LEFT, font=('맑은 고딕', 9),
                 wraplength=240).pack(side=tk.BOTTOM, fill=tk.X, padx=10, pady=10)
        self.pt_items = []
        self.pt_sel = None
        self.pt_hits = None
        self.after(200, self._pt_fill)

    def _pt_wheel(self, e):
        try:
            if str(self._notebook.select()) != str(self._notebook.tabs()[2]):
                return
            self.pt_canvas.yview_scroll(int(-e.delta / 120) * 3, 'units')
        except Exception:
            pass

    def _pt_current_colors(self):
        decks = pantone_decks()
        v = self.pt_deck_var.get()
        out = []
        for d in decks:
            if v == '모든 팬덱' or v.startswith(d['ko'] + '  ('):
                out += [(c, d) for c in d['colors']]
        return out

    def _pt_fill(self, items=None, info=None):
        if items is None:
            q = self.pt_q.get().strip().lower().replace('pantone', '').replace('®', '').strip()
            items = self._pt_current_colors()
            if q:
                items = [(c, d) for c, d in items if q in c[0].lower()]
            self.pt_hits = None
            self.pt_cmp = None
        self.pt_items = items
        if info is None:
            info = f"{len(items)}색"
            if items:
                d0 = items[0][1]
                if all(d is d0 for _, d in items):
                    info += f"  ·  {d0['name']}  판 {d0['version']} ({d0['date']})"
        self.pt_info.set(info)
        self._pt_layout()

    def _pt_layout(self):
        c = self.pt_canvas
        c.delete('all')
        W = max(200, c.winfo_width())
        cols = max(1, (W - self.SW_GAP) // (self.SW_W + self.SW_GAP))
        self._pt_tags = {}
        for i, (col, d) in enumerate(self.pt_items):
            r, k = divmod(i, cols)
            x = self.SW_GAP + k * (self.SW_W + self.SW_GAP)
            y = self.SW_GAP + r * (self.SW_H + 22 + self.SW_GAP)
            rgb = '#%02x%02x%02x' % lab_to_rgb(col[1], col[2], col[3])
            tag = f"s{i}"
            c.create_rectangle(x, y, x + self.SW_W, y + self.SW_H, fill=rgb,
                               outline='#1e6fd9' if self.pt_sel is col else '#d0d0d0',
                               width=3 if self.pt_sel is col else 1, tags=(tag,))
            label = col[0].replace('PANTONE® ', '').replace('PANTONE ', '')
            c.create_text(x + self.SW_W / 2, y + self.SW_H + 10, text=label[:16],
                          font=('맑은 고딕', 8), tags=(tag,))
            if self.pt_hits and i < len(self.pt_hits):
                c.create_text(x + 6, y + 10, anchor='w', text=f"ΔE {self.pt_hits[i]:.2f}",
                              font=('맑은 고딕', 8, 'bold'),
                              fill='#000' if col[1] > 55 else '#fff', tags=(tag,))
            c.tag_bind(tag, '<Button-1>', lambda e, i=i: self._pt_pick(i))
        rows = (len(self.pt_items) + cols - 1) // cols
        c.configure(scrollregion=(0, 0, W, self.SW_GAP + rows * (self.SW_H + 22 + self.SW_GAP)))

    def _pt_pick(self, i):
        col, d = self.pt_items[i]
        self.pt_sel = col
        rgb = '#%02x%02x%02x' % lab_to_rgb(col[1], col[2], col[3])
        self.pt_big.delete('all')
        cmp_ = getattr(self, 'pt_cmp', None)
        txt = f"{col[0]}\n팬덱: {d['ko']}\nL* {col[1]:.2f}   a* {col[2]:.2f}   b* {col[3]:.2f}\n화면 색 {rgb.upper()}"
        if cmp_ and self.pt_hits is not None:
            # 비교 썸네일: 왼쪽 내가 잰 색 | 오른쪽 팬톤 색
            mine = '#%02x%02x%02x' % lab_to_rgb(*cmp_[1])
            self.pt_big.create_rectangle(0, 0, 121, 152, fill=mine, outline='')
            self.pt_big.create_rectangle(121, 0, 242, 152, fill=rgb, outline='')
            for x, t, L in ((60, '내가 잰 색', cmp_[1][0]), (181, '팬톤', col[1])):
                self.pt_big.create_text(x, 14, text=t, font=('맑은 고딕', 9, 'bold'),
                                        fill='#000' if L > 55 else '#fff')
            dE = de2000(*cmp_[1], col[1], col[2], col[3])
            feel = ("눈으로 거의 같음" if dE <= 1 else "자세히 보면 다름" if dE <= 2
                    else "차이가 보임" if dE <= 5 else "다른 색")
            txt = (f"ΔE2000 {dE:.2f}  ({feel})\n" + txt +
                   f"\n\n내가 잰 색({cmp_[0]}): L* {cmp_[1][0]:.2f}  a* {cmp_[1][1]:.2f}  b* {cmp_[1][2]:.2f}")
        else:
            self.pt_big.create_rectangle(0, 0, 242, 152, fill=rgb, outline='')
        self.pt_sel_var.set(txt)
        self._pt_layout()

    def _pt_put(self, side):
        if not self.pt_sel:
            messagebox.showinfo("팬톤 색 보기", "먼저 색 칸을 누르십시오.")
            return
        col = self.pt_sel
        self.state_data[side]['measurements'].append((col[1], col[2], col[3]))
        self._update_panel(side)
        self._set_status(f"{'기준색' if side == 'ref' else '비교색'}에 {col[0]} 을(를) 넣었습니다")

    def _pt_to_palette(self):
        if not self.pt_sel:
            messagebox.showinfo("팬톤 색 보기", "먼저 색 칸을 누르십시오.")
            return
        name = self._current_palette_name() if hasattr(self, 'palettes_tab_selector_var') else None
        if not name or name not in self.palettes:
            messagebox.showwarning("내 팔레트", "[내 팔레트] 탭에서 팔레트를 먼저 만들거나 고르십시오.")
            return
        col = self.pt_sel
        self.palettes[name]['entries'].append({'name': col[0], 'lab': (col[1], col[2], col[3])})
        self._save_palettes()
        try:
            self._refresh_palette_entries()
        except Exception:
            pass
        self._set_status(f"'{name}' 팔레트에 {col[0]} 을(를) 넣었습니다")

    def _pt_nearest(self, side):
        ms = self.state_data[side]['measurements']
        if not ms:
            messagebox.showinfo("팬톤 색 보기",
                                f"{'기준색' if side == 'ref' else '비교색'}을 먼저 재거나 넣으십시오.")
            return
        L, a, b = (sum(m[i] for m in ms) / len(ms) for i in range(3))
        items = self._pt_current_colors()
        scored = sorted(((de2000(L, a, b, c[1], c[2], c[3]), c, d) for c, d in items), key=lambda x: x[0])[:40]
        self.pt_hits = [x[0] for x in scored]
        self.pt_cmp = ('기준색' if side == 'ref' else '비교색', (L, a, b))
        self._pt_fill([(c, d) for _, c, d in scored],
                      info=f"{'기준색' if side == 'ref' else '비교색'}(L {L:.1f}, a {a:.1f}, b {b:.1f})과 가까운 순서 40색  ·  "
                           f"ΔE2000 1 이하면 눈으로 거의 같음")
        if scored:
            self._pt_pick(0)

    def _tab_preview(self, nb):
        frame = ttk.Frame(nb, padding=10)
        nb.add(frame, text="실시간 화면")

        ctrl = ttk.Frame(frame)
        ctrl.pack(fill=tk.X, pady=(0, 8))

        self.preview_running = False
        self.preview_btn = ttk.Button(ctrl, text="▶ 실시간 화면 시작",
                                      command=self._toggle_live_preview)
        self.preview_btn.pack(side=tk.LEFT, padx=4)

        ttk.Button(ctrl, text="멈춤",
                   command=self._stop_live_preview).pack(side=tk.LEFT, padx=4)
        ttk.Button(ctrl, text="실시간 화면 사진 저장...",
                   command=self._preview_save).pack(side=tk.LEFT, padx=4)

        ttk.Label(ctrl, text="새로 고침 간격(ms):").pack(side=tk.LEFT, padx=(20, 4))
        self.preview_interval_var = tk.StringVar(value="500")
        ttk.Entry(ctrl, textvariable=self.preview_interval_var,
                  width=6).pack(side=tk.LEFT)

        preview_frame = ttk.LabelFrame(frame, text="Preview")
        preview_frame.pack(fill=tk.BOTH, expand=True)

        self.preview_canvas = tk.Canvas(preview_frame, width=640, height=480,
                                        bg='black')
        self.preview_canvas.pack(padx=4, pady=4)
        self.preview_canvas.create_text(320, 240, text="실시간 화면이 꺼져 있습니다",
                                        fill="#666", font=("Segoe UI", 12))

        self.preview_log = tk.Text(frame, height=6, font=("Consolas", 9),
                                   state=tk.DISABLED, wrap=tk.NONE)
        self.preview_log.pack(fill=tk.X, pady=(8, 0))

    def _preview_print(self, text):
        self.preview_log.config(state=tk.NORMAL)
        self.preview_log.insert(tk.END, text + "\n")
        self.preview_log.see(tk.END)
        self.preview_log.config(state=tk.DISABLED)

    def _toggle_live_preview(self):
        if self.preview_running:
            self._stop_live_preview()
        else:
            self._start_live_preview()

    def _start_live_preview(self):
        if not self.connected:
            messagebox.showerror("오류", "연결되어 있지 않습니다")
            return
        if not HAS_PIL:
            messagebox.showerror("오류", "Pillow(그림 부품)가 없습니다")
            return

        fn = getattr(rm, "StartPreview", None)
        ok, val = try_call(fn)
        if not ok:
            self._preview_print(f"StartPreview: 오류 {val}")
            return

        self.preview_running = True
        self.preview_btn.config(text="⏹ 실시간 화면 멈춤")
        self._preview_print("실시간 화면을 시작했습니다.")
        self._preview_tick()

    def _stop_live_preview(self):
        self.preview_running = False
        if self.preview_after_id:
            try:
                self.after_cancel(self.preview_after_id)
            except Exception:
                pass
            self.preview_after_id = None

        fn = getattr(rm, "StopPreview", None)
        try_call(fn)
        try:
            self.preview_btn.config(text="▶ 실시간 화면 시작")
            self.preview_canvas.delete("all")
            self.preview_canvas.create_text(320, 240,
                                            text="실시간 화면을 멈췄습니다",
                                            fill="#666", font=("Segoe UI", 12))
        except Exception:
            pass
        self._preview_print("실시간 화면을 멈췄습니다.")

    def _preview_tick(self):
        if not self.preview_running:
            return

        try:
            interval = max(100, int(self.preview_interval_var.get()))
        except Exception:
            interval = 500

        fn = getattr(rm, "GetPreview", None)
        ok, data = try_call(fn)

        if ok and data and len(data) > 4:
            try:
                width = int.from_bytes(data[0:2], 'big')
                height = int.from_bytes(data[2:4], 'big')
                pixels = data[4:]

                img = Image.new("RGB", (width, height))
                expected = width * height * 2
                if len(pixels) < expected:
                    self._preview_print(
                        f"화면 점이 모자랍니다: {len(pixels)} < {expected}")
                    self.preview_after_id = self.after(interval, self._preview_tick)
                    return

                pix_data = []
                for i in range(0, expected, 2):
                    v = int.from_bytes(pixels[i:i+2], 'big')
                    r = (v >> 11) & 0x1F
                    g = (v >> 5) & 0x3F
                    b = v & 0x1F
                    pix_data.append((
                        (r * 255) // 31,
                        (g * 255) // 63,
                        (b * 255) // 31,
                    ))

                img.putdata(pix_data)
                img = img.resize((640, 480), Image.NEAREST)
                photo = ImageTk.PhotoImage(img)

                self.preview_canvas.delete("all")
                self.preview_canvas.create_image(320, 240, image=photo)
                self.preview_canvas.image = photo
            except Exception as e:
                self._preview_print(f"그리기 오류: {e}")
        elif not ok:
            self._preview_print(f"GetPreview: {data}")

        if self.preview_running:
            self.preview_after_id = self.after(interval, self._preview_tick)

    def _preview_save(self):
        target = filedialog.asksaveasfilename(
            title="SavePreview", initialfile="preview.bmp",
            defaultextension=".bmp")

        if not target:
            return

        def worker():
            fn = getattr(rm, "SavePreview", None)
            ok, val = try_call(fn, target)
            self.after(0, lambda: self._preview_print(
                f"SavePreview: " + ("OK" if ok else f"오류 {val}")))

        threading.Thread(target=worker, daemon=True).start()

    # ======================================================================
    #  ВКЛАДКА 9. КОНСОЛЬ
    # ======================================================================

    def _tab_console(self, nb):
        frame = ttk.Frame(nb, padding=10)
        nb.add(frame, text="콘솔")

        unlock = ttk.LabelFrame(frame, text="Unlock Extended Commands")
        unlock.pack(fill=tk.X, pady=(0, 8))

        ttk.Label(unlock, text="비밀번호:").grid(row=0, column=0, padx=4, pady=4, sticky='w')
        self.unlock_pass_var = tk.StringVar(value=DEFAULT_UNLOCK_PASSWORD)
        ttk.Entry(unlock, textvariable=self.unlock_pass_var, width=30).grid(
            row=0, column=1, padx=4, pady=4, sticky='we')
        ttk.Button(unlock, text="Unlock",
                   command=self._on_unlock).grid(row=0, column=2, padx=4, pady=4)

        gen = ttk.LabelFrame(frame, text="GenericCmd")
        gen.pack(fill=tk.X, pady=(0, 8))

        self.preset_commands = {
            "SetSerialNum": {
                "cmd": "0x032a", "v1": "0x00001d7e", "v2": "0x000005de",
                "v3": "0", "v4": "0", "v5": "0", "v6": "0", "string": "0",
            },
            "BackupCalibData (text)": {
                "cmd": "0x0167", "v1": "0x00bc614e", "v2": "0x00001fa9",
                "v3": "0x0000", "v4": "0", "v5": "0", "v6": "0", "string": "",
            },
            "BackupCalibData (binary)": {
                "cmd": "0x0167", "v1": "0x00bc614e", "v2": "0x00001fa9",
                "v3": "0x1d7e", "v4": "0", "v5": "0", "v6": "0", "string": "",
            },
            "GetMultiColorCmd": {
                "cmd": "0x7823", "v1": "0", "v2": "0", "v3": "0",
                "v4": "0", "v5": "0", "v6": "0", "string": "",
            },
        }

        ttk.Label(gen, text="명령:").grid(row=0, column=0, padx=4, pady=4, sticky='w')
        self.gen_cmd_var = tk.StringVar(value="")
        self.gen_cmd_combo = ttk.Combobox(gen, textvariable=self.gen_cmd_var,
                                          values=list(self.preset_commands.keys()),
                                          width=30)
        self.gen_cmd_combo.grid(row=0, column=1, padx=4, pady=4, sticky='we')
        self.gen_cmd_combo.bind('<<ComboboxSelected>>', self._on_preset_selected)

        params = ['v1', 'v2', 'v3', 'v4', 'v5', 'v6']
        self.gen_param_vars = {}
        for i, p in enumerate(params):
            ttk.Label(gen, text=f"{p}:").grid(row=1, column=i*2, padx=2, pady=2, sticky='e')
            var = tk.StringVar(value="0")
            self.gen_param_vars[p] = var
            ttk.Entry(gen, textvariable=var, width=12).grid(
                row=1, column=i*2+1, padx=2, pady=2)

        ttk.Label(gen, text="String:").grid(row=2, column=0, padx=4, pady=4, sticky='w')
        self.gen_string_var = tk.StringVar(value="")
        ttk.Entry(gen, textvariable=self.gen_string_var, width=50).grid(
            row=2, column=1, columnspan=5, padx=4, pady=4, sticky='we')

        ttk.Button(gen, text="GenericCmd 보내기",
                   command=self._console_generic).grid(row=3, column=1,
                                                       padx=4, pady=4, sticky='w')

        self.console_log = tk.Text(frame, height=20, font=("Consolas", 10),
                                   state=tk.DISABLED, wrap=tk.NONE)
        self.console_log.pack(fill=tk.BOTH, expand=True)

    def _on_preset_selected(self, event=None):
        name = self.gen_cmd_var.get()
        if name in self.preset_commands:
            preset = self.preset_commands[name]
            self.gen_cmd_var.set(preset['cmd'])
            for p in ['v1', 'v2', 'v3', 'v4', 'v5', 'v6']:
                self.gen_param_vars[p].set(preset.get(p, '0'))
            self.gen_string_var.set(preset.get('string', ''))

    def _console_print(self, text):
        self.console_log.config(state=tk.NORMAL)
        self.console_log.insert(tk.END, text + "\n")
        self.console_log.see(tk.END)
        self.console_log.config(state=tk.DISABLED)

    def _on_unlock(self):
        password = self.unlock_pass_var.get().strip()
        if not password:
            messagebox.showwarning("비밀번호", "비밀번호 입력")
            return

        def worker():
            fn = getattr(rm, "UnlockExtendedCommands", None)
            ok, val = try_call(fn, password)
            if ok:
                self.after(0, lambda: self._console_print(
                    f"UnlockExtendedCommands -> OK"))
                self.after(0, lambda: self._set_status(
                    "확장 명령 잠금 해제됨"))
            else:
                self.after(0, lambda: self._console_print(
                    f"UnlockExtendedCommands -> 오류: {val}"))

        threading.Thread(target=worker, daemon=True).start()

    def _console_generic(self):
        cmd_str = self.gen_cmd_var.get().strip()
        if not cmd_str:
            return

        try:
            cmd = int(cmd_str, 0)
        except Exception:
            self._console_print(f"명령 형식이 틀렸습니다: {cmd_str}")
            return

        params = []
        for p in ['v1', 'v2', 'v3', 'v4', 'v5', 'v6']:
            try:
                params.append(int(self.gen_param_vars[p].get(), 0))
            except Exception:
                self._console_print(f"형식이 틀렸습니다 {p}")
                return

        string = self.gen_string_var.get()

        def worker():
            fn = getattr(rm, "GenericCmd", None)
            if fn is None:
                self.after(0, lambda: self._console_print("GenericCmd 없음"))
                return
            ok, val = try_call(fn, cmd, params[0], params[1], params[2],
                               params[3], params[4], params[5], string)
            if ok:
                self.after(0, lambda: self._console_print(
                    f"GenericCmd(0x{cmd:04x}, {params}, {string!r}) -> OK"))
            else:
                self.after(0, lambda: self._console_print(
                    f"GenericCmd(0x{cmd:04x}) -> 오류: {val}"))

        threading.Thread(target=worker, daemon=True).start()

    # ======================================================================
    #  ПОДКЛЮЧЕНИЕ И СЛУЖЕБНЫЕ
    # ======================================================================

    def _connect_async(self):
        if self.busy:
            return
        self._set_busy(True, "RM200 에 연결하는 중...")

        def worker():
            try:
                safe_command(rm.Connect)
                fw = None
                try:
                    fw = safe_command(rm.GetFWVersion)
                except Exception:
                    try:
                        ok, fw = try_call(getattr(rm, "GetFWInfo", None))
                    except Exception:
                        pass
                sn = None
                try:
                    sn = safe_command(rm.GetSerialNum)
                except Exception:
                    pass
                cnt = safe_command(rm.GetNumberOfEntries)
                dev_time = None
                for fname in ("GetTimeString", "GetTime", "GetDateTime", "GetRTCTime"):
                    fn = getattr(rm, fname, None)
                    if fn is not None:
                        try:
                            dev_time = safe_command(fn)
                            break
                        except Exception:
                            pass
                self.after(0, lambda: self._on_connect_ok(fw, sn, cnt, dev_time))
            except Exception as e:
                self.after(0, lambda e=e: self._on_connect_fail(e))

        threading.Thread(target=worker, daemon=True).start()

    def _on_connect_ok(self, fw, sn, cnt, dev_time):
        self.connected = True
        if not self._xs_checked:
            self._xs_checked = True
            self.after(1500, self._xs_check)
        self._led_state = 'ok'
        self._hb_fail = 0
        self._hb_n = 0
        self.device_info = {'fw': fw, 'sn': sn, 'count': cnt, 'dev_time': dev_time}
        self._set_busy(False)
        self._update_status_bar()
        self._refresh_file_info_async()

    def _on_connect_fail(self, e):
        self.connected = False
        self._led_state = 'off'
        self._set_busy(False)
        self._set_status(f"연결 안 됨: {e}")
        if self._is_driver_err(e):
            self._driver_offer()
            return
        messagebox.showerror(
            "연결 오류",
            f"RM200 에 연결하지 못했습니다:\n{e}\n\n"
            "USB 연결과 기계 전원을 확인한 뒤 [RM200 다시 연결]을 누르십시오.\n처음이면 USB 드라이버(WinUSB)를 바꿔야 합니다(설명서 2번)."
        )

    def _refresh_file_info_async(self):
        if not self.connected:
            return

        def worker():
            try:
                data = safe_command(rm.FetchFile, "MeasDataV05.dat")
                records = parse_measdata(data)
                self._known_keys = {(r.get('counter'), r.get('datetime'),
                                     tuple(round(x, 3) for x in r['sample_lab'])) for r in records}
                newest = newest_record(records)
                self.after(0, lambda: self._on_file_info(newest, records, None))
            except Exception as e:
                self.after(0, lambda e=e: self._on_file_info(None, None, e))

        threading.Thread(target=worker, daemon=True).start()

    def _on_file_info(self, newest, records, error):
        if error:
            self._update_status_bar(extra=f"기록 파일 읽기 오류 ({error})")
            return
        if newest is None:
            self._update_status_bar(extra="기록 파일: 측정값 없음")
            return
        age = record_age_seconds(newest)
        extra = f"파일의 마지막 측정: {newest['datetime']} ({format_age(age)})"
        self._update_status_bar(extra=extra)

    def _menu_reconnect(self):
        def worker():
            ok = self._reconnect_device()
            self.after(0, lambda: self._update_status_bar(
                extra=("다시 연결 성공" if ok else "다시 연결 실패")))
        threading.Thread(target=worker, daemon=True).start()

    def _menu_reboot(self):
        def worker():
            ok = self._reboot_device()
            self.after(0, lambda: self._update_status_bar(
                extra=("reboot OK" if ok else "reboot FAIL")))
        threading.Thread(target=worker, daemon=True).start()

    def _menu_save_dump(self):
        if not self.connected:
            messagebox.showerror("오류", "연결되어 있지 않습니다")
            return
        target = filedialog.asksaveasfilename(
            title="측정 기록 파일 저장", initialfile="MeasDataV05.dat")
        if not target:
            return

        def worker():
            try:
                data = safe_command(rm.FetchFile, "MeasDataV05.dat")
                with open(target, 'wb') as f:
                    f.write(data)
                self.after(0, lambda: self._set_status(
                    f"{len(data)} 바이트를 {target} 에 저장했습니다"))
            except Exception as e:
                self.after(0, lambda e=e: messagebox.showerror("오류", str(e)))

        threading.Thread(target=worker, daemon=True).start()

    def _menu_screenshot(self):
        self._notebook.select(7)
        self._on_screen_screenshot()

    def _menu_temperature(self):
        ok, val = try_call(getattr(rm, "MeasureTemperature", None))
        messagebox.showinfo("온도",
                            f"{val!r}" if ok else f"오류: {val}")

    def _menu_about(self):
        messagebox.showinfo(
            "프로그램 정보",
            "RM200 Color Advisor\n\n"
            "기준색과 비교색 측정, ΔE 색 차이, CMYK 보정 제안, 내 팔레트,\n"
            "기계 정보, 파일 받기, 팬덱 켜고 끄기, 교정 상태,\n"
            "기계 화면과 실시간 화면 보기.\n\n기계를 망가뜨릴 수 있는 쓰기·지우기 명령은 막혀 있습니다.\n\n"
            "원작: slowsky-netizen/Rm200 (MIT), 통신: rm200lib (Richard Burton, AGPL-3.0). 한국어판: 대표님 프로젝트."
        )

    def _reconnect_device(self):
        print("[RECONNECT] Disconnect + Connect...")
        try:
            rm.Disconnect()
        except Exception:
            pass
        time.sleep(1.0)

        for attempt in range(1, RECONNECT_MAX + 1):
            try:
                rm.Connect()
                print(f"[다시 연결] 성공 ({attempt}번째).")
                try:
                    self.device_info['count'] = safe_command(rm.GetNumberOfEntries)
                except Exception:
                    pass
                self.connected = True
                return True
            except Exception as e:
                print(f"[다시 연결] {attempt}번째 시도: {e}")
                time.sleep(RECONNECT_DELAY)

        self.connected = False
        print("[다시 연결] 실패.")
        return False

    def _reboot_device(self):
        reboot_fn = getattr(rm, "Reboot", None)
        if reboot_fn is None:
            print("[재부팅] 기능 없음.")
            return False

        print("[재부팅] 명령을 보냅니다...")
        ok, exc = _call_with_timeout(reboot_fn, REBOOT_TIMEOUT)
        if not ok:
            print(f"[재부팅] 실패: {exc}")
            return False

        for attempt in range(1, RECONNECT_MAX + 1):
            time.sleep(RECONNECT_DELAY)
            try:
                rm.Connect()
                print(f"[재부팅] 다시 연결 성공 ({attempt}번째).")
                try:
                    self.device_info['count'] = safe_command(rm.GetNumberOfEntries)
                except Exception:
                    pass
                self.connected = True
                return True
            except Exception as e:
                print(f"[재부팅] {attempt}번째 시도: {e}")

        self.connected = False
        print("[재부팅] 다시 켠 뒤 연결하지 못했습니다.")
        return False

    # ======================================================================
    #  ИЗМЕРЕНИЕ / СРАВНЕНИЕ
    # ======================================================================

    # ---- Ver 0.16: 측정 (교정 확인, 단계·초 표시, 취소, 진행 기록) ----
    def _meas_log(self, msg):
        try:
            path = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(PALETTES_FILE))),
                                "측정_진행기록.txt")
            with open(path, 'a', encoding='utf-8') as f:
                f.write(dt.datetime.now().strftime('%Y-%m-%d %H:%M:%S ') + msg + "\n")
        except Exception:
            pass

    def _meas_stage(self, token, text):
        if token != self._meas_token:
            return
        self._meas_text = text
        self._meas_log(f"  {time.time() - self._meas_t0:5.1f}초  {text}")

    def _meas_tick(self, token):
        if token != self._meas_token or not self.busy:
            return
        side = self._meas_side
        sw = self.widgets[side]['swatch']
        sw.delete('all')
        W = max(300, sw.winfo_width()); H = max(120, sw.winfo_height())
        el = time.time() - self._meas_t0
        sw.create_rectangle(0, 0, W, H, fill='#fff8e1', outline='')
        sw.create_text(W / 2, H / 2 - 22, text=self._meas_text, fill='#e65100',
                       font=('맑은 고딕', 13, 'bold'), width=W - 30)
        sw.create_text(W / 2, H / 2 + 18, text=f"{el:.0f}초 지남", fill='#555',
                       font=('맑은 고딕', 12))
        sw.create_text(W / 2, H - 16, text="기계 단추는 누르지 마십시오 · 보통 15~25초 · [측정 취소]로 멈춤",
                       fill='#888', font=('맑은 고딕', 9))
        self.after(500, lambda: self._meas_tick(token))

    def _meas_end(self, token):
        """측정이 끝나거나 취소되면 단추를 원래대로."""
        if token != self._meas_token:
            return False
        self._meas_token += 1
        for sd in ('ref', 'smp'):
            try:
                self.widgets[sd]['measure_btn'].config(text="측정", command=lambda s=sd: self._on_measure(s))
            except Exception:
                pass
        self._set_busy(False)
        return True

    def _on_measure_cancel(self):
        side = getattr(self, '_meas_side', 'smp')
        self._meas_log("  사용자가 측정 취소")
        self._meas_end(self._meas_token)
        self._update_panel(side)
        self._set_status("측정을 취소했습니다")

    def _on_measure(self, side):
        if not self.connected:
            messagebox.showerror("오류", "RM200 과 연결되어 있지 않습니다")
            return
        if self.busy:
            return
        self._meas_token = getattr(self, '_meas_token', 0) + 1
        token = self._meas_token
        self._meas_side = side
        self._meas_t0 = time.time()
        self._meas_text = "교정 상태 확인 중"
        self._set_busy(True, "측정 중입니다... RM200 을 측정할 곳에 대고 기다리십시오.")
        b = self.widgets[side]['measure_btn']
        b.config(state=tk.NORMAL, text="측정 취소", command=self._on_measure_cancel)
        self._meas_log(f"측정 시작 ({'기준색' if side == 'ref' else '비교색'})")
        self._meas_tick(token)

        def stage(t):
            self.after(0, lambda: self._meas_stage(token, t))

        def worker():
            try:
                # 1) 교정 확인
                try:
                    cs = safe_command(rm.GetCalibrationState)
                    left = safe_command(rm.GetTimeToCalibExpired)
                except Exception:
                    cs = left = None
                self._meas_log(f"  교정 상태 {cs!r}, 만료까지 {left!r}")
                if cs == 0 or left == 0:
                    raise RuntimeError("CALIB")
                if token != self._meas_token:
                    return
                # 2) 이미 아는 기록(지난번 읽은 것) — 없으면 지금 한 번 읽음
                def rec_key(r):
                    return (r.get('counter'), r.get('datetime'), tuple(round(x, 3) for x in r['sample_lab']))
                before = getattr(self, '_known_keys', None)
                if before is None:
                    stage("기록 파일 확인 중")
                    try:
                        before = {rec_key(r) for r in parse_measdata(safe_command(rm.FetchFile, "MeasDataV05.dat"))}
                    except Exception:
                        before = None
                prev_count = safe_command(rm.GetNumberOfEntries) or 0
                stage("기계가 재는 중 (기계를 대고 움직이지 마십시오)")
                safe_command(rm.TriggerMeasurement, self.aperture)
                t_trig = time.time()
                scr_checked = False

                deadline = time.time() + self.timeout
                got = False
                while time.time() < deadline:
                    if token != self._meas_token:
                        return
                    try:
                        cnt = safe_command(rm.GetNumberOfEntries)
                    except Exception:
                        cnt = None
                    if cnt is not None and cnt > prev_count:
                        got = True
                        break
                    if not scr_checked and time.time() - t_trig > 6:
                        scr_checked = True
                        try:
                            with rm.LOCK:
                                lcd = rm.GetLcdData()
                            if lcd_has_alert(lcd):
                                self._last_lcd = lcd
                                raise RuntimeError("SCREEN")
                        except RuntimeError:
                            raise
                        except Exception:
                            pass
                    time.sleep(0.5)
                if not got:
                    try:
                        cs = safe_command(rm.GetCalibrationState)
                    except Exception:
                        cs = None
                    raise RuntimeError("CALIB" if cs == 0 else "NOMEAS")
                stage("측정됨, 값 꺼내는 중")
                time.sleep(1.0)

                records = []
                fresh = []
                for attempt in range(3):
                    if token != self._meas_token:
                        return
                    if attempt > 0:
                        # 기계가 아직 파일에 옮겨 적지 않음 → 기계를 다시 켜서 옮기게 함
                        stage("값 꺼내는 중 (기계를 잠깐 다시 켭니다, 약 10초)")
                        if not self._reboot_device():
                            raise RuntimeError("기계를 다시 켠 뒤 연결하지 못했습니다. [RM200 다시 연결]을 누르십시오")
                        time.sleep(0.5)
                    stage("기록 읽는 중")
                    data = safe_command(rm.FetchFile, "MeasDataV05.dat")
                    records = parse_measdata(data)
                    if before is not None:
                        fresh = [r for r in records if rec_key(r) not in before]
                    if fresh or before is None or attempt == 2:
                        break
                if records:
                    self._known_keys = {rec_key(r) for r in records}
                try:
                    cs2 = safe_command(rm.GetCalibrationState)
                except Exception:
                    cs2 = None
                if cs2 == 0:
                    self.after(0, lambda: self._set_status(
                        "기계가 다시 켜진 뒤 교정을 원합니다. 다음 측정 전에 기계 화면에 따라 교정하십시오."))
                if not records:
                    raise RuntimeError("기록 파일에 쓸 수 있는 측정값이 없습니다")
                if fresh:
                    newest = sorted(fresh, key=lambda r: (r.get('counter') or 0, r['datetime']))[-1]
                    self._meas_log(f"  끝: {time.time() - self._meas_t0:.1f}초, L={newest['sample_lab'][0]:.2f}")
                    self.after(0, lambda: self._meas_end(token) and self._on_new_measure(side, newest))
                else:
                    self._meas_log("  새 기록을 찾지 못해 목록에서 고르게 함")
                    self.after(0, lambda: self._meas_end(token) and self._on_pick_records(side, records, None))
            except Exception as e:
                self._meas_log(f"  오류: {e}")
                self.after(0, lambda e=e: self._meas_fail(token, side, e))

        threading.Thread(target=worker, daemon=True).start()

    def _meas_fail(self, token, side, e):
        if not self._meas_end(token):
            return
        self._update_panel(side)
        if str(e) == "CALIB":
            self._set_status("기계가 교정을 원합니다")
            self._auto_calibrate(need=True)
            return
        if str(e) == "SCREEN":
            self._set_status("기계 화면에 경고가 떠 있어 측정하지 못했습니다")
            self._dev_alert = False
            self._set_dev_alert(True, getattr(self, '_last_lcd', None))
            return
        if str(e) == "NOMEAS":
            self._set_status("기계가 측정하지 않았습니다")
            messagebox.showwarning(
                "측정되지 않았습니다",
                f"{int(self.timeout)}초 동안 기계에 새 측정이 생기지 않았습니다.\n\n"
                "기계 화면을 확인하십시오.\n"
                "· 교정하라는 글이 떠 있으면 교정을 먼저 하십시오.\n"
                "· 다른 화면(메뉴 등)이 열려 있으면 처음 화면으로 돌아간 뒤 다시 [측정]을 누르십시오.")
            return
        self._on_pick_records(side, None, e)

    def _on_new_measure(self, side, rec):
        """방금 잰 값을 목록에서 고를 필요 없이 바로 색 칸에 넣음."""
        self._set_busy(False)
        self.state_data[side]['measurements'].append(rec['sample_lab'])
        self._update_panel(side)
        side_ko = "기준색" if side == 'ref' else "비교색"
        n = len(self.state_data[side]['measurements'])
        self._set_status(
            f"{side_ko}에 방금 잰 값을 넣었습니다  L={rec['sample_lab'][0]:.2f} "
            f"a={rec['sample_lab'][1]:.2f} b={rec['sample_lab'][2]:.2f}  (모두 {n}개, 평균으로 계산)")

    def _on_pick_records(self, side, records, error):
        self._set_busy(False)

        if error:
            self._set_status(f"측정 오류: {error}")
            messagebox.showerror("측정 오류", str(error))
            return

        newest = newest_record(records)
        if newest is not None:
            age = record_age_seconds(newest)
            if age is not None and age > MAX_AGE_SECONDS:
                self._set_status(
                    f"[!] 가장 최근 측정: {newest['datetime']} "
                    f"({format_age(age)})."
                )
            else:
                self._update_status_bar(
                    extra=f"파일의 마지막 측정: {newest['datetime']} "
                          f"({format_age(age)})"
                )

        chosen = self._show_pick_record_dialog(side, records)
        if chosen is None:
            self._set_status("측정값을 넣지 않았습니다")
            return

        self.state_data[side]['measurements'].append(chosen['sample_lab'])
        self._update_panel(side)
        side_ru = "기준색" if side == 'ref' else "비교색"
        n = len(self.state_data[side]['measurements'])
        self._set_status(
            f"{side_ru} 추가: {chosen['datetime']}  "
            f"L={chosen['sample_lab'][0]:.2f} "
            f"a={chosen['sample_lab'][1]:.2f} "
            f"b={chosen['sample_lab'][2]:.2f}  (모두 {n}개)"
        )

    def _show_pick_record_dialog(self, side, records):
        side_ru = "기준색" if side == 'ref' else "비교색"

        state = {'records': sorted(records,
                                   key=lambda r: (r['datetime'], r['counter']),
                                   reverse=True)}

        dlg = tk.Toplevel(self)
        dlg.title(f"측정값 고르기 ({side_ru})")
        dlg.transient(self)
        dlg.grab_set()
        dlg.geometry("900x600")
        dlg.minsize(720, 480)

        header_var = tk.StringVar()
        age_var    = tk.StringVar()
        status_var = tk.StringVar(value="")

        ttk.Label(dlg, textvariable=header_var, padding=(8, 8, 8, 2),
                  font=("Segoe UI", 9, "bold")).pack(anchor=tk.W)
        ttk.Label(dlg, textvariable=age_var, padding=(8, 0, 8, 2),
                  font=("Segoe UI", 9)).pack(anchor=tk.W)

        warn_text = ("방금 잰 값이 목록에 없으면 RM200 이 아직 "
                     "기록을 저장하지 않은 것입니다.\n아래 [새로 고침] 또는 "
                     "[다시 켜고 새로 고침]을 누르십시오.")
        ttk.Label(dlg, text=warn_text, foreground="#a00",
                  padding=(8, 4, 8, 8), wraplength=860,
                  justify=tk.LEFT).pack(anchor=tk.W)

        list_frame = ttk.Frame(dlg)
        list_frame.pack(fill=tk.BOTH, expand=True, padx=8, pady=4)

        scrollbar = ttk.Scrollbar(list_frame, orient=tk.VERTICAL)
        listbox = tk.Listbox(list_frame, font=("Consolas", 10), height=16,
                             yscrollcommand=scrollbar.set)
        scrollbar.config(command=listbox.yview)
        listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        ttk.Label(dlg, textvariable=status_var, padding=(8, 0, 8, 0),
                  foreground="#555").pack(anchor=tk.W)

        result = {'rec': None}

        def update_header():
            total = len(state['records'])
            ram_count = self.device_info.get('count')
            header_var.set(
                f"기록 파일의 측정값: {total}개.  "
                f"기계 기억 개수: {ram_count}."
            )
            if state['records']:
                newest = state['records'][0]
                age = record_age_seconds(newest)
                age_var.set(f"가장 최근: {newest['datetime']} "
                            f"({format_age(age)}).")
            else:
                age_var.set("기록이 없습니다.")

        def rebuild_list():
            listbox.delete(0, tk.END)
            for r in state['records']:
                L, a, b = r['sample_lab']
                tag = " <-- Solid C" if r['id'] == VALID_ID else ""
                age = record_age_seconds(r)
                listbox.insert(
                    tk.END,
                    f"{r['datetime']} ({format_age(age):>11})  "
                    f"L={L:7.3f} a={a:7.3f} b={b:7.3f}"
                    f"  {r['name']!r:12}{tag}"
                )
            if state['records']:
                listbox.selection_set(0)

        update_header()
        rebuild_list()

        btns = ttk.Frame(dlg)
        btns.pack(fill=tk.X, padx=8, pady=8)

        btn_refresh = ttk.Button(btns, text="새로 고침",
                                 command=lambda: do_refresh(False))
        btn_refresh.pack(side=tk.LEFT, padx=3)
        btn_refresh_reboot = ttk.Button(btns, text="다시 켜고 새로 고침",
                                        command=lambda: do_refresh(True))
        btn_refresh_reboot.pack(side=tk.LEFT, padx=3)

        btn_cancel = ttk.Button(btns, text="취소", command=lambda: on_cancel())
        btn_cancel.pack(side=tk.RIGHT, padx=3)
        btn_add = ttk.Button(btns, text="넣기", command=lambda: on_ok())
        btn_add.pack(side=tk.RIGHT, padx=3)

        def set_buttons_state(st):
            for b in (btn_refresh, btn_refresh_reboot, btn_add, btn_cancel):
                try:
                    b.config(state=st)
                except Exception:
                    pass

        def safe_after(func, *args):
            try:
                if dlg.winfo_exists():
                    dlg.after(0, lambda: func(*args))
            except Exception:
                pass

        def do_refresh(with_reboot):
            set_buttons_state(tk.DISABLED)
            status_var.set("다시 켜는 중..." if with_reboot
                           else "다시 연결하는 중...")

            def worker():
                try:
                    ok = self._reboot_device() if with_reboot \
                        else self._reconnect_device()
                    if not ok:
                        raise RuntimeError("다시 연결하지 못했습니다")
                    data = safe_command(rm.FetchFile, "MeasDataV05.dat")
                    new_records = parse_measdata(data)
                    new_sorted = sorted(
                        new_records,
                        key=lambda r: (r['datetime'], r['counter']),
                        reverse=True)
                    safe_after(on_refresh_done, new_sorted, None)
                except Exception as e:
                    safe_after(on_refresh_done, None, e)

            threading.Thread(target=worker, daemon=True).start()

        def on_refresh_done(new_records, error):
            set_buttons_state(tk.NORMAL)
            if error:
                status_var.set(f"오류: {error}")
                return
            state['records'] = new_records
            update_header()
            rebuild_list()
            status_var.set(f"새로 고쳤습니다. 측정값 {len(new_records)}개.")
            try:
                self._update_status_bar()
            except Exception:
                pass

        def on_ok():
            sel = listbox.curselection()
            if sel:
                result['rec'] = state['records'][sel[0]]
            dlg.destroy()

        def on_cancel():
            dlg.destroy()

        listbox.bind("<Double-Button-1>", lambda ev: on_ok())
        dlg.protocol("WM_DELETE_WINDOW", on_cancel)

        self.wait_window(dlg)
        return result['rec']

    def _on_import_latest(self, side):
        if not self.connected:
            messagebox.showerror("오류", "RM200 과 연결되어 있지 않습니다")
            return
        if self.busy:
            return

        self._set_busy(True, "측정 기록 읽는 중...")

        def worker():
            try:
                data = safe_command(rm.FetchFile, "MeasDataV05.dat")
                records = parse_measdata(data)
                if not records:
                    raise RuntimeError("기록 파일에 쓸 수 있는 측정값이 없습니다")
                self.after(0, lambda: self._on_pick_records(side, records, None))
            except Exception as e:
                self.after(0, lambda e=e: self._on_pick_records(side, None, e))

        threading.Thread(target=worker, daemon=True).start()

    def _on_import_both(self):
        if not self.connected:
            messagebox.showerror("오류", "RM200 과 연결되어 있지 않습니다")
            return
        if self.busy:
            return

        self._set_busy(True, "측정 기록 읽는 중...")

        def worker():
            try:
                data = safe_command(rm.FetchFile, "MeasDataV05.dat")
                records = parse_measdata(data)
                records.sort(key=lambda r: (r['datetime'], r['counter']))
                if len(records) < 2:
                    raise RuntimeError("기록 파일에 측정값이 2개 이상 있어야 합니다")
                ref = records[-2]
                smp = records[-1]
                self.after(0, lambda: self._on_import_both_done(ref, smp, None))
            except Exception as e:
                self.after(0, lambda e=e: self._on_import_both_done(None, None, e))

        threading.Thread(target=worker, daemon=True).start()

    def _on_import_both_done(self, ref, smp, error):
        self._set_busy(False)
        if error:
            self._set_status(f"가져오기 오류: {error}")
            messagebox.showerror("오류", str(error))
            return

        age_ref = record_age_seconds(ref)
        age_smp = record_age_seconds(smp)

        msg = (f"마지막 측정값 2개를 가져올까요?\n\n"
               f"기준색 (마지막에서 두 번째):\n"
               f"  {ref['datetime']}  ({format_age(age_ref)})\n"
               f"  L*={ref['sample_lab'][0]:.2f} "
               f"a*={ref['sample_lab'][1]:.2f} "
               f"b*={ref['sample_lab'][2]:.2f}\n\n"
               f"비교색 (마지막):\n"
               f"  {smp['datetime']}  ({format_age(age_smp)})\n"
               f"  L*={smp['sample_lab'][0]:.2f} "
               f"a*={smp['sample_lab'][1]:.2f} "
               f"b*={smp['sample_lab'][2]:.2f}")

        if messagebox.askyesno("측정값 2개 가져오기", msg):
            self.state_data['ref']['measurements'].append(ref['sample_lab'])
            self.state_data['smp']['measurements'].append(smp['sample_lab'])
            self._update_panel('ref')
            self._update_panel('smp')
            self._set_status("마지막 측정값 2개를 가져왔습니다")
        else:
            self._set_status("가져오기를 취소했습니다")

    def _on_clear(self, side):
        if not self.state_data[side]['measurements']:
            return
        side_ru = "기준색" if side == 'ref' else "비교색"
        if messagebox.askyesno("지우기", f"{side_ru} 측정을 모두 지울까요?"):
            self.state_data[side]['measurements'].clear()
            self._update_panel(side)
            self._set_status(f"{side_ru} 측정값을 지웠습니다")

    def _update_panel(self, side):
        w = self.widgets[side]
        measurements = self.state_data[side]['measurements']

        w['swatch'].delete("all")
        SW = max(300, w['swatch'].winfo_width())
        SH = max(120, w['swatch'].winfo_height())
        if not measurements:
            w['swatch'].create_text(SW / 2, SH / 2, text="자료 없음", fill="#888",
                                    font=('맑은 고딕', 12))
            w['lab_var'].set("—")
        else:
            L = sum(m[0] for m in measurements) / len(measurements)
            a = sum(m[1] for m in measurements) / len(measurements)
            b = sum(m[2] for m in measurements) / len(measurements)
            r, g, b_ = lab_to_rgb(L, a, b)
            color = f"#{r:02x}{g:02x}{b_:02x}"
            w['swatch'].create_rectangle(0, 0, SW, SH,
                                         fill=color, outline=color)
            brightness = (r * 299 + g * 587 + b_ * 114) / 1000
            txt_color = 'black' if brightness > 128 else 'white'
            w['swatch'].create_text(SW / 2, SH / 2 - 14, text=color.upper(),
                                    fill=txt_color,
                                    font=("Consolas", 16, "bold"))
            w['swatch'].create_text(SW / 2, SH / 2 + 18,
                                    text=f"{len(measurements)}회 평균",
                                    fill=txt_color, font=("맑은 고딕", 11))
            w['lab_var'].set(f"L*={L:7.3f}  a*={a:7.3f}  b*={b:7.3f}")
        self._show_nearest_pantone(side)

        w['listbox'].config(state=tk.NORMAL)
        w['listbox'].delete('1.0', tk.END)
        for i, (L, a, b) in enumerate(measurements, 1):
            w['listbox'].insert(tk.END,
                                f"#{i:>2}:  L={L:7.3f}  a={a:7.3f}  b={b:7.3f}\n")
        w['listbox'].config(state=tk.DISABLED)

    # ---- Ver 0.13: 잰 색을 팬톤에서 찾기 ----
    def _nearest_pantone(self, L, a, b, n=1):
        allc = [(c, d) for d in pantone_decks() for c in d['colors']]
        # 빠른 1차 거르기(ΔE76) 뒤 ΔE2000 으로 다시 줄 세움
        pre = sorted(allc, key=lambda x: (x[0][1] - L) ** 2 + (x[0][2] - a) ** 2 + (x[0][3] - b) ** 2)[:80]
        sc = sorted(((de2000(L, a, b, c[1], c[2], c[3]), c, d) for c, d in pre), key=lambda x: x[0])
        return sc[:n]

    def _show_nearest_pantone(self, side):
        w = self.widgets[side]
        if 'pt_var' not in w:
            return
        ms = self.state_data[side]['measurements']
        w['pt_chip'].delete('all')
        if not ms:
            w['pt_var'].set("가장 가까운 팬톤: 측정하면 여기에 나옵니다")
            return
        L, a, b = (sum(m[i] for m in ms) / len(ms) for i in range(3))
        try:
            hit = self._nearest_pantone(L, a, b)
        except Exception:
            hit = []
        if not hit:
            w['pt_var'].set("가장 가까운 팬톤: 팬톤 자료를 읽지 못했습니다")
            return
        dE, c, d = hit[0]
        rgb = '#%02x%02x%02x' % lab_to_rgb(c[1], c[2], c[3])
        mine = '#%02x%02x%02x' % lab_to_rgb(L, a, b)
        w['pt_chip'].create_rectangle(0, 0, 17, 34, fill=mine, outline='')
        w['pt_chip'].create_rectangle(17, 0, 34, 34, fill=rgb, outline='')
        feel = ("거의 같음" if dE <= 1 else "자세히 보면 다름" if dE <= 2
                else "차이가 보임" if dE <= 5 else "다른 색")
        name = c[0].replace('PANTONE® ', 'PANTONE ')
        w['pt_var'].set(f"가장 가까운 팬톤: {name}  ΔE {dE:.2f} ({feel})\n"
                        f"{d['ko']}  ·  누르면 가까운 순서 40색")

    # ---- Ver 0.20: 우리 물건(내 팔레트)에서 가장 비슷한 색 찾기 ----
    def _find_own(self, side):
        ms = self.state_data[side]['measurements']
        if not ms:
            messagebox.showinfo("우리 물건에서 찾기",
                                f"{'기준색' if side == 'ref' else '비교색'}을 먼저 [측정]하거나 [가져오기] 하십시오.")
            return
        if not any(p['entries'] for p in self.palettes.values()):
            messagebox.showinfo("우리 물건에서 찾기",
                                "내 팔레트에 색이 없습니다.\n[내 팔레트] 칸에서 LVT·벽지·마루 같은 팔레트를 만들고\n"
                                "견본을 [새 색 측정해 넣기]로 넣어 두십시오.")
            return
        L, a, b = (sum(m[i] for m in ms) / len(ms) for i in range(3))
        w = getattr(self, '_own_win', None)
        if w is not None:
            try:
                w.destroy()
            except Exception:
                pass
        w = tk.Toplevel(self)
        self._own_win = w
        w.title("우리 물건에서 가장 비슷한 색")
        w.configure(bg='#ffffff')
        w.transient(self)
        top = tk.Frame(w, bg='#ffffff'); top.pack(fill=tk.X, padx=12, pady=(10, 4))
        tk.Label(top, text=f"잰 색 ({len(ms)}회 평균)  L {L:.1f}  a {a:.1f}  b {b:.1f}", bg='#ffffff',
                 font=('맑은 고딕', 11, 'bold'), fg='#1e3a5f').pack(side=tk.LEFT)
        tk.Label(top, text="   찾을 곳:", bg='#ffffff', font=('맑은 고딕', 11)).pack(side=tk.LEFT)
        scopes = ['모든 팔레트'] + self._pal_folders(self.palettes.keys())
        var = tk.StringVar(value=getattr(self, '_own_scope', '모든 팔레트')
                           if getattr(self, '_own_scope', '모든 팔레트') in scopes else '모든 팔레트')
        cb = ttk.Combobox(top, textvariable=var, values=scopes, state='readonly', width=28,
                          font=('맑은 고딕', 11))
        cb.pack(side=tk.LEFT, padx=6)
        tk.Label(w, text="ΔE 1 이하면 눈으로 거의 같음, 2 이하면 자세히 보면 다름, 5 넘으면 다른 색",
                 bg='#ffffff', fg='#777', font=('맑은 고딕', 9)).pack(anchor='w', padx=12)
        cv = tk.Canvas(w, width=640, height=10 * 58 + 8, bg='#ffffff', highlightthickness=0)
        cv.pack(padx=12, pady=8)

        def fill(e=None):
            self._own_scope = scope = var.get()
            hits = []
            for name, p in self.palettes.items():
                if scope != '모든 팔레트' and not (name == scope or name.startswith(scope + '/')):
                    continue
                for en in p['entries']:
                    l2, a2, b2 = en['lab']
                    hits.append((de2000(L, a, b, l2, a2, b2), name, en))
            hits.sort(key=lambda x: x[0])
            self._own_hits = hits[:10]
            cv.delete('all')
            mine = '#%02x%02x%02x' % lab_to_rgb(L, a, b)
            if not hits:
                cv.create_text(320, 40, text="이 폴더에는 색이 없습니다", fill='#888',
                               font=('맑은 고딕', 12))
                return
            for i, (dE, name, en) in enumerate(hits[:10]):
                y = 4 + i * 58
                rgb = '#%02x%02x%02x' % lab_to_rgb(*en['lab'])
                cv.create_rectangle(0, y, 50, y + 50, fill=mine, outline='')
                cv.create_rectangle(50, y, 100, y + 50, fill=rgb, outline='')
                cv.create_rectangle(0, y, 100, y + 50, outline='#ccc')
                feel = ("거의 같음" if dE <= 1 else "자세히 보면 다름" if dE <= 2
                        else "차이가 보임" if dE <= 5 else "다른 색")
                col = '#2e7d32' if dE <= 1 else '#ef6c00' if dE <= 2 else '#c62828'
                cv.create_text(116, y + 15, anchor='w', text=f"{i + 1}.  {en['name']}",
                               font=('맑은 고딕', 12, 'bold'), fill='#222')
                cv.create_text(116, y + 37, anchor='w', text=f"{name}", font=('맑은 고딕', 10), fill='#666')
                cv.create_text(630, y + 25, anchor='e', text=f"ΔE {dE:.2f}  {feel}",
                               font=('맑은 고딕', 12, 'bold'), fill=col)
        cb.bind('<<ComboboxSelected>>', fill)
        tk.Label(w, text="색 조각 왼쪽 반은 잰 색, 오른쪽 반은 우리 물건입니다.", bg='#ffffff', fg='#777',
                 font=('맑은 고딕', 9)).pack(anchor='w', padx=12)
        tk.Button(w, text="닫기", command=w.destroy, relief=tk.FLAT, padx=16, pady=3,
                  font=('맑은 고딕', 11), cursor='hand2').pack(pady=(4, 12))
        fill()

    def _goto_pantone(self, side):
        if not self.state_data[side]['measurements']:
            messagebox.showinfo("팬톤에서 찾기",
                                f"{'기준색' if side == 'ref' else '비교색'}을 먼저 [측정]하거나 [가져오기] 하십시오.")
            return
        try:
            self.pt_deck_var.set('모든 팬덱')
        except Exception:
            pass
        self._notebook.select(2)
        try:
            self._paint_tabs()
        except Exception:
            pass
        self._pt_nearest(side)

    def _on_calculate(self):
        # --- Источник эталона ---
        src = self.ref_source_var.get()
        ref_lab = None
        src_label = ""

        if src == 'measure':
            ref_list = self.state_data['ref']['measurements']
            if not ref_list:
                messagebox.showwarning(
                    "자료가 모자랍니다",
                    "기준색을 직접 넣거나 측정하십시오.")
                return
            ref_lab = tuple(sum(m[i] for m in ref_list) / len(ref_list)
                            for i in range(3))
            src_label = "기준색(측정값)"
        elif src == 'cmyk':
            try:
                c = float(self.man_c_var.get())
                m = float(self.man_m_var.get())
                y = float(self.man_y_var.get())
                k = float(self.man_k_var.get())
            except Exception as e:
                messagebox.showerror("입력 오류", f"CMYK 값이 잘못됐습니다: {e}")
                return
            ref_lab = cmyk_to_lab(c, m, y, k)
            src_label = f"기준색 (CMYK {c:.0f},{m:.0f},{y:.0f},{k:.0f})"
        elif src == 'rgb':
            try:
                r = int(self.man_r_var.get())
                g = int(self.man_g_var.get())
                b = int(self.man_b_var.get())
            except Exception as e:
                messagebox.showerror("입력 오류", f"RGB 값이 잘못됐습니다: {e}")
                return
            ref_lab = srgb_to_lab(r, g, b)
            src_label = f"기준색 (RGB {r},{g},{b})"
        else:
            return

        # --- Образец ---
        smp_list = self.state_data['smp']['measurements']
        if not smp_list:
            messagebox.showwarning(
                "자료가 모자랍니다",
                "비교색을 한 번 이상 측정하십시오.")
            return
        smp_lab = tuple(sum(m[i] for m in smp_list) / len(smp_list)
                        for i in range(3))

        # --- 비교 방식 ---
        palette_name = self.compare_palette_var.get()

        if palette_name == PSEUDO_CMYK:
            text = format_result_cmyk(ref_lab, smp_lab,
                                      icc_path=self.icc,
                                      threshold=self.threshold)
            header = f"=== 방식: CMYK ===\n{src_label}\n" \
                     f"비교색 ({len(smp_list)}회 평균)\n\n"
            text = header + text
        else:
            pal = self._palette_by_name(palette_name)
            if not pal or not pal['entries']:
                messagebox.showwarning(
                    "팔레트",
                    f"팔레트 '{palette_name}' 이(가) 비어 있습니다.")
                return
            try:
                n_max = int(self.n_mix_var.get())
                if n_max < 1:
                    n_max = 1
            except Exception:
                n_max = 3

            mix = propose_palette_mix(ref_lab, pal['entries'], n_max)
            text = format_result_palette(ref_lab, smp_lab,
                                         palette_name, mix)
            header = f"=== 방식: 팔레트 '{palette_name}' ===\n" \
                     f"{src_label}\n" \
                     f"비교색 ({len(smp_list)}회 평균)\n\n"
            text = header + text

        self.result_text.delete('1.0', tk.END)
        self.result_text.insert(tk.END, text)
        self._set_status("계산했습니다")

    def _on_close(self):
        self._stop_live_preview()
        self._save_palettes()
        if getattr(self, '_cloud_on', False):
            try:
                cloud.leave(self._pc_id)
            except Exception:
                pass

        if self.connected:
            try:
                rm.Disconnect()
            except Exception:
                pass
        self.destroy()


# ==========================================================================
#  MAIN
# ==========================================================================

def main():
    ap = argparse.ArgumentParser(description="RM200 측색계")
    ap.add_argument("--icc", default=None)
    ap.add_argument("--aperture", type=int, default=1, choices=[0, 1, 2])
    ap.add_argument("--timeout", type=float, default=25.0)
    ap.add_argument("--threshold", type=float, default=1.0)

    g = ap.add_mutually_exclusive_group()
    g.add_argument("--reconnect-after-measure", action="store_true",
                   help="측정할 때마다 RM200 다시 연결")
    g.add_argument("--reboot-after-measure", action="store_true",
                   help="측정할 때마다 RM200 다시 켜기")

    args = ap.parse_args()

    app = AdvisorApp(aperture=args.aperture, icc=args.icc,
                     timeout=args.timeout, threshold=args.threshold,
                     reboot_after=args.reboot_after_measure,
                     reconnect_after=args.reconnect_after_measure)
    ico = os.path.join(os.path.dirname(os.path.abspath(__file__)), "rm200color.ico")
    if os.path.exists(ico):
        try:
            app.iconbitmap(default=ico)
        except Exception:
            pass
    app.mainloop()


if __name__ == "__main__":
    main()
