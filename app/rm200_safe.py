# -*- coding: utf-8 -*-
"""
rm200_safe: rm200lib 을 감싸서 기계를 망가뜨릴 수 있는 명령을 막는 안전 층.

기계로 나가는 모든 USB 명령을 맨 앞 2바이트(명령 번호)로 검사합니다.
허용 목록에 없는 명령은 기계로 보내지 않고 오류를 냅니다.
설정을 바꾸는 명령(조리개, 시각, 견본 책 켜기/끄기)은 확인 창에서 [예]를 눌러야 나갑니다.
"""
import os
import sys

import usb.core
import usb.control
import usb.util
import usb.backend.libusb1

import rm200lib as _lib
from rm200lib import *  # noqa: F401,F403  (읽기 함수는 그대로 씁니다)


class BlockedCommand(Exception):
    pass


# 읽기 전용, 측정, 미리보기, 다시 켜기
READ_OK = {
    0x7811: "통신 크기", 0x7812: "기계 정보", 0x7823: "여러 색 결과",
    0x782d: "부트로더 버전", 0x7701: "펌웨어 버전", 0x7807: "칩 번호",
    0x7837: "델타E 설정 읽기", 0x7724: "파일 목록", 0x782a: "모드 읽기",
    0x7905: "배터리", 0x7825: "조리개 읽기", 0x7835: "측정",
    0x7714: "다시 켜기", 0x780e: "화면 사진", 0x7722: "파일 읽기",
    0x7721: "파일 닫기", 0x7834: "미리보기 켜기/끄기", 0x7816: "미리보기 사진",
    0x7806: "온도", 0x970a: "시각 읽기", 0x9709: "단추 상태",
    0x7819: "측정 기록 수", 0x7820: "측정 기록", 0x7821: "견본 책 목록",
    0x782e: "교정 남은 시간", 0x7828: "교정 상태",
}
# 설정 변경: 확인 뒤에만
CONFIRM = {0x7824: "조리개 바꾸기", 0x7904: "기계 시각 맞추기",
           0x7822: "팬덱(색 견본 책) 켜기/끄기"}
# 파일 열기는 읽기 모드(1)만
OPEN_FILE = 0x7720

# Ver 0.19: 원격 단추 창이 기계 화면을 보여 주는 동안만 True
REMOTE_KEYS = False
_RED = [False]
# 확인 함수: GUI 가 messagebox.askyesno 로 바꿔 끼웁니다. 기본은 거절.
confirm = lambda title, text: False


def _check(data):
    data = bytes(data)
    if len(data) < 2:
        raise BlockedCommand("알 수 없는 명령")
    op = (data[0] << 8) | data[1]
    if op in READ_OK:
        return
    if op == OPEN_FILE:
        if len(data) > 2 and data[2] == 1:
            return
        raise BlockedCommand("기계 안 파일 쓰기는 이 프로그램에서 막혀 있습니다")
    if op == 0x780f:   # Ver 0.19: 기계 단추 대신 누르기(원격 단추 창에서만)
        if REMOTE_KEYS and len(data) >= 4 and ((data[2] << 8) | data[3]) in (1, 2, 3, 4, 5, 6, 7, 8):
            return
        if _RED[0] and len(data) >= 4 and ((data[2] << 8) | data[3]) in (6, 7):
            return   # Ver 0.32: 빨간 단추 누르기 도중(다른 화면이 REMOTE_KEYS 를 꺼도 놓기까지 마침)
        raise BlockedCommand("기계 단추 누르기는 [기계 원격 단추] 창에서만 됩니다")
    if op in CONFIRM:
        if confirm("기계 설정 바꾸기",
                   f"{CONFIRM[op]} 명령을 기계에 보냅니다.\n"
                   "기계 설정이 바뀝니다. 계속할까요?"):
            return
        raise BlockedCommand(f"{CONFIRM[op]}: 취소했습니다")
    raise BlockedCommand(
        f"명령 {op:04x} 는 기계 자료를 바꾸거나 지울 수 있어 막혀 있습니다")


class GuardedDevice:
    """실제 USB 장치를 감싸 쓰기 전에 명령을 검사합니다."""

    # Ver 0.33: 원본은 대답을 1초만 기다림. 측정 직후처럼 기계가 바쁘면 1초를 넘겨
    # "USB 시간 초과"가 나고, 늦게 온 그 대답이 통로에 남아 다음 명령이 앞 명령의 대답을 받음
    # → 그 뒤로 계속 USB 오류. 이제 넉넉히 기다리고, 시간 초과가 났으면 다음 명령 전에 남은 대답을 비움.
    READ_WAIT_MS = 5000

    def __init__(self, real):
        self._real = real
        self._pending = None
        self._dirty = False

    def ctrl_transfer(self, *a, **k):
        if self._dirty:
            self._drain()
        return self._real.ctrl_transfer(*a, **k)

    def _drain(self):
        for _ in range(8):
            try:
                self._real.read(0x81, 4096, 150)
            except Exception:
                break
        self._dirty = False

    def write(self, ep, data, *a, **k):
        _check(data)
        if self._dirty:
            self._drain()
        return self._real.write(ep, data, *a, **k)

    def read(self, ep, n, timeout=None, *a, **k):
        if ep == 0x81 and (timeout is None or timeout < self.READ_WAIT_MS):
            timeout = self.READ_WAIT_MS
        try:
            return self._real.read(ep, n, timeout, *a, **k)
        except Exception as e:
            m = str(e).lower()
            if 'timeout' in m or 'timed out' in m or getattr(e, 'errno', None) in (110, 60, 10060) \
                    or getattr(e, 'backend_error_code', None) == -7:
                self._dirty = True
            raise

    def __getattr__(self, name):
        return getattr(self._real, name)


def _backend():
    here = os.path.dirname(os.path.abspath(__file__))
    for p in (os.path.join(os.path.dirname(here), "libusb", "libusb-1.0.dll"),
              os.path.join(here, "libusb", "libusb-1.0.dll"),
              os.path.join(os.path.dirname(sys.executable), "libusb-1.0.dll")):
        if os.path.exists(p):
            be = usb.backend.libusb1.get_backend(find_library=lambda x, p=p: p)
            if be is not None:
                return be
    return usb.backend.libusb1.get_backend()


def _open_once(be):
    real = usb.core.find(idVendor=0x0765, idProduct=0x6001, backend=be)
    if real is None:
        if usb.core.find(idVendor=0x03EB, idProduct=0x6124, backend=be):
            raise Exception("기계가 비상 기록 모드(SAM-BA)로 잡혀 있습니다")
        raise Exception("RM200 을 찾지 못했습니다 (전원, USB 선, WinUSB 드라이버 확인)")
    # 백업점검 1.0.3 과 같은 순서. 윈도우(WinUSB)에서는 거절돼도 통신에는 지장 없음.
    # set_configuration(0) 은 기계 설정을 풀어 버려 쓰지 않습니다.
    for step in (lambda: usb.control.set_feature(real, 1),
                 lambda: real.set_configuration(1)):
        try:
            step()
        except Exception:
            pass
    _lib.dev = GuardedDevice(real)
    try:
        _lib.GetComBufSize()
    except Exception:
        Disconnect()
        raise


def Connect():
    import time
    Disconnect()          # 앞서 열어 둔 통로가 남아 있으면 먼저 닫기
    be = _backend()
    if be is None:
        raise Exception("USB 부품(libusb)을 불러오지 못했습니다. 압축을 다 풀었는지 확인하십시오")
    last = None
    for attempt in range(3):
        try:
            _open_once(be)
            return
        except NotImplementedError:
            raise Exception("USB 드라이버가 WinUSB 가 아닙니다. "
                            "기계 메뉴 → USB 드라이버 바꾸기를 하십시오")
        except Exception as e:
            last = e
            msg = str(e)
            if "찾지 못했" in msg or "SAM-BA" in msg:
                raise
            time.sleep(1.0)
    msg = str(last)
    if "Errno 13" in msg or "Access denied" in msg or "Errno 16" in msg or "busy" in msg.lower():
        raise Exception(
            "다른 프로그램이 기계를 쓰고 있어 열 수 없습니다.\n"
            "RM200 백업점검 창이나 이 프로그램 창이 하나 더 열려 있으면 모두 닫고,\n"
            "USB 선을 뺐다가 다시 꽂은 뒤 [RM200 다시 연결]을 누르십시오.\n"
            f"({msg})")
    raise last


def Disconnect():
    d = _lib.dev
    if d is not None:
        try:
            usb.util.dispose_resources(getattr(d, "_real", d))
        except Exception:
            pass
        _lib.dev = None


# 원본 오타(CommandCool) 고침
def SetAperture(aperture):
    aperture = int(aperture)
    if aperture < 0 or aperture > 2:
        raise Exception("조리개는 0=작게, 1=중간, 2=크게/자동")
    return _lib.CommandBool(b"\x78\x24" + bytes([aperture]))


def SetFandeckActive(name, state):
    return _lib.SetFandeckActive(name, int(state))


def _blocked(what):
    def f(*a, **k):
        raise BlockedCommand(f"{what} 기능은 이 프로그램에서 막혀 있습니다")
    f.__name__ = what
    return f


for _n in ("FileDelete", "EnterBootloader", "SetDeviceMode", "GenericCmd",
           "SetSerialNum", "BackupCalibData", "BLUpload", "BLUploadChunk",
           "BLAction", "BLUploadBootloader", "BLUploadFirmware",
           "BLUploadCalibration", "BLUploadWelcome", "BLEraseWelcome",
           "FileWrite", "PutFile", "UploadFile", "WriteVersionsDotDat",
           "Display565Image", "DeleteFandeck",
           "UnlockExtendedCommands"):
    globals()[_n] = _blocked(_n)

# 원본 GUI 가 찾는 이름
GetFWVersion = _lib.GetFWInfo


# ---- 0.4: 여러 일이 동시에 기계와 말하지 않도록 한 줄로 세우기 ----
import threading as _th
LOCK = _th.RLock()


def _locked(f):
    def w(*a, **k):
        with LOCK:
            return f(*a, **k)
    w.__name__ = f.__name__
    return w


_lib.CommandData = _locked(_lib.CommandData)
_lib.CommandBool = _locked(_lib.CommandBool)
_lib.GetInfo = _locked(_lib.GetInfo)
GetInfo = _lib.GetInfo


def Ping():
    """기계가 살아 있는지 짧게 물어봄(모드 읽기). 다른 일 중이면 None."""
    if _lib.dev is None:
        return False
    if not LOCK.acquire(blocking=False):
        return None
    try:
        return _lib.GetDeviceMode() is not None
    finally:
        LOCK.release()


def GetTimeDT():
    import datetime as _dt
    t = _lib.GetTime()
    if not t:
        return None
    return _dt.datetime(*[int(x) for x in t])


def internet_time():
    """인터넷 표준 시각(한국 표준시 기준 PC 지역 시각)을 가져옴. (시각, 출처)"""
    import socket, struct as _st, time as _t, datetime as _dt
    for host in ("time.bora.net", "time.kriss.re.kr", "time.windows.com", "pool.ntp.org"):
        try:
            s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            s.settimeout(2.0)
            t0 = _t.time()
            s.sendto(b"\x1b" + 47 * b"\0", (host, 123))
            data, _ = s.recvfrom(48)
            s.close()
            secs = _st.unpack("!I", data[40:44])[0] - 2208988800
            frac = _st.unpack("!I", data[44:48])[0] / 2 ** 32
            rtt = _t.time() - t0
            return _dt.datetime.fromtimestamp(secs + frac + rtt / 2), host
        except Exception:
            continue
    # NTP 가 막힌 곳: 웹 서버 시각(Date 머리글)
    import urllib.request, email.utils
    for url in ("https://www.google.com", "https://www.naver.com"):
        try:
            with urllib.request.urlopen(urllib.request.Request(url, method="HEAD"), timeout=4) as r:
                d = email.utils.parsedate_to_datetime(r.headers["Date"])
                return d.astimezone().replace(tzinfo=None), url
        except Exception:
            continue
    raise Exception("인터넷 시각을 가져오지 못했습니다(인터넷 연결 확인)")


# ---- Ver 0.8: 실제 통신 시각 기록과 USB 꽂힘 확인 ----
import time as _time
LAST_IO = 0.0


def _io_marked(f):
    def w(*a, **k):
        global LAST_IO
        LAST_IO = _time.time()
        try:
            return f(*a, **k)
        finally:
            LAST_IO = _time.time()
    w.__name__ = f.__name__
    return w


_lib.CommandData = _io_marked(_lib.CommandData)
_lib.CommandBool = _io_marked(_lib.CommandBool)
_lib.GetInfo = _io_marked(_lib.GetInfo)
GetInfo = _lib.GetInfo
_BE = None


def Present():
    """USB 에 기계가 꽂혀 있는지(통신 없이 목록만 봄)."""
    global _BE
    if _BE is None:
        _BE = _backend()
    try:
        return usb.core.find(idVendor=0x0765, idProduct=0x6001, backend=_BE) is not None
    except Exception:
        return False


# ---- Ver 0.17: 파일 읽기는 "열기 → 나눠 읽기 → 닫기" 전체를 한 줄로 ----
# 명령 하나씩만 잠그면 두 일이 같은 파일을 번갈아 열고 닫아
# 기계에 "오류 0077 no file open for reading" 이 뜸. 파일 일 전체를 잠금.
def _file_locked(f, close_on_error):
    def w(*a, **k):
        with LOCK:
            try:
                return f(*a, **k)
            except Exception:
                if not close_on_error:
                    raise
                # 읽다가 끊기면 기계 쪽 파일을 닫아 둠(다음 읽기가 꼬이지 않게)
                try:
                    _lib.CommandBool(b"\x77\x21")
                except Exception:
                    pass
                raise
    w.__name__ = f.__name__
    return w


for _n in ("FetchFile", "DownloadFile", "ReadVersionsDotDat", "SaveScreenshot",
           "GetFandecks", "SavePreview", "SaveRecordImage"):
    if hasattr(_lib, _n):
        setattr(_lib, _n, _file_locked(getattr(_lib, _n), _n == "FetchFile"))
        globals()[_n] = getattr(_lib, _n)


# ---- Ver 0.19: 기계 단추 대신 누르기 (1=가운데 2=위 3=아래 4=왼쪽 5=오른쪽) ----
def PressKey(key):
    key = int(key)
    if key not in (1, 2, 3, 4, 5, 6, 7, 8):   # 6/7 = 빨간 단추 놓기/누르고 있기, 8 = 캡처
        raise BlockedCommand("가운데·위·아래·왼쪽·오른쪽·측정 단추만 누를 수 있습니다")
    return _lib.CommandBool(b"\x78\x0f" + key.to_bytes(2, "big"))


# Ver 0.32: 위 빨간 측정 단추를 사람이 누르는 것처럼 "누르고 있기(7) → 놓기(6)".
# (0.31 의 키 8 은 실제 기계에서 오류 0027 프로토콜 오류가 남: 키 8 은 미리보기 중에만 받음)
def PressRedButton(hold=0.6):
    import time as _t
    _RED[0] = True
    try:
        a = PressKey(7)
        _t.sleep(hold)
        b = PressKey(6)
    finally:
        _RED[0] = False
    return a, b


GenerateKeyboardEvent = PressKey


# Ver 0.24: USB 선을 뺐다 꽂은 것처럼 USB 통로를 초기화하고 다시 연결 (기계 자료는 건드리지 않음)
def ResetUsb():
    with LOCK:
        d = _lib.dev
        real = getattr(d, "_real", d) if d is not None else None
        if real is None:
            be = _backend()
            real = usb.core.find(idVendor=0x0765, idProduct=0x6001, backend=be) if be else None
        if real is None:
            raise Exception("RM200 을 찾지 못했습니다 (USB 선이 빠졌거나 전원이 꺼져 있습니다)")
        try:
            real.reset()
        except Exception:
            pass
        Disconnect()
        try:
            usb.util.dispose_resources(real)
        except Exception:
            pass
        _time.sleep(1.5)
        Connect()
