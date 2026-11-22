# -*- coding: utf-8 -*-
"""엑스라이트 동기화 서버(sync.xrite.com)와 통신: 이 기계 번호로 파일 목록 보기, 팬덱 받기.
기계에는 아무것도 쓰지 않습니다(PC 쪽 자료만 받음)."""
import re, html, json, os, urllib.request

URL = "https://sync.xrite.com/v3/syncsvc.asmx"
ACTIVE = False   # 지금 서버와 주고받는 중인지(불빛용)


def _soap(action, body, timeout=20):
    global ACTIVE
    ACTIVE = True
    try:
        env = ('<?xml version="1.0" encoding="utf-8"?><s:Envelope xmlns:s="http://schemas.xmlsoap.org/soap/envelope/">'
               f'<s:Body>{body}</s:Body></s:Envelope>').encode('utf-8')
        req = urllib.request.Request(URL, data=env, headers={
            'Content-Type': 'text/xml; charset=utf-8',
            'SOAPAction': f'"http://sync.xrite.com/v3/SyncSVC/{action}"'})
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return r.read().decode('utf-8', 'replace')
    finally:
        ACTIVE = False


def chip_key(chip_hex):
    """GetChipId() 의 '0x3bb92b760000001a' → '3b-b92b76000000'"""
    h = chip_hex.lower().replace('0x', '').replace(' ', '').replace('-', '')
    return '3b-' + h[2:14]


def open_session(serial, chip):
    x = _soap('OpenDeviceSession',
              '<OpenDeviceSession xmlns="http://sync.xrite.com/v3/SyncSVC">'
              f'<deviceID>{serial}</deviceID><securityKey>{chip}</securityKey>'
              '<securityType>1</securityType><language>en</language></OpenDeviceSession>')
    m = re.search(r'<SessionId>([^<]+)</SessionId>', x)
    if not m:
        msg = re.search(r'<StatusMessage>([^<]*)', x)
        raise Exception("엑스라이트 서버가 이 기계를 받아 주지 않았습니다: " + (msg.group(1) if msg else '?'))
    return m.group(1)


def available_files(session):
    x = _soap('GetAvailableFiles',
              '<GetAvailableFiles xmlns="http://sync.xrite.com/v3/SyncSVC">'
              f'<SessionID>{session}</SessionID><FileType>Any</FileType></GetAvailableFiles>')
    out = []
    for fi in re.findall(r'<FileInfo>(.*?)</FileInfo>', x, re.S):
        d = {}
        for k in ('FileType', 'SKU', 'Description', 'VersionString', 'VersionDate', 'ByteLength', 'FileURL'):
            m = re.search(f'<{k}>(.*?)</{k}>', fi, re.S)
            d[k] = html.unescape(m.group(1)) if m else ''
        out.append(d)
    return out


def vkey(v):
    try:
        return tuple(int(x) for x in v.split('.'))
    except Exception:
        return (0,)


def download(url, path, progress=None):
    global ACTIVE
    ACTIVE = True
    try:
        tmp = path + '.part'
        with urllib.request.urlopen(url, timeout=60) as r, open(tmp, 'wb') as f:
            total = int(r.headers.get('Content-Length') or 0); got = 0
            while True:
                b = r.read(65536)
                if not b:
                    break
                f.write(b); got += len(b)
                if progress:
                    progress(got, total)
        os.replace(tmp, path)
    finally:
        ACTIVE = False


_OBJ = re.compile(r'<cc:Object ObjectType="FandeckColor" Name="([^"]*)"[^>]*>(.*?)</cc:Object>', re.S)
_LAB = re.compile(r'<cc:ColorCIELab ColorSpecification="CS-GE\.D65-10">\s*<cc:L>([-\d.eE]+)</cc:L>\s*'
                  r'<cc:A>([-\d.eE]+)</cc:A>\s*<cc:B>([-\d.eE]+)</cc:B>', re.S)


def parse_fdk(path):
    t = open(path, encoding='utf-8', errors='replace').read()
    cols = []
    for m in _OBJ.finditer(t):
        l = _LAB.search(m.group(2))
        if l:
            cols.append([m.group(1).strip(), round(float(l.group(1)), 2),
                         round(float(l.group(2)), 2), round(float(l.group(3)), 2)])
    return cols
