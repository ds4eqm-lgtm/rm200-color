# -*- coding: utf-8 -*-
"""Ver 0.26: 내 팔레트·이색 장부를 여러 PC가 같이 쓰는 공용 저장소(토큰 없음).

새로고침 재고관리와 같은 Firestore(serogochim-inventory)의 'rm200' 칸에 문서 하나씩 저장합니다.
- 저장할 때마다 '마지막으로 맞춘 내용(base)'과 비교해 3갈래로 합칩니다.
  두 PC가 서로 다른 곳을 고치면 둘 다 살고, 같은 곳을 고치면 나중에 저장한 쪽이 남습니다.
  한쪽에서 지운 것은 다른 쪽이 그 사이에 고치지 않았을 때만 지워집니다.
- 인터넷이 안 되면 이 PC에만 저장하고, 다시 되면 맞춥니다.
"""
import json
import os
import socket
import time
import urllib.error
import urllib.request

API_KEY = "AIzaSyCNpACKBrRc4e0aZcy4yindQPIHSMcOp50"
BASE = ("https://firestore.googleapis.com/v1/projects/serogochim-inventory/"
        "databases/(default)/documents")
COLL = "rm200"
PRESENCE = "rm200_presence"
MAX_BYTES = 900_000
TIMEOUT = 8


def _url(path, extra=""):
    return f"{BASE}/{path}?key={API_KEY}{extra}"


def _req(method, url, body=None):
    data = json.dumps(body).encode("utf-8") if body is not None else None
    r = urllib.request.Request(url, data=data, method=method,
                               headers={"Content-Type": "application/json"})
    try:
        with urllib.request.urlopen(r, timeout=TIMEOUT) as resp:
            return resp.status, json.loads(resp.read().decode("utf-8") or "{}")
    except urllib.error.HTTPError as e:
        try:
            return e.code, json.loads(e.read().decode("utf-8") or "{}")
        except Exception:
            return e.code, {}


def get_doc(name):
    """(내용 또는 None, updateTime 또는 None). 연결 실패면 예외."""
    code, js = _req("GET", _url(f"{COLL}/{name}"))
    if code == 404:
        return None, None
    if code != 200:
        raise IOError(f"공용 저장소 읽기 실패 {code}")
    f = js.get("fields", {})
    raw = f.get("json", {}).get("stringValue")
    return (json.loads(raw) if raw else None), js.get("updateTime")


def put_doc(name, data, prev_update, who):
    """prev_update 가 그대로일 때만 씀(그 사이 다른 PC가 바꿨으면 False)."""
    raw = json.dumps(data, ensure_ascii=False, separators=(",", ":"))
    if len(raw.encode("utf-8")) > MAX_BYTES:
        raise ValueError("자료가 너무 커서 공용 저장소에 올리지 못했습니다(이 PC에는 저장됨)")
    cond = (f"&currentDocument.updateTime={prev_update}" if prev_update
            else "&currentDocument.exists=false")
    body = {"fields": {"json": {"stringValue": raw}, "by": {"stringValue": who},
                       "t": {"integerValue": str(int(time.time()))}}}
    code, js = _req("PATCH", _url(f"{COLL}/{name}", cond), body)
    if code == 200:
        return js.get("updateTime")
    if code in (400, 409, 412) or "FAILED_PRECONDITION" in json.dumps(js):
        return False
    raise IOError(f"공용 저장소 쓰기 실패 {code}")


# ---------------------------------------------------------------- 3갈래 합치기
_MISSING = object()


def merge3(base, local, remote):
    if local == remote:
        return local
    if base is _MISSING or base is None:
        base_is_none = True
    else:
        base_is_none = False
    if not base_is_none and local == base:
        return remote
    if not base_is_none and remote == base:
        return local
    if isinstance(local, dict) and isinstance(remote, dict):
        b = base if isinstance(base, dict) else {}
        out = {}
        keys = list(remote.keys()) + [k for k in local.keys() if k not in remote]
        for k in keys:
            lv = local.get(k, _MISSING)
            rv = remote.get(k, _MISSING)
            bv = b.get(k, _MISSING)
            if lv is _MISSING:          # 이 PC에서 없음
                if bv is not _MISSING and rv == bv:
                    continue            # 이 PC에서 지웠고 저쪽은 그대로 → 지움
                out[k] = rv
            elif rv is _MISSING:        # 저쪽에 없음
                if bv is not _MISSING and lv == bv:
                    continue            # 저쪽에서 지웠고 이쪽은 그대로 → 지움
                out[k] = lv
            else:
                out[k] = merge3(bv, lv, rv)
        return out
    return local                        # 같은 곳을 둘 다 고침 → 이 PC(방금 저장한 쪽)


# ---------------------------------------------------------------- 모양 바꾸기
def pal_to_map(palettes):
    """{이름: {'entries':[{'name','lab'}]}} → {이름: {'#순번 이름': [L,a,b]}} (순서 보존)."""
    out = {}
    for n, p in palettes.items():
        m = {}
        seen = {}
        for e in p.get("entries", []):
            k = e["name"]
            seen[k] = seen.get(k, 0) + 1
            if seen[k] > 1:
                k = f"{k}\u0001{seen[k]}"
            m[k] = [round(float(x), 4) for x in e["lab"]]
        out[n] = m
    return out


def map_to_pal(m):
    out = {}
    for n, ents in m.items():
        out[n] = {"entries": [{"name": k.split("\u0001")[0], "lab": tuple(v)} for k, v in ents.items()]}
    return out


def cm_to_map(cm):
    items = {}
    for it in cm.get("items", []):
        d = {k: v for k, v in it.items() if k != "records"}
        recs = {}
        for r in it.get("records", []):
            k = f"{r.get('date')}|{r.get('lot')}"
            while k in recs:
                k += "+"
            recs[k] = r
        d["records"] = recs
        items[it.get("name", "?")] = d
    return items


def map_to_cm(m):
    items = []
    for name, d in m.items():
        it = {k: v for k, v in d.items() if k != "records"}
        it["name"] = name
        it["records"] = list(d.get("records", {}).values())
        items.append(it)
    return {"items": items}


# ---------------------------------------------------------------- 맞추기
class Doc:
    """문서 하나(palettes 또는 cm)를 이 PC 파일과 맞춤. base 는 .sync 폴더에."""

    def __init__(self, name, sync_dir):
        self.name = name
        self.path = os.path.join(sync_dir, f"{name}.base.json")
        self.base, self.upd = None, None
        try:
            with open(self.path, encoding="utf-8") as f:
                js = json.load(f)
            self.base, self.upd = js.get("data"), js.get("upd")
        except Exception:
            pass

    def _keep(self, data, upd):
        self.base, self.upd = data, upd
        tmp = self.path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump({"data": data, "upd": upd}, f, ensure_ascii=False)
        os.replace(tmp, self.path)

    def sync(self, local, who):
        """local(맵) 을 공용 저장소와 맞춰 합친 맵을 돌려줌. 연결 실패면 예외."""
        for _ in range(4):
            remote, upd = get_doc(self.name)
            if remote is None:
                merged = local
            elif self.base is None:     # 이 PC 처음: 둘 다 살림(지우지 않음)
                merged = merge3(None, local, remote)
            else:
                merged = merge3(self.base, local, remote)
            if merged != remote:
                r = put_doc(self.name, merged, upd, who)
                if r is False:
                    continue            # 그 사이 다른 PC가 씀 → 다시 읽고 합침
                upd = r
            self._keep(merged, upd)
            return merged
        raise IOError("다른 PC와 동시에 저장이 겹쳐 다음에 다시 맞춥니다")


def pc_name():
    return (os.environ.get("COMPUTERNAME") or socket.gethostname() or "PC")[:40]


def beat(pid, who, ver):
    body = {"fields": {"name": {"stringValue": who}, "ver": {"stringValue": ver},
                       "t": {"integerValue": str(int(time.time()))}}}
    _req("PATCH", _url(f"{PRESENCE}/{pid}"), body)


def leave(pid):
    _req("DELETE", _url(f"{PRESENCE}/{pid}"))


def online(stale=150):
    code, js = _req("GET", _url(PRESENCE, "&pageSize=50"))
    if code != 200:
        raise IOError("접속 목록 읽기 실패")
    now = time.time()
    out = []
    for d in js.get("documents", []):
        f = d.get("fields", {})
        t = int(f.get("t", {}).get("integerValue", "0"))
        if now - t < stale:
            out.append((d["name"].rsplit("/", 1)[-1], f.get("name", {}).get("stringValue", "PC"),
                        f.get("ver", {}).get("stringValue", "")))
    return out


def add_log(items, who, tries=5):
    """Ver 0.42: 측정값을 공용 기록(rm200/meas_log, 최근 200개)에 덧붙임. 휴대폰 앱과 같은 문서.
    다른 기기와 겹치면 다시 읽고 다시 씀. 성공하면 True."""
    import random
    for _ in range(tries):
        cur, upd = get_doc("meas_log")
        lst = cur if isinstance(cur, list) else []
        lst = list(items) + lst
        if put_doc("meas_log", lst[:200], upd, who):
            return True
        time.sleep(0.3 + random.random() * 0.5)
    return False
