# -*- coding: utf-8 -*-
"""Ver 0.26: 깃허브(ds4eqm-lgtm/rm200-color)에서 새 판을 받아 프로그램 파일만 바꿉니다.

- update/version.json: {"ver": "0.27", "files": {"rm200_color.py": "<sha256>", ...}, "full": false}
- 바뀐 파일만 app/ 에서 받아 sha256 을 확인한 뒤 tools/app 에 넣습니다.
  넣기 전 파일은 tools/app_이전 에 보관합니다. 내_팔레트(자료)는 건드리지 않습니다.
- "full": true 면 파이썬 같은 바탕 부품도 바뀐 판이라 새 압축을 받아야 한다고 알려 줍니다.
"""
import hashlib
import json
import os
import shutil
import urllib.request

REPO = "ds4eqm-lgtm/rm200-color"
RAW = f"https://raw.githubusercontent.com/{REPO}/main"
PAGE = f"https://github.com/{REPO}"
SETUP = f"{RAW}/download/RM200_setup.zip"
HERE = os.path.dirname(os.path.abspath(__file__))
TIMEOUT = 15


def vkey(v):
    try:
        return tuple(int(x) for x in str(v).strip().split("."))
    except Exception:
        return (0,)


def _get(url):
    r = urllib.request.Request(url + ("&" if "?" in url else "?") + "nocache=1",
                               headers={"Cache-Control": "no-cache", "User-Agent": "rm200-color"})
    with urllib.request.urlopen(r, timeout=TIMEOUT) as resp:
        return resp.read()


def check(cur):
    """새 판 정보(dict) 또는 None."""
    info = json.loads(_get(f"{RAW}/update/version.json").decode("utf-8"))
    if vkey(info.get("ver")) > vkey(cur):
        return info
    return None


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for b in iter(lambda: f.read(1 << 16), b""):
            h.update(b)
    return h.hexdigest()


def apply(info, app_dir=HERE):
    """바뀐 파일을 받아 넣음. 바꾼 파일 수를 돌려줌. 하나라도 틀리면 아무것도 안 바꿈."""
    files = info.get("files", {})
    stage = os.path.join(os.path.dirname(app_dir), "app_새판")
    if os.path.isdir(stage):
        shutil.rmtree(stage, ignore_errors=True)
    os.makedirs(stage)
    todo = []
    for name, want in files.items():
        if "/" in name or "\\" in name or name.startswith("."):
            continue
        cur = os.path.join(app_dir, name)
        if os.path.exists(cur) and sha(cur) == want:
            continue
        data = _get(f"{RAW}/app/{name}")
        if hashlib.sha256(data).hexdigest() != want:
            shutil.rmtree(stage, ignore_errors=True)
            raise IOError(f"{name} 받은 내용이 맞지 않습니다(다음에 다시)")
        with open(os.path.join(stage, name), "wb") as f:
            f.write(data)
        todo.append(name)
    keep = os.path.join(os.path.dirname(app_dir), "app_이전")
    os.makedirs(keep, exist_ok=True)
    for name in todo:
        cur = os.path.join(app_dir, name)
        if os.path.exists(cur):
            shutil.copy2(cur, os.path.join(keep, name))
    for name in todo:
        os.replace(os.path.join(stage, name), os.path.join(app_dir, name))
    with open(os.path.join(app_dir, "VERSION"), "w", encoding="utf-8") as f:
        f.write(str(info["ver"]))
    shutil.rmtree(stage, ignore_errors=True)
    return len(todo)
