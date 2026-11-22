# -*- coding: utf-8 -*-
"""RM200 측색계 시작 파일: 경로와 버전을 정하고 본 프로그램을 엽니다."""
import os, sys, traceback
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
try:
    with open(os.path.join(HERE, "VERSION"), encoding="utf-8") as f:
        os.environ["RM200_APP_VERSION"] = f.read().strip()
except Exception:
    pass
pal_dir = os.path.join(ROOT, "내_팔레트")
os.makedirs(pal_dir, exist_ok=True)
os.environ.setdefault("RM200_PALETTES", os.path.join(pal_dir, "palettes.json"))


# Ver 0.26: 새 폴더에 처음 풀었으면, 옆에 있는 예전 판 폴더의 내 팔레트·이색 장부를 가져옴(예전 것은 그대로 둠)
def _bring_old():
    import glob, shutil
    want = ("palettes.json", "cm_log.json")
    if any(os.path.exists(os.path.join(pal_dir, n)) for n in want):
        return
    parent = os.path.dirname(ROOT)
    cands = []
    for d in glob.glob(os.path.join(parent, "*", "내_팔레트")) + glob.glob(os.path.join(parent, "*", "*", "내_팔레트")):
        if os.path.normcase(os.path.abspath(d)) == os.path.normcase(os.path.abspath(pal_dir)):
            continue
        t = max([os.path.getmtime(os.path.join(d, n)) for n in want if os.path.exists(os.path.join(d, n))] or [0])
        if t:
            cands.append((t, d))
    if not cands:
        return
    src = sorted(cands)[-1][1]
    for n in want:
        f = os.path.join(src, n)
        if os.path.exists(f):
            shutil.copy2(f, os.path.join(pal_dir, n))
    with open(os.path.join(pal_dir, "가져온_곳.txt"), "w", encoding="utf-8") as f:
        f.write("예전 판 폴더에서 가져왔습니다: " + src + "\n")


if not os.environ.get("RM200_NO_INSTALL_ASK"):
    try:
        _bring_old()
    except Exception:
        pass
os.chdir(ROOT)
sys.argv = [sys.argv[0]] + sys.argv[1:]
try:
    import rm200_color
    rm200_color.main()
except SystemExit:
    pass
except BaseException:
    msg = traceback.format_exc()
    try:
        with open(os.path.join(ROOT, "오류기록.txt"), "a", encoding="utf-8") as f:
            f.write(msg + "\n")
    except Exception:
        pass
    try:
        import tkinter as tk
        from tkinter import messagebox
        r = tk.Tk(); r.withdraw()
        messagebox.showerror("RM200 측색계", "프로그램을 여는 중 문제가 생겼습니다.\n"
                             "프로그램 폴더의 오류기록.txt 를 보내 주십시오.\n\n" + msg[-800:])
    except Exception:
        pass
