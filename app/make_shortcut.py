# -*- coding: utf-8 -*-
"""바탕화면과 시작 메뉴에 'RM200 측색계' 바로가기를 만듭니다(전용 아이콘)."""
import os, base64, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
pyw = os.path.join(ROOT, "tools", "python", "pythonw.exe")
run = os.path.join(HERE, "run.py")
icon = os.path.join(HERE, "rm200color.ico")
ps = (
    "$sh=New-Object -ComObject WScript.Shell;"
    "foreach($d in @([Environment]::GetFolderPath('Desktop'),[Environment]::GetFolderPath('Programs'))){"
    "Remove-Item -LiteralPath (Join-Path $d 'RM200 색 비교기.lnk') -ErrorAction SilentlyContinue;"
    "$s=$sh.CreateShortcut((Join-Path $d 'RM200 측색계.lnk'));"
    f"$s.TargetPath='{pyw}';$s.Arguments='\"{run}\"';$s.WorkingDirectory='{ROOT}';"
    f"$s.IconLocation='{icon},0';$s.Description='RM200 측색계';$s.Save()}}"
)
enc = base64.b64encode(ps.encode("utf-16-le")).decode()
r = subprocess.run(["powershell", "-NoProfile", "-ExecutionPolicy", "Bypass", "-EncodedCommand", enc])
print("바탕화면과 시작 메뉴에 'RM200 측색계' 바로가기를 만들었습니다." if r.returncode == 0
      else "바로가기를 만들지 못했습니다.")
input("Enter 를 누르면 닫힙니다.")
