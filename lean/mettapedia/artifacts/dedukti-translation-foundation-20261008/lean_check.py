from pathlib import Path
import os, sys
overlay=Path(__file__).resolve().parent / "checked"
os.environ["LEAN_PATH"]=str(overlay)+os.pathsep+os.environ.get("LEAN_PATH", "")
os.execvp("lean", ["lean", "-M", "24576", *sys.argv[1:]])
