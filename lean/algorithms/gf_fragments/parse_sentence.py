#!/usr/bin/env python3
"""Parse a sentence through GF ParseEng and return the tree as JSON.

Uses the C runtime (pgf Python bindings) for speed and low memory.

Usage: python3 gf_fragments/parse_sentence.py "the moon is less bright than the sun"
Output: JSON {"trees": [...], "errors": [...]}
"""
import json, sys, os
from pathlib import Path

GF_LD = "/home/zar/.local/gf-extract/usr/lib"
PGF_PY_EGG = "/home/zar/.local/gf-extract/usr/local/lib/python3.12/dist-packages/pgf-1.1-py3.12-linux-x86_64.egg"
DEFAULT_PGF_PATHS = [
    Path("/home/zar/claude/gf-wordnet/build/ParseEng.pgf"),
    Path("/home/zar/claude/lean-projects/algorithms/gf_fragments/generated/GrammarEng.project_core.pgf"),
]


def ensure_runtime_libs():
    cur = os.environ.get("LD_LIBRARY_PATH", "")
    parts = [x for x in cur.split(":") if x]
    if GF_LD in parts:
        return
    env = os.environ.copy()
    env["LD_LIBRARY_PATH"] = ":".join([GF_LD] + parts)
    os.execvpe(sys.executable, [sys.executable, __file__, *sys.argv[1:]], env)


def choose_pgf_path() -> Path | None:
    explicit = os.environ.get("GF_PARSEENG_PGF")
    if explicit:
        p = Path(explicit)
        return p if p.exists() else None
    for p in DEFAULT_PGF_PATHS:
        if p.exists():
            return p
    return None

def main():
    if len(sys.argv) < 2:
        print(json.dumps({"error": "usage: parse_sentence.py <sentence>"}))
        sys.exit(1)

    ensure_runtime_libs()
    sentence = sys.argv[1]
    pgf_path = choose_pgf_path()
    if pgf_path is None:
        print(json.dumps({
            "trees": [],
            "errors": ["no PGF found; build /home/zar/claude/gf-wordnet/build/ParseEng.pgf or set GF_PARSEENG_PGF"],
        }))
        return

    try:
        if PGF_PY_EGG not in sys.path:
            sys.path.insert(0, PGF_PY_EGG)
        import pgf
    except ImportError:
        pgf = None

    if pgf is not None:
        try:
            g = pgf.readPGF(str(pgf_path))
            lang_name = "ParseEng" if "ParseEng" in g.languages else next(iter(g.languages.keys()))
            eng = g.languages[lang_name]
            trees = []
            for i, (prob, tree) in enumerate(eng.parse(sentence, cat=g.startCat)):
                trees.append(str(tree))
                if i >= 2:
                    break
            print(json.dumps({"trees": trees, "errors": []}))
            return
        except pgf.ParseError as e:
            print(json.dumps({"trees": [], "errors": [str(e)]}))
            return
        except Exception as e:
            pass  # fall through to Haskell CLI

    if True:  # Haskell CLI fallback
        # Fall back to GF Haskell CLI
        import subprocess
        gf_bin = os.environ.get("GF_BIN", "/home/zar/.local/gf-extract/usr/bin/gf")
        gf_lib = os.environ.get("GF_LIB", "")
        env = dict(os.environ)
        if gf_lib:
            env["LD_LIBRARY_PATH"] = gf_lib + ":" + env.get("LD_LIBRARY_PATH", "")
        cmd = f'p -lang=ParseEng "{sentence}"'
        result = subprocess.run(
            [gf_bin, "--run", str(pgf_path)],
            input=cmd, capture_output=True, text=True, env=env, timeout=60
        )
        lines = [l.strip() for l in result.stdout.strip().split("\n") if l.strip()]
        if lines and "The parser failed" not in result.stdout:
            print(json.dumps({"trees": lines[:3], "errors": []}))
        else:
            print(json.dumps({"trees": [], "errors": [result.stdout.strip() or "parse failed"]}))

if __name__ == "__main__":
    main()
