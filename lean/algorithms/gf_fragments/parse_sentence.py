#!/usr/bin/env python3
"""Parse a sentence through GF ParseEng and return the tree as JSON.

Uses the C runtime (pgf Python bindings) for speed and low memory.

Usage: python3 gf_fragments/parse_sentence.py "the moon is less bright than the sun"
Output: JSON {"trees": [...], "errors": [...]}
"""
import json, sys, os

def main():
    if len(sys.argv) < 2:
        print(json.dumps({"error": "usage: parse_sentence.py <sentence>"}))
        sys.exit(1)

    sentence = sys.argv[1]
    pgf_path = "/home/zar/claude/gf-wordnet/build/ParseEng.pgf"

    try:
        import pgf
    except ImportError:
        pgf = None

    if pgf is not None:
        try:
            g = pgf.readPGF(pgf_path)
            eng = g.languages["ParseEng"]
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
        gf_bin = os.environ.get("GF_BIN", "gf")
        gf_lib = os.environ.get("GF_LIB", "")
        env = dict(os.environ)
        if gf_lib:
            env["LD_LIBRARY_PATH"] = gf_lib + ":" + env.get("LD_LIBRARY_PATH", "")
        cmd = f'p -lang=ParseEng "{sentence}"'
        result = subprocess.run(
            [gf_bin, "--run", pgf_path],
            input=cmd, capture_output=True, text=True, env=env, timeout=60
        )
        lines = [l.strip() for l in result.stdout.strip().split("\n") if l.strip()]
        if lines and "The parser failed" not in result.stdout:
            print(json.dumps({"trees": lines[:3], "errors": []}))
        else:
            print(json.dumps({"trees": [], "errors": [result.stdout.strip() or "parse failed"]}))
    except Exception as e:
        print(json.dumps({"trees": [], "errors": [str(e)]}))

if __name__ == "__main__":
    main()
