#!/usr/bin/env python3
"""Compare admitted native-source cases with GNU Prolog and SWI-Prolog.

Canonical terms are compared in the LP carrier after numbering variables.
This supplements profile qualification; an engine's extra syntax is not an
ISO conformance oracle for refused cases.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from packed_source_reader import Commands, LEAN, TOOLS


def quoted_atom(text):
    return "'" + str(text).replace("\\", "\\\\").replace("'", "\\'") + "'"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-work", required=True, type=Path)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--gnu-prolog", required=True, type=Path)
    parser.add_argument("--swipl", required=True, type=Path)
    parser.add_argument("--lean", type=Path)
    args = parser.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    commands = Commands(work / "commands")
    lean = [args.lean] if args.lean else ["lake", "env", "lean"]
    results = []
    for case in json.loads((args.source_work / "results.json").read_text()):
        if not case["alternatives"]:
            continue
        dialect, name = case["case"].split("-", 1)
        source = (args.source_work / (name + ".pl")).resolve()
        canonical = work / (case["case"] + ".pl")
        goal = (
            "set_prolog_flag(double_quotes," + ("codes" if dialect == "iso" else "string") + "),"
            "catch((open(" + quoted_atom(source) + ",read,S),read_term(S,T,[]),"
            "read_term(S,E,[]),close(S),(E==end_of_file->true;halt(3)),numbervars(T,0,_),"
            "open(" + quoted_atom(canonical) + ",write,O),"
            "write_term(O,T,[quoted(true),ignore_ops(true),numbervars(false)]),"
            "write(O,'.'),nl(O),close(O)),_,halt(2)),halt"
        )
        engine = [args.gnu_prolog, "--query-goal", goal] if dialect == "iso" else [args.swipl, "-q", "-g", goal]
        commands.run(case["case"] + "-reference", engine)
        commands.run(case["case"] + "-agreement", [*lean, "--run", TOOLS / "check_prolog_reference.lean",
            dialect, source, canonical])
        results.append(dict(case=case["case"], canonical=canonical.read_text(), matched=True))
        (work / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    pins = {name: hashlib.sha256(path.resolve().read_bytes()).hexdigest()
            for name, path in (("gnu-prolog", args.gnu_prolog), ("swi-prolog", args.swipl))}
    (work / "qualification.json").write_text(json.dumps(dict(cases=len(results), binaries=pins), indent=2) + "\n")
    print(json.dumps(dict(external_term_agreements=len(results))))


if __name__ == "__main__":
    main()
