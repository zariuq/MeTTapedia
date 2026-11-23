#!/usr/bin/env python3
"""Check a grammar extension over the module corpus, retaining both packets.

This checks unique parsing and exact decoded data for previously accepted
files. Refusals remain visible. It is finite evidence, not a proof of packed
parser completeness or universal grammar equivalence.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    tools = Path(__file__).resolve().parent
    gslt, repo = tools.parent, tools.parents[2]
    lean = repo / "lean/mettapedia"
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--cetta", type=Path, required=True)
    parser.add_argument("--library-root", type=Path)
    parser.add_argument("--reference-grammar", type=Path, required=True)
    parser.add_argument("--grammar", type=Path, default=gslt / "module/module_v1.cf")
    args = parser.parse_args()
    work = args.output.resolve()
    work.mkdir(parents=True, exist_ok=False)
    binary = args.cetta.resolve()
    library_root = (args.library_root or binary.parent / "lib").resolve()
    library = library_root / "lib_lbnf.metta"
    files = sorted((gslt / "module").rglob("*.module"))
    if not files:
        raise RuntimeError("empty module corpus")
    grammars = [args.reference_grammar.resolve(), args.grammar.resolve()]
    checker = tools / "check_module_corpus.lean"
    inputs = [Path(__file__), binary, checker, *grammars, *files, *library_root.rglob("*.metta")]
    pins = {str(path): sha(path) for path in inputs}
    inventory = work / "files.txt"
    inventory.write_text("\n".join(map(str, files)) + "\n")
    packets = []
    for label, grammar in zip(["reference", "current"], grammars):
        bindings = "\n".join(f'($p{i} (langdef:parse-authored-file $parser {json.dumps(str(file))}))'
                              for i, file in enumerate(files))
        values = " ".join(f"$p{i}" for i in range(len(files)))
        source = f'''!(import! &self {json.dumps(str(library))})
!(let $read (lbnf:read-file {json.dumps(str(grammar))})
 (case (lbnf:finish-read $read)
  (((LbnfReadValueV1 $binding $origin $document)
    (let $syntax (lbnf:lower-document $document "ModuleV1" "ModuleFile" (SyntaxLexicalPolicyV1 bnfc-documented))
     (case $syntax
      (((SyntaxGSLTAdmittedV1 $entry)
        (let* (($parser (langdef:load-syntax-gslt-parser $syntax))
          {bindings}
          ($closed (langdef:close-authored-parser $parser)))
         (ModuleReads {values})))
       ($bad (GrammarRefused $bad))))))
   ($bad (ReadFailed $bad)))))
'''
        workload = work / (label + ".metta")
        workload.write_text(source)
        run = subprocess.run([str(binary), "--lang", "he", "--profile", "extended", str(workload)],
                             capture_output=True, text=True, timeout=180)
        (work / (label + ".out")).write_text(run.stdout)
        (work / (label + ".err")).write_text(run.stderr)
        run.check_returncode()
        rows = [line[1:-1] for line in run.stdout.splitlines()
                if line.startswith("[(ModuleReads ") and line.endswith("]")]
        if len(rows) != 1:
            raise RuntimeError(label + ": expected one complete reader packet")
        packet = work / (label + "-packet.metta")
        packet.write_text(rows[0] + "\n")
        packets.append(packet)
    replay = subprocess.run(["lake", "env", "lean", "--run", str(checker), str(inventory),
                             *map(str, packets)], cwd=lean, capture_output=True, text=True, timeout=180)
    (work / "compare.out").write_text(replay.stdout)
    (work / "compare.err").write_text(replay.stderr)
    replay.check_returncode()
    rows = json.loads(replay.stdout)
    changed = [name for name, digest in pins.items() if sha(name) != digest]
    record = {"passed": not changed, "files": len(files), "rows": rows, "input_pins": pins,
              "changed_inputs": changed, "accepted": sum(row["accepted"] for row in rows),
              "newly_accepted": sum(row["accepted"] and not row["previouslyAccepted"] for row in rows),
              "refused": [row["file"] for row in rows if not row["accepted"]],
              "universal_parser_completeness": False}
    (work / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({key: record[key] for key in ["passed", "files", "accepted", "newly_accepted", "refused"]}))
    if not record["passed"]:
        raise RuntimeError("grammar qualification inputs changed")


if __name__ == "__main__":
    main()
