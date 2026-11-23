#!/usr/bin/env python3
"""Compare the two module readers on Datalog's inference and data modules."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cetta", type=Path, required=True)
    parser.add_argument("--cetta-library-root", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    lean = root.parents[1] / "lean/mettapedia"
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    binary = args.cetta.resolve()
    grammar = root / "module/module_v1.cf"
    checker = root / "tools/check_datalog_module_reader.lean"
    library_root = args.cetta_library_root.resolve() if args.cetta_library_root else binary.parent / "lib"
    library = library_root / "lib_lbnf.metta"
    if not library.is_file():
        raise RuntimeError("the selected CeTTa library is incomplete")

    def replay(*arguments):
        return subprocess.run(["lake", "env", "lean", "--run", str(checker), *map(str, arguments)],
                              cwd=lean, text=True, capture_output=True, timeout=180)

    printed = replay("print", output)
    (output / "print.log").write_text(printed.stdout + printed.stderr)
    printed.check_returncode()
    fixtures = []
    for name, filename in (("kernel", "GroundKernel"), ("core", "Core"), ("language", "Language")):
        fixtures.extend([(name, root / f"module/gold/SouffleDatalog/{filename}.module"),
                         (f"printed-{name}", output / f"printed-{name}.module")])
    fixtures.extend((name, output / f"{name}.module") for name in
                    ("printed-collections", "printed-options"))
    sources = [binary, grammar, checker, Path(__file__), library] + [path for _, path in fixtures]
    sources += list((root / "module/gold/SouffleDatalog").glob("*.module"))
    sources += [lean / name for name in ("lean-toolchain", "lake-manifest.json", "lakefile.lean")]
    for module in ("Mettapedia.GSLT.LanguageDef.ModuleSource.LbnfDecode",
                   "Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog",
                   "Mettapedia.GSLT.LanguageDef.ModuleSource.CollectionLiteralControls"):
        relative = Path(*module.split("."))
        setup = lean / ".lake/build/ir" / relative.with_suffix(".setup.json")
        sources += [setup, lean / relative.with_suffix(".lean"),
                    lean / ".lake/build/lib/lean" / relative.with_suffix(".olean")]
        for dependency, groups in json.loads(setup.read_text())["importArts"].items():
            if dependency.startswith("Mettapedia."):
                sources.append(lean / Path(*dependency.split(".")).with_suffix(".lean"))
                sources.extend(Path(path) for group in groups for path in group)
    sources = list(dict.fromkeys(path.resolve() for path in sources))
    hashes = {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in sources}
    bindings = " ".join(f'($p{i} (langdef:parse-authored-file $parser {json.dumps(str(path))}))'
                        for i, (_, path) in enumerate(fixtures))
    cases = " ".join(f'(Case {json.dumps(name)} $p{i})' for i, (name, _) in enumerate(fixtures))
    program = f'''!(import! &self {json.dumps(str(library))})
!(let $read (lbnf:read-file {json.dumps(str(grammar))})
  (case (lbnf:finish-read $read)
    (((LbnfReadValueV1 $binding $origin $document)
      (let $syntax (lbnf:lower-document $document "ModuleV1" "ModuleFile" (SyntaxLexicalPolicyV1 bnfc-documented))
        (case $syntax
          (((SyntaxGSLTAdmittedV1 $entry)
            (let* (($parser (langdef:load-syntax-gslt-parser $syntax))
                   {bindings}
                   ($closed (langdef:close-authored-parser $parser)))
              (DatalogModuleReads {cases})))
           ($refused (GrammarRefused $refused))))))
     ($failed (ReadFailed $failed)))))
'''
    workload = output / "read.metta"
    workload.write_text(program)
    started = time.monotonic()
    run = subprocess.run([str(binary), "--lang", "he", "--profile", "extended", str(workload)],
                         text=True, capture_output=True, timeout=180)
    (output / "runtime.stdout").write_text(run.stdout)
    (output / "runtime.stderr").write_text(run.stderr)
    run.check_returncode()
    packets = [line[1:-1] for line in run.stdout.splitlines()
               if line.startswith("[(DatalogModuleReads ") and line.endswith("]")]
    if len(packets) != 1:
        raise RuntimeError("expected one complete reader packet")
    packet = output / "packet.metta"
    packet.write_text(packets[0] + "\n")
    checked = replay("check", packet)
    (output / "check.log").write_text(checked.stdout + checked.stderr)
    print(checked.stdout, end="")
    checked.check_returncode()
    for name, contents in (
            ("empty", ""), ("duplicate", packets[0] + "\n" + packets[0]),
            ("wrong-label", packets[0].replace('(Case "kernel"', '(Case "other"', 1)),
            ("wrong-production", packets[0].replace('"MFile"', '"InvalidModuleProduction"', 1))):
        malformed = output / f"{name}.metta"
        malformed.write_text(contents)
        refused = replay("check", malformed)
        (output / f"{name}.log").write_text(refused.stdout + refused.stderr)
        if refused.returncode == 0:
            raise RuntimeError(f"malformed packet accepted: {name}")
    if any(hashlib.sha256(path.read_bytes()).hexdigest() != hashes[str(path)] for path in sources):
        raise RuntimeError("qualification inputs changed during the run")
    (output / "qualification.json").write_text(json.dumps({
        "reader_cases": len(fixtures), "malformed_packets_refused": 4,
        "seconds": time.monotonic() - started, "inputs": hashes,
        "packed_parser_completeness_proved": False, "datalog_core_qualified": False,
    }, indent=2) + "\n")


if __name__ == "__main__":
    main()
