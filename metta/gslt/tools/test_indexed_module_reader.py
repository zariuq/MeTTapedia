#!/usr/bin/env python3
"""Qualify the indexed .module reader and its explicit Nat/Vec admission profile."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cetta", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    lean = root.parents[1] / "lean/mettapedia"
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    binary = args.cetta.resolve()
    grammar = root / "module/module_v1.cf"
    source = root / "module/IndexedNatVec.module"
    original = source.read_text()

    def changed(old, new):
        if original.count(old) != 1:
            raise RuntimeError(f"fixture edit is not unique: {old}")
        return original.replace(old, new)

    cases = [
        ("valid", original),
        ("alpha", changed("Cons (n : Nat, a : A, xs : Vec A n) : Vec A (Succ n)",
                          "Cons (k : Nat, element : A, tail : Vec A k) : Vec A (Succ k)")),
        ("negative-field", changed("xs : Vec A n", "xs : (Vec A n -> A)")),
        ("payload-shadow", changed("a : A", "n : A")),
        ("recursive-shadow", changed("xs : Vec A n", "n : Vec A n")),
        ("global-shadow", changed("n : Nat, a : A", "Zero : Nat, a : A")),
        ("wrong-result", changed("Nil () : Vec A Zero", "Nil () : Nat")),
        ("wrong-parameter", changed("Vec parameters (A : Type)", "Vec parameters (B : Type)")),
        ("wrong-entry", changed("theory Data()", "theory Other()")),
        ("extra-import", 'import "Other.module" as other\n' + original),
        ("duplicate-constructor", changed("Cons (", "Nil (")),
        ("unknown-field", changed("a : A", "a : Other")),
    ]
    bindings = []
    packets = []
    for i, (name, contents) in enumerate(cases):
        fixture = output / f"{name}.module"
        fixture.write_text(contents)
        bindings.append(f'($case{i} (langdef:parse-authored-file $parser {json.dumps(str(fixture))}))')
        packets.append(f'(Case {json.dumps(name)} $case{i})')
    program = f'''!(import! &self {json.dumps(str(binary.parent / "lib/lib_lbnf.metta"))})
!(let $read (lbnf:read-file {json.dumps(str(grammar))})
  (case (lbnf:finish-read $read)
    (((LbnfReadValueV1 $binding $origin $document)
      (let $syntax (lbnf:lower-document $document "ModuleV1" "ModuleFile" (SyntaxLexicalPolicyV1 bnfc-documented))
        (case $syntax
          (((SyntaxGSLTAdmittedV1 $entry)
            (let* (($parser (langdef:load-syntax-gslt-parser $syntax))
                   {" ".join(bindings)}
                   ($closed (langdef:close-authored-parser $parser)))
              (IndexedModuleReads {" ".join(packets)})))
           ($refused (GrammarRefused $refused))))))
     ($failed (ReadFailed $failed)))))
'''
    program_file = output / "read.metta"
    program_file.write_text(program)
    start = time.monotonic()
    run = subprocess.run([str(binary), "--lang", "he", "--profile", "extended", str(program_file)],
                         text=True, capture_output=True, check=True, timeout=180)
    (output / "runtime.stdout").write_text(run.stdout)
    (output / "runtime.stderr").write_text(run.stderr)
    lines = [line for line in run.stdout.splitlines() if line.startswith("[(IndexedModuleReads ")]
    if len(lines) != 1 or not lines[0].endswith("]"):
        raise RuntimeError("runtime did not publish one complete indexed reader packet")
    packet = output / "packet.metta"
    packet.write_text(lines[0][1:-1] + "\n")
    command = (["lean"] if os.environ.get("LEAN_PATH") else ["lake", "env", "lean"]) + ["--run", str(root / "tools/check_indexed_module_reader.lean"), str(packet)]
    replay = subprocess.run(command, cwd=lean, text=True, capture_output=True, timeout=180)
    (output / "replay.stdout").write_text(replay.stdout)
    (output / "replay.stderr").write_text(replay.stderr)
    print(replay.stdout, end="")
    print(replay.stderr, end="")
    replay.check_returncode()
    original_packet = packet.read_text()
    def synthetic(trees):
        return '(IndexedModuleReads ' + ' '.join(
            f'(Case {json.dumps(label)} (LangDef:AuthoredParseAccepted ModuleV1 "" "" ({trees})))'
            for label, _ in cases) + ')'
    malformed = [
        ("empty-packet", "", "expected one indexed reader packet"),
        ("duplicate-packet", original_packet + original_packet, "expected one indexed reader packet"),
        ("wrong-envelope", original_packet.replace("IndexedModuleReads", "WrongEnvelope", 1),
         "unexpected indexed reader envelope"),
        ("unknown-production", original_packet.replace('"MFile"', '"UnknownProduction"', 1),
         "unexpected module file"),
        ("wrong-case-identity", original_packet.replace('(Case "valid"', '(Case "other"', 1),
         "reordered or duplicate indexed reader case"),
        ("missing-parse", synthetic(""), "exactly one source parse required"),
        ("ambiguous-parse", synthetic("a b"), "exactly one source parse required"),
    ]
    process_controls = []
    for label, contents, diagnostic in malformed:
        mutation = output / f"{label}.metta"
        mutation.write_text(contents)
        result = subprocess.run(command[:-1] + [str(mutation)], cwd=lean,
                                text=True, capture_output=True, timeout=180)
        log = result.stdout + result.stderr
        (output / f"{label}.log").write_text(log)
        passed = result.returncode != 0 and diagnostic in log
        process_controls.append({"name": label, "passed": passed})
        if not passed:
            raise RuntimeError(f"malformed packet control failed: {label}\n{log}")
        print(f"(IndexedModulePacketControl {label} true)")
    record = {
        "cases": len(cases), "passed": len(cases), "mode": "he", "profile": "extended",
        "binary_sha256": hashlib.sha256(binary.read_bytes()).hexdigest(),
        "grammar_sha256": hashlib.sha256(grammar.read_bytes()).hexdigest(),
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "seconds": round(time.monotonic() - start, 3),
        "packet_controls": process_controls,
        "prime_execution_qualified": False, "packed_parser_completeness_proved": False,
    }
    (output / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")


if __name__ == "__main__":
    main()
