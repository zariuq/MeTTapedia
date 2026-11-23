#!/usr/bin/env python3
"""Exercise textual Nat/Vec operations through the common reader and typed replay.

This is a source-adapter qualification gate. It does not implement a parser,
an inference kernel, or the execution semantics of the proposed program.
"""

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
    parser.add_argument("--cetta-library-root", type=Path,
                        help="CeTTa library directory; defaults to lib beside the binary")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    lean = root.parents[1] / "lean/mettapedia"
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    binary = args.cetta.resolve()
    library_root = ((args.cetta_library_root.resolve() if args.cetta_library_root
                     else binary.parent / "lib"))
    lbnf_library = library_root / "lib_lbnf.metta"
    langdef_library = library_root / "langdef.metta"
    if not lbnf_library.is_file() or not langdef_library.is_file():
        raise RuntimeError("CeTTa LBNF/langdef library root is incomplete")
    grammar = root / "module/module_v1.cf"
    source = root / "module/IndexedNatVecAppend.module"
    receipt_sources = [Path(__file__).resolve(), root / "tools/check_append_source_reader.lean",
                       lbnf_library, langdef_library]
    receipt_sources += [lean / "Mettapedia/GSLT/LanguageDef" / name for name in (
        "IndexedInductiveAppendChecking.lean", "IndexedInductiveAppendSource.lean",
        "IndexedInductiveAppendElaboration.lean", "IndexedInductiveOperationSource.lean",
        "ModuleSource/LbnfDecode.lean", "ModuleSource/IndexedNatVecSource.lean")]
    receipt_sources += [lean / "Mettapedia/TypeTheory/Calculi/CumulativePiSigmaId/Declarations" / name
                        for name in ("NativeNaturalVectorFamilies.lean", "NativeNaturalVectorPrograms.lean",
                                     "NativeNaturalVectorProgramEvidence.lean",
                                     "NativeNaturalVectorComputationProfiles.lean")]
    receipt_hashes = {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                      for path in receipt_sources}
    original = source.read_text()
    binary_hash = hashlib.sha256(binary.read_bytes()).hexdigest()
    grammar_hash = hashlib.sha256(grammar.read_bytes()).hexdigest()
    source_hash = hashlib.sha256(source.read_bytes()).hexdigest()

    def changed(old, new):
        if original.count(old) != 1:
            raise RuntimeError(f"fixture edit is not unique: {old}")
        return original.replace(old, new)

    alpha = changed("Cons (n : Nat, a : A, xs : Vec A n) : Vec A (Succ n)",
                    "Cons (count : Nat, item : A, rest : Vec A count) : Vec A (Succ count)")
    alpha = alpha.replace("(Succ k)", "(Succ previous)").replace("(Add k m)", "(Add previous m)")
    alpha = alpha.replace("(Cons A k x tail)", "(Cons A previous head suffix)")
    alpha = alpha.replace("(Append A k m tail ys)", "(Append A previous m suffix ys)")
    alpha = alpha.replace("(Add k m)", "(Add previous m)").replace(" x ", " head ")
    cases = [
        ("valid", original),
        ("alpha", alpha),
        ("wrong-child", changed("(Append A k m tail ys)", "(Append A k m x ys)")),
        ("omitted-recursion", changed("(Append A k m tail ys)", "tail")),
        ("wrong-index", changed("(Append A (Succ k)", "(Append A (Zero)")),
        ("unbound", changed("~> ys;", "~> unknown;")),
        ("missing-clause", changed("      AddZero : (Add (Zero) m) ~> m;\n", "")),
        ("extra-block", changed("    Rewrites {", "    Types { Ignored; }\n    Rewrites {")),
        ("negative-field", changed("xs : Vec A n", "xs : (Vec A n -> A)")),
        ("wrong-entry", changed("theory Data()", "theory Other()")),
    ]
    bindings, packets = [], []
    for index, (label, contents) in enumerate(cases):
        fixture = output / f"{label}.module"
        fixture.write_text(contents)
        bindings.append(f'($case{index} (langdef:parse-authored-file $parser {json.dumps(str(fixture))}))')
        packets.append(f'(Case {json.dumps(label)} $case{index})')
    program = f'''!(import! &self {json.dumps(str(lbnf_library))})
!(let $read (lbnf:read-file {json.dumps(str(grammar))})
  (case (lbnf:finish-read $read)
    (((LbnfReadValueV1 $binding $origin $document)
      (let $syntax (lbnf:lower-document $document "ModuleV1" "ModuleFile" (SyntaxLexicalPolicyV1 bnfc-documented))
        (case $syntax
          (((SyntaxGSLTAdmittedV1 $entry)
            (let* (($parser (langdef:load-syntax-gslt-parser $syntax))
                   {" ".join(bindings)}
                   ($closed (langdef:close-authored-parser $parser)))
              (AppendSourceReads {" ".join(packets)})))
           ($refused (GrammarRefused $refused))))))
     ($failed (ReadFailed $failed)))))
'''
    program_file = output / "read.metta"
    program_file.write_text(program)
    started = time.monotonic()
    run = subprocess.run([str(binary), "--lang", "he", "--profile", "extended", str(program_file)],
                         text=True, capture_output=True, timeout=180)
    (output / "runtime.stdout").write_text(run.stdout)
    (output / "runtime.stderr").write_text(run.stderr)
    run.check_returncode()
    lines = [line for line in run.stdout.splitlines() if line.startswith("[(AppendSourceReads ")]
    if len(lines) != 1 or not lines[0].endswith("]"):
        raise RuntimeError("runtime did not publish one complete append reader packet")
    packet = output / "packet.metta"
    packet.write_text(lines[0][1:-1] + "\n")
    command = (["lean"] if os.environ.get("LEAN_PATH") else ["lake", "env", "lean"]) + [
        "--run", str(root / "tools/check_append_source_reader.lean"), str(packet)]
    replay = subprocess.run(command, cwd=lean, text=True, capture_output=True, timeout=180)
    (output / "replay.stdout").write_text(replay.stdout)
    (output / "replay.stderr").write_text(replay.stderr)
    print(replay.stdout, end="")
    print(replay.stderr, end="")
    replay.check_returncode()
    raw_agreement = [line for line in replay.stdout.splitlines()
                     if line.startswith("(AppendSourceRawAgreement ")]
    if raw_agreement != ["(AppendSourceRawAgreement true)"]:
        raise RuntimeError("missing or unsuccessful exact source comparison")
    policy = [line for line in replay.stdout.splitlines()
              if line.startswith("(AppendSourceCheckingPolicy ")]
    if policy != ["(AppendSourceCheckingPolicy [0, 1])"]:
        raise RuntimeError("missing or different checking policy")
    original_packet = packet.read_text()

    def synthetic(trees):
        return '(AppendSourceReads ' + ' '.join(
            f'(Case {json.dumps(label)} (LangDef:AuthoredParseAccepted ModuleV1 "" "" ({trees})))'
            for label, _ in cases) + ')'

    malformed = [
        ("empty", "", "expected one append reader packet"),
        ("duplicate", original_packet + original_packet, "expected one append reader packet"),
        ("wrong-envelope", original_packet.replace("AppendSourceReads", "OtherReads", 1),
         "unexpected append source envelope"),
        ("missing-tree", synthetic(""), "exactly one source parse required"),
        ("ambiguous-tree", synthetic("a b"), "exactly one source parse required"),
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
    if hashlib.sha256(binary.read_bytes()).hexdigest() != binary_hash:
        raise RuntimeError("runtime binary changed during qualification")
    if hashlib.sha256(grammar.read_bytes()).hexdigest() != grammar_hash:
        raise RuntimeError("grammar changed during qualification")
    if hashlib.sha256(source.read_bytes()).hexdigest() != source_hash:
        raise RuntimeError("source changed during qualification")
    if any(hashlib.sha256(Path(path).read_bytes()).hexdigest() != digest
           for path, digest in receipt_hashes.items()):
        raise RuntimeError("checking receipt sources changed during qualification")
    record = {
        "cases": len(cases), "passed": len(cases), "mode": "he", "profile": "extended",
        "binary_sha256": binary_hash,
        "grammar_sha256": grammar_hash,
        "source_sha256": source_hash,
        "seconds": round(time.monotonic() - started, 3), "packet_controls": process_controls,
        "name_policy": "declared-nullary", "raw_reader_agreement": raw_agreement[0].endswith("true)"),
        "checking_policy": "generated-declarations-natural-iota", "permitted_rows": [0, 1],
        "cetta_library_root": str(library_root),
        "receipt_sources": receipt_hashes,
        "prime_execution_qualified": False, "packed_parser_completeness_proved": False,
    }
    (output / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")


if __name__ == "__main__":
    main()
