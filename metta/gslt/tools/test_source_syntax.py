#!/usr/bin/env python3
"""Check retained source cores and both round trips through native packed parsing.

The supplied grammar gates retain the actual native reader, ABI, selection
policy and original selected packets. This gate checks syntax preservation;
runtime IR lowering and complete native-forest coverage remain separate.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

from packed_source_reader import LEAN, REPO, TOOLS


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, required=True)
    for name in ["ocaml", "maude", "erlang"]:
        parser.add_argument("--" + name + "-source-gate", type=Path, required=True)
    parser.add_argument("--timeout", type=float, default=120)
    args = parser.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    tool = TOOLS / "source_syntax.lean"
    prefix = ["lake", "env", "lean", "-DwarningAsError=true", "--run", str(tool)]
    commands, results, negatives = [], [], []
    inputs = {Path(__file__), tool, TOOLS / "packed_source_reader.py"}
    modules = REPO / "lean/mettapedia/Mettapedia/GSLT/LanguageDef/ModuleFormat"
    inputs.update(modules / (name + ".lean") for name in [
        "ScalarSyntaxCore", "ScalarSyntaxReification", "ScalarSyntaxPrinting", "ScalarSyntaxCST", "ScalarSyntaxReader",
        "SourcePacket", "SourcePacketCertificate", "SourceSyntax", "SourceSyntaxExport", "SourceSyntaxViewLaws",
        "GoldCoreSyntax", "GoldCoreSyntaxViews", "GoldCoreSyntaxReaders"])
    inputs.update(REPO / "metta/gslt/module/gold" / name for name in [
        "SourceLexical.module", "OCaml/Syntax.module", "Maude/Syntax.module", "Erlang/Syntax.module"])
    pins = {}

    def remember():
        for path in inputs:
            if str(path) not in pins:
                pins[str(path)] = sha(path)
        (work / "input-pins.json").write_text(json.dumps(pins, indent=2) + "\n")

    remember()

    def run(label, command, *, accepted=True):
        started = time.monotonic()
        result = subprocess.run([str(arg) for arg in command], cwd=LEAN,
                                capture_output=True, timeout=args.timeout)
        (work / (label + ".out")).write_bytes(result.stdout)
        (work / (label + ".err")).write_bytes(result.stderr)
        commands.append({"label": label, "command": [str(arg) for arg in command],
                         "exit_code": result.returncode, "seconds": time.monotonic() - started})
        (work / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
        if (result.returncode == 0) != accepted:
            raise RuntimeError(label + ": unexpected command outcome")
        if not accepted and b"selected source packet failed independent certificate replay" not in result.stdout + result.stderr:
            raise RuntimeError(label + ": failure was not the intended source refusal")
        return result.stdout.decode()

    def native(family, gate, source, label):
        grammar = gate / "grammar"
        command = [gate / "native/source-reader", grammar / "reader.abi", grammar / "reader-start.term",
                   source, work / (label + ".forest"), "--select", grammar / "selection.term", 256]
        output = run(label, command)
        lines = output.splitlines()
        status = json.loads(lines[0])
        rows = [line for line in lines[1:] if line.startswith("(result ")]
        if status["outcome"] != 0 or not status["accepted"] or not status["selected"] or not rows:
            raise RuntimeError(label + ": native selected parse did not finish")
        if status["semanticResults"] != len(rows):
            raise RuntimeError(label + ": selected result count differs")
        forest = work / (label + ".forest")
        if forest.stat().st_size != status["forestWireBytes"]:
            raise RuntimeError(label + ": packed forest size differs")
        return rows, status

    cases = {
        "ocaml": ["core_recursion", "core_lists", "core_mutual", "core_variants", "core_closures", "core_sort"],
        "maude": ["core_peano", "core_bags", "core_conditional", "core_vending", "core_mutex", "ambiguous_operator"],
        "erlang": ["core_sequential", "core_pingpong", "core_counter", "core_selective", "core_parallel_map",
                   "core_blocked", "core_sender_order", "core_multiple_values", "core_shadow", "core_local_shadow"],
    }
    for family, labels in cases.items():
        gate = getattr(args, family + "_source_gate").resolve()
        qualification = json.loads((gate / "qualification.json").read_text())
        if not qualification["passed"]:
            raise RuntimeError(family + ": input grammar gate is not qualified")
        grammar = gate / "grammar"
        inputs.update([gate / "qualification.json", gate / "native/source-reader",
                       grammar / "reader.abi", grammar / "reader-start.term", grammar / "selection.term"])
        remember()
        extension = {"ocaml": ".ml", "maude": ".maude", "erlang": ".core"}[family]
        extra = []
        if family == "ocaml":
            for label, text in [("variant_int", "type t = C of int;; 1;;"),
                                ("variant_bool", "type t = C of bool;; 1;;"),
                                ("unicode_comment", "(* λ 😃 *) 7;;")]:
                source = work / (label + extension)
                source.write_text(text)
                extra.append((label, source, None))
        for label in labels:
            source = gate / (label + extension)
            if not source.exists():
                source = gate / "core" / (label + extension)
            if not source.exists():
                directory = {"ocaml": "OCaml", "maude": "Maude", "erlang": "Erlang"}[family]
                source = REPO / "metta/gslt/module/gold" / directory / "examples" / (label + extension)
            extra.append((label, source, gate / (label + ".packet")))
        for label, source, original_packet in extra:
            tag = family + "-" + label
            inputs.add(source)
            remember()
            if original_packet is None:
                rows, _ = native(family, gate, source, tag + "-original")
            else:
                inputs.add(original_packet)
                remember()
                rows = [line for line in original_packet.read_text().splitlines() if line.startswith("(result ")]
            if not rows:
                raise RuntimeError(tag + ": no retained selected alternative")
            cores = []
            for alternative, row in enumerate(rows):
                stem = tag + "-" + str(alternative)
                packet = work / (stem + ".packet")
                packet.write_text(row + "\n")
                core = work / (stem + ".syntax.metta")
                printed = work / (stem + extension)
                run(stem + "-read", prefix + ["read", family, source, packet, core])
                run(stem + "-print", prefix + ["print", family, core, printed])
                if printed.read_bytes() != source.read_bytes():
                    raise RuntimeError(stem + ": source round trip differs")
                reparsed, status = native(family, gate, printed, stem + "-reparse")
                reread = []
                for index, new_row in enumerate(reparsed):
                    new_packet = work / (stem + "-reparse-" + str(index) + ".packet")
                    new_core = work / (stem + "-reparse-" + str(index) + ".syntax.metta")
                    new_packet.write_text(new_row + "\n")
                    run(stem + "-reread-" + str(index), prefix + ["read", family, printed, new_packet, new_core])
                    reread.append(sha(new_core))
                if sha(core) not in reread:
                    raise RuntimeError(stem + ": constructor-core round trip lost its alternative")
                cores.append(sha(core))
            record = {"family": family, "name": label, "alternatives": len(rows), "cores": cores,
                      "source_roundtrip": True, "core_roundtrip": True}
            results.append(record)
            (work / "results.json").write_text(json.dumps(results, indent=2) + "\n")
            print(json.dumps(record), flush=True)
            if label == labels[0]:
                sample = rows[0]
                root = re.match(r"\(result \(node ([^\s()]+)", sample)
                if root is None:
                    raise RuntimeError(family + ": selected packet has no source root")
                bad_packets = {
                    "unknown-production": "(result (node unknown-production nil) nil)",
                    "wrong-scalar": re.sub(r"\(cp [0-9]+\)", "(cp 1114112)", sample, count=1),
                    "missing-child": "(result (node " + root[1] + " nil) nil)",
                }
                for kind, bad in bad_packets.items():
                    damaged = work / (family + "-" + kind + ".packet")
                    damaged.write_text(bad + "\n")
                    target = work / (family + "-" + kind + ".syntax.metta")
                    run(family + "-" + kind, prefix + ["read", family, source, damaged, target], accepted=False)
                    if target.exists():
                        raise RuntimeError(kind + ": refusal created an output")
                    negatives.append(family + ":" + kind)
    distinct = {row["name"]: row["cores"] for row in results if row["family"] == "ocaml"}
    if distinct["variant_int"] == distinct["variant_bool"]:
        raise RuntimeError("erased variant field types were identified in retained syntax")
    if not any(len(set(row["cores"])) > 1 for row in results):
        raise RuntimeError("no distinct retained parses exercised the core round trip")
    changed = [path for path, digest in pins.items() if sha(path) != digest]
    if changed:
        raise RuntimeError("captured inputs changed during qualification")
    record = {"passed": True, "source_cases": len(results), "negative_controls": negatives,
              "results": results, "input_pins": pins, "changed_inputs": changed,
              "scope": "retained source syntax, independent printing, and both round trips through selected native packets",
              "universal_native_forest_coverage": False, "runtime_lowering_correspondence": False}
    (work / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")
    print(str(len(results)) + " source round trips and " + str(len(negatives)) + " refusals passed", flush=True)


if __name__ == "__main__":
    main()
