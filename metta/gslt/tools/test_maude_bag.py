#!/usr/bin/env python3
"""Run ordinary GOLD-BAG or GOLD-SET through the shared equation backend.

Checks whole native runs and resumption against independent source values,
and compares the same ground terms with Maude. Finite controls do not grant
general normalization, confluence or frontend certificates.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--source-work", type=Path, required=True)
    parser.add_argument("--cetta", type=Path, required=True)
    parser.add_argument("--petta-runner", type=Path, required=True)
    parser.add_argument("--maude", type=Path, required=True)
    parser.add_argument("--module", choices=["GOLD-BAG", "GOLD-SET"], default="GOLD-BAG")
    parser.add_argument("--timeout", type=int, default=180)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[3]
    lean, gslt = repo / "lean/mettapedia", repo / "metta/gslt"
    work = args.output.resolve()
    work.mkdir(parents=True, exist_ok=False)
    source_work = args.source_work.resolve()
    source_record_path = source_work / "qualification.json"
    source_record = json.loads(source_record_path.read_text())
    if not source_record["passed"] or any(sha(path) != digest for path, digest in source_record["input_pins"].items()):
        raise RuntimeError("source grammar/elaboration qualification is missing, failed or stale")
    source = gslt / "module/gold/Maude/examples/core_bags.maude"
    packet = source_work / "core_bags.packet"
    generator = gslt / "tools/generate_maude_bag_controls.lean"
    common = gslt / "tools/test_gslt_complete.sh"
    matched = re.search(r"^libraries=\((.*?)^\)", common.read_text(), re.S | re.M)
    if matched is None:
        raise RuntimeError("shared runtime library list is missing")
    libraries = [gslt / "lib" / (name + ".metta") for name in matched[1].split()]
    cetta, petta, maude = args.cetta.resolve(), args.petta_runner.resolve(), args.maude.resolve()
    reader = source_work / "native/source-reader"
    reader_inputs = [source_work / "grammar" / name for name in ["reader.abi", "reader-start.term", "selection.term"]]
    inputs = [Path(__file__), generator, common, source, packet, source_record_path, reader, *reader_inputs,
              cetta, petta, maude, *libraries]
    inputs += sorted((petta.parent / "src").rglob("*.pl"))
    for directory, names in [
        ("Mettapedia/Languages/Maude", ["Syntax", "Semantics", "Examples", "ACUFold", "ACUFlattenSubstitution",
            "BagCardinality", "BagIdempotence", "SchemaLink"]),
        ("Mettapedia/GSLT/LanguageDef/ModuleFormat", ["MaudeCompilation", "MaudeACUBagPresentation",
            "MaudeACUBagCompilation", "MaudeACUBagQuery", "MaudeACUEquationCompilation",
            "MaudeSourceLowering", "MaudeSourceResolution"]),
    ]:
        for name in names:
            relative = Path(directory) / (name + ".lean")
            inputs += [lean / relative, lean / ".lake/build/lib/lean" / relative.with_suffix(".olean")]
    pins = {str(path): sha(path) for path in inputs}

    def run(label, command, *, input_text=None, env=None):
        with (work / (label + ".out")).open("w") as out, (work / (label + ".err")).open("w") as err:
            process = subprocess.Popen(command, cwd=lean, text=True,
                stdin=subprocess.PIPE if input_text is not None else subprocess.DEVNULL,
                stdout=out, stderr=err, env=env, start_new_session=True)
            try:
                process.communicate(input_text, timeout=args.timeout)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGTERM)
                process.wait(timeout=10)
                raise
        return process, (work / (label + ".out")).read_text(), (work / (label + ".err")).read_text()

    generated = work / "generated"
    result, output, error = run("generate", ["lake", "env", "lean", "-DwarningAsError=true", "--run",
        str(generator), str(generated), str(source), str(packet), args.module])
    if result.returncode:
        raise RuntimeError("generation failed: " + (output + error)[-1500:])
    original = source.read_text()
    start = original.index("fmod " + args.module)
    stop = original.index("endfm", start) + len("endfm")
    selected_module = original[start:stop]
    altered_equation = selected_module.replace("eq card(a B) = s(card(B)) .", "eq card(a B) = card(B) .") if args.module == "GOLD-BAG" else \
        selected_module.replace("eq B B = B .", "eq B B = empty .")
    mutations = {
        "altered-equation": altered_equation,
        "missing-commutativity": selected_module.replace("ctor assoc comm id: empty", "ctor assoc id: empty", 1),
        "wrong-identity": selected_module.replace("ctor assoc comm id: empty", "ctor assoc comm id: a", 1),
    }
    refusals = []
    for label, changed_module in mutations.items():
        if changed_module == selected_module:
            raise RuntimeError(label + ": source mutation did not apply")
        changed = original[:start] + changed_module + original[stop:]
        candidate = work / (label + ".maude")
        candidate.write_text(changed)
        result, output, error = run(label + "-parse", [str(reader), str(reader_inputs[0]), str(reader_inputs[1]),
            str(candidate), str(work / (label + ".forest")), "--select", str(reader_inputs[2]), "256"])
        lines = output.splitlines()
        if result.returncode or error or not lines:
            raise RuntimeError(label + ": mutated source did not parse")
        metadata = json.loads(lines[0])
        if metadata["outcome"] != 0 or not metadata["semanticResults"]:
            raise RuntimeError(label + ": mutated source parse is incomplete")
        changed_packet = work / (label + ".packet")
        changed_packet.write_text("\n".join(lines[1:]) + "\n")
        refused_output = work / (label + "-unexpected-emission")
        result, output, error = run(label + "-emit", ["lake", "env", "lean", "-DwarningAsError=true", "--run",
            str(generator), str(refused_output), str(candidate), str(changed_packet), args.module])
        passed = result.returncode != 0 and "source rows differ from the checked equation schema" in output + error and not refused_output.exists()
        refusals.append({"label": label, "passed": passed, "exit": result.returncode})
        (work / "refusals.json").write_text(json.dumps(refusals, indent=2) + "\n")
        pins[str(candidate)], pins[str(changed_packet)] = sha(candidate), sha(changed_packet)
        if not passed:
            raise RuntimeError(label + ": source mutation was not refused at its declared boundary")
    cases = json.loads((generated / "reference-cases.json").read_text())
    scope = json.loads((generated / "scope.json").read_text())
    module_text = "\n".join(line for line in original.splitlines()
        if not re.match(r"\s*(red|reduce|rew|rewrite|search)\b", line))
    references = []
    for case in cases:
        command = module_text + f'\nred in {args.module} : {case["term"]} .\nquit\n'
        result, output, error = run("maude-" + case["label"], [str(maude), "-no-banner", "-no-advise"],
            input_text=command, env=dict(os.environ, MAUDE_LIB=str(maude.parent)))
        values = re.findall(r"^result " + re.escape(scope["resultSort"]) + r":\s*(.+)$", output, re.M)
        if args.module == "GOLD-BAG":
            expected = "s(" * case["expected"] + "0" + ")" * case["expected"]
            agrees = len(values) == 1 and re.sub(r"\s+", "", values[0]) == expected
        else:
            actual = [] if values == ["empty"] else (values[0].split() if len(values) == 1 else None)
            agrees = actual is not None and sorted(actual) == sorted(case["expected"])
        passed = result.returncode == 0 and not error and agrees
        references.append({"label": case["label"], "passed": passed, "expected": case["expected"], "values": values})
        (work / "references.json").write_text(json.dumps(references, indent=2) + "\n")
        if not passed:
            raise RuntimeError(case["label"] + ": Maude normal form disagrees")
    workload = work / "workload.metta"
    workload.write_text("\n".join(path.read_text() for path in [*libraries,
        generated / "machine.metta", generated / "controls.metta"]))
    for path in [workload, *generated.iterdir()]:
        pins[str(path)] = sha(path)
    expected_rows = [f'(MaudeBagNativeControl "{case["label"]}" true true true true)' for case in cases]
    results = []
    for engine, command in [
        ("cetta", [str(cetta), "--lang", "petta", "--quiet", str(workload)]),
        ("petta", ["bash", str(petta), "--silent", str(workload)]),
    ]:
        started = time.monotonic()
        result, output, error = run(engine, command, env=dict(os.environ, CETTA_PETTA_SEARCH_MACHINE="1"))
        rows = [line for line in output.splitlines() if line.startswith("(MaudeBagNativeControl ")]
        passed = result.returncode == 0 and not error and rows == expected_rows
        results.append({"engine": engine, "exit": result.returncode, "passed": passed,
            "checks": 4 * len(rows), "seconds": time.monotonic() - started, "rows": rows})
        (work / "results.json").write_text(json.dumps(results, indent=2) + "\n")
        print(json.dumps(results[-1]), flush=True)
        if not passed:
            raise RuntimeError(engine + ": native cardinality controls failed")
    unchanged = all(sha(path) == digest for path, digest in pins.items())
    record = {"passed": unchanged, "inputs_current": unchanged, "input_pins": pins,
        "controls": len(cases), "checks_per_engine": 4 * len(cases), "references": references, "refusals": refusals,
        "source_module": args.module,
        "scope": "source-connected equation stage; module and universal compiler certificates remain open"}
    (work / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")
    if not unchanged:
        raise RuntimeError("an input changed during qualification")


if __name__ == "__main__":
    main()
