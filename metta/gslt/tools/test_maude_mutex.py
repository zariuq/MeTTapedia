#!/usr/bin/env python3
"""Compose mutex E normalization, R exploration and query matching.

The same complete graph and safety-pattern substitutions are checked with
Maude. A second permit must expose a counterexample. This finite gate does
not replace the retained universal E/R coherence and source proofs.
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
        raise RuntimeError("source qualification is missing, failed or stale")
    source = gslt / "module/gold/Maude/examples/core_mutex.maude"
    packet = source_work / "core_mutex.packet"
    generator = gslt / "tools/generate_maude_mutex_controls.lean"
    common = gslt / "tools/test_gslt_complete.sh"
    match = re.search(r"^libraries=\((.*?)^\)", common.read_text(), re.S | re.M)
    if match is None:
        raise RuntimeError("shared runtime library list is missing")
    libraries = [gslt / "lib" / (name + ".metta") for name in match[1].split()]
    libraries.append(gslt / "lib/gslt_maude_query.metta")
    cetta, petta, maude = args.cetta.resolve(), args.petta_runner.resolve(), args.maude.resolve()
    reader = source_work / "native/source-reader"
    reader_inputs = [source_work / "grammar" / name for name in ["reader.abi", "reader-start.term", "selection.term"]]
    inputs = [Path(__file__), generator, common, source, packet, source_record_path, reader, *reader_inputs,
              cetta, petta, maude, *libraries]
    inputs += sorted((petta.parent / "src").rglob("*.pl"))
    for directory, names in [
        ("Mettapedia/Languages/Maude", ["Syntax", "Semantics", "Examples", "ACUFold", "MutexNormalization", "SchemaLink"]),
        ("Mettapedia/GSLT/LanguageDef/ModuleFormat", ["MaudeCompilation", "MaudeACUBagPresentation",
            "MaudeACUBagCompilation", "MaudeACUBagQuery", "MaudeACUQueryController", "MaudeACUEquationCompilation",
            "MaudeACUStagePair", "MaudeSourceLowering", "MaudeSourceResolution"]),
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
        str(generator), str(generated), str(source), str(packet)])
    if result.returncode:
        raise RuntimeError("generation failed: " + (output + error)[-1500:])
    original = source.read_text()
    mutations = {
        "altered-initialization": original.replace("eq init = idle1 idle2 permit .", "eq init = idle1 idle2 permit permit ."),
        "altered-rule": original.replace("[enter1] : idle1 permit => crit1 .", "[enter1] : idle1 => crit1 ."),
        "missing-commutativity": original.replace("ctor assoc comm id: empty", "ctor assoc id: empty"),
    }
    refusals = []
    for label, changed in mutations.items():
        if changed == original:
            raise RuntimeError(label + ": source mutation did not apply")
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
            str(generator), str(refused_output), str(candidate), str(changed_packet)])
        passed = result.returncode != 0 and "source rows differ from the checked mutex schema" in output + error and not refused_output.exists()
        refusals.append({"label": label, "passed": passed, "exit": result.returncode})
        (work / "refusals.json").write_text(json.dumps(refusals, indent=2) + "\n")
        pins[str(candidate)], pins[str(changed_packet)] = sha(candidate), sha(changed_packet)
        if not passed:
            raise RuntimeError(label + ": source mutation was not refused at its declared boundary")
    cases = json.loads((generated / "reference-cases.json").read_text())
    module_text = original.split("search ", 1)[0]
    references = []
    for case in cases:
        observed = []
        passed = True
        for suffix, target, expected in [("graph", "M", case["reachable"]), ("pattern", "crit1 crit2 M", case["solutions"])]:
            query = module_text + f'\nsearch in GOLD-MUTEX : {case["source"]} =>* {target} .\nquit\n'
            result, output, error = run("maude-" + case["label"] + "-" + suffix,
                [str(maude), "-no-banner", "-no-advise"], input_text=query,
                env=dict(os.environ, MAUDE_LIB=str(maude.parent)))
            actual = {tuple(sorted(value.split())) if value.strip() != "empty" else ()
                for value in re.findall(r"^M --> (.+)$", output, re.M)}
            expected_set = {tuple(sorted(value)) for value in expected}
            passed = passed and result.returncode == 0 and not error and actual == expected_set and (
                "No more solutions." in output or "No solution." in output)
            observed.append({"kind": suffix, "solutions": [list(v) for v in sorted(actual)]})
        references.append({"label": case["label"], "passed": passed, "observed": observed})
        (work / "references.json").write_text(json.dumps(references, indent=2) + "\n")
        if not passed:
            raise RuntimeError(case["label"] + ": Maude reference differs")
    workload = work / "workload.metta"
    workload.write_text("\n".join(path.read_text() for path in [*libraries,
        generated / "machine.metta", generated / "controls.metta"]))
    for path in [workload, *generated.iterdir()]:
        pins[str(path)] = sha(path)
    expected_rows = [f'(MaudeMutexNativeControl "{case["label"]}" true true true true true)' for case in cases]
    results = []
    for engine, command in [
        ("cetta", [str(cetta), "--lang", "petta", "--quiet", str(workload)]),
        ("petta", ["bash", str(petta), "--silent", str(workload)]),
    ]:
        started = time.monotonic()
        result, output, error = run(engine, command, env=dict(os.environ, CETTA_PETTA_SEARCH_MACHINE="1"))
        rows = [line for line in output.splitlines() if line.startswith("(MaudeMutexNativeControl ")]
        passed = result.returncode == 0 and not error and rows == expected_rows
        results.append({"engine": engine, "exit": result.returncode, "passed": passed,
            "checks": 5 * len(rows), "seconds": time.monotonic() - started, "rows": rows})
        (work / "results.json").write_text(json.dumps(results, indent=2) + "\n")
        print(json.dumps(results[-1]), flush=True)
        if not passed:
            raise RuntimeError(engine + ": native mutex composition failed")
    unchanged = all(sha(path) == digest for path, digest in pins.items())
    record = {"passed": unchanged, "inputs_current": unchanged, "input_pins": pins,
        "controls": len(cases), "checks_per_engine": 5 * len(cases), "references": references, "refusals": refusals,
        "scope": "source-connected mutex E/R/query composition; universal coherence and compiler certificates remain open"}
    (work / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")
    if not unchanged:
        raise RuntimeError("an input changed during qualification")


if __name__ == "__main__":
    main()
