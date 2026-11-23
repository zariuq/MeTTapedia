#!/usr/bin/env python3
"""Qualify conditional max through the shared premise provider.

With --source-work, the original source uses its checked ground BOOL import
profile. Without it, this remains the prepared-IR gate. Universal frontend
and source/runtime correspondence remain separate requirements.
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
    parser.add_argument("--cetta", type=Path, required=True)
    parser.add_argument("--petta-runner", type=Path, required=True)
    parser.add_argument("--maude", type=Path, required=True)
    parser.add_argument("--source-work", type=Path)
    parser.add_argument("--timeout", type=int, default=180)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[3]
    lean, gslt = repo / "lean/mettapedia", repo / "metta/gslt"
    work = args.output.resolve()
    work.mkdir(parents=True, exist_ok=False)
    source = gslt / "module/gold/Maude/examples/core_conditional.maude"
    generator = gslt / "tools/generate_maude_max_controls.lean"
    common = gslt / "tools/test_gslt_complete.sh"
    match = re.search(r"^libraries=\((.*?)^\)", common.read_text(), re.S | re.M)
    if match is None:
        raise RuntimeError("shared runtime library list is missing")
    libraries = [gslt / "lib" / (name + ".metta") for name in match[1].split()]
    cetta, petta, maude = args.cetta.resolve(), args.petta_runner.resolve(), args.maude.resolve()
    inputs = [Path(__file__), generator, common, source, cetta, petta, maude,
              maude.parent / "prelude.maude", *libraries]
    inputs += sorted((petta.parent / "src").rglob("*.pl"))
    for directory, names in [
        ("Mettapedia/Languages/Maude", ["Syntax", "Semantics", "Examples", "ConditionalMax",
            "ConditionalMaxBounds", "ConditionalMaxValue", "ConditionalMaxNormalization",
            "HookedEquivalence", "EquationalInterpretation", "TheoryEmbedding", "ConditionalMaxBoolPrelude",
            "ConditionalMaxBoolModel", "ConditionalMaxBoolAlgebra", "ConditionalMaxBoolHooks",
            "ConditionalMaxBoolConservativity", "ConditionalMaxBoolControls"]),
        ("Mettapedia/GSLT/LanguageDef/ModuleFormat", ["MaudeCompilation", "MaudeConditionalCompilation",
            "MaudeConditionalImport", "MaudeConditionalSourceGuard", "MaudeSourceLowering"]),
    ]:
        for name in names:
            relative = Path(directory) / (name + ".lean")
            inputs += [lean / relative, lean / ".lake/build/lib/lean" / relative.with_suffix(".olean")]
    source_arguments = []
    if args.source_work is not None:
        source_work = args.source_work.resolve()
        source_record_path = source_work / "qualification.json"
        source_record = json.loads(source_record_path.read_text())
        if not source_record["passed"] or any(sha(path) != digest for path, digest in source_record["input_pins"].items()):
            raise RuntimeError("source grammar/elaboration qualification is missing, failed or stale")
        packet = source_work / "core_conditional.packet"
        reader = source_work / "native/source-reader"
        reader_inputs = [source_work / "grammar" / name for name in ["reader.abi", "reader-start.term", "selection.term"]]
        inputs += [packet, source_record_path, reader, *reader_inputs]
        inputs += [Path(path) for path in source_record["input_pins"]]
        source_arguments = [str(source), str(packet)]
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
        str(generator), str(generated), *source_arguments])
    if result.returncode:
        raise RuntimeError("generation failed: " + (output + error)[-1500:])
    refusals = []
    if args.source_work is not None:
        original = source.read_text()
        mutations = {
            "false-base-comparison": original.replace("eq 0 <= N = true .", "eq 0 <= N = false .", 1),
            "reversed-left-guard": original.replace("N if M <= N = true .", "N if N <= M = true .", 1),
            "wrong-conditional-result": original.replace("max(N, M) = N if", "max(N, M) = M if", 1),
            "including-import": original.replace("protecting BOOL", "including BOOL", 1),
            "extending-import": original.replace("protecting BOOL", "extending BOOL", 1),
            "system-module": original.replace("fmod GOLD-MAX", "mod GOLD-MAX", 1).replace("endfm", "endm", 1),
            "open-command": original.replace("red max(s(s(0)), s(0)) .", "red max(N, s(0)) .", 1),
            "rewrite-command": original.replace("red max(s(s(0)), s(0)) .", "rew max(s(s(0)), s(0)) .", 1),
        }
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
            unexpected = work / (label + "-unexpected-emission")
            result, output, error = run(label + "-emit", ["lake", "env", "lean", "-DwarningAsError=true", "--run",
                str(generator), str(unexpected), str(candidate), str(changed_packet)])
            expected_reason = "the conditional source profile expects a ground Nat reduction" if label in {
                "open-command", "rewrite-command"} else "source differs from the certified conditional BOOL import profile"
            passed = result.returncode != 0 and expected_reason in output + error and not unexpected.exists()
            refusals.append({"label": label, "passed": passed, "exit": result.returncode})
            (work / "refusals.json").write_text(json.dumps(refusals, indent=2) + "\n")
            pins[str(candidate)], pins[str(changed_packet)] = sha(candidate), sha(changed_packet)
            if not passed:
                raise RuntimeError(label + ": changed source was not refused")
    cases = json.loads((generated / "reference-cases.json").read_text())
    scope = json.loads((generated / "scope.json").read_text())
    if scope["originalBOOLImportAdmitted"] != (args.source_work is not None):
        raise RuntimeError("the generated import profile differs from the requested route")
    module_text = "\n".join(line for line in source.read_text().splitlines()
        if not re.match(r"\s*(red|reduce|rew|rewrite|search)\b", line))
    references = []
    for case in cases:
        query = module_text + f'\nred in GOLD-MAX : {case["term"]} .\nquit\n'
        result, output, error = run("maude-" + case["label"], [str(maude), "-no-banner", "-no-advise"],
            input_text=query, env=dict(os.environ, MAUDE_LIB=str(maude.parent)))
        values = re.findall(r"^result Nat:\s*(.+)$", output, re.M)
        expected = "s(" * case["expected"] + "0" + ")" * case["expected"]
        passed = result.returncode == 0 and not error and len(values) == 1 and re.sub(r"\s+", "", values[0]) == expected
        references.append({"label": case["label"], "passed": passed, "expected": case["expected"], "values": values})
        (work / "references.json").write_text(json.dumps(references, indent=2) + "\n")
        if not passed:
            raise RuntimeError(case["label"] + ": Maude reference differs")
    workload = work / "workload.metta"
    workload.write_text("\n".join(path.read_text() for path in [*libraries,
        generated / "machine.metta", generated / "controls.metta"]))
    for path in [workload, *generated.iterdir()]:
        pins[str(path)] = sha(path)
    expected_rows = [f'(MaudeMaxNativeControl "{case["label"]}" true true true true)' for case in cases]
    results = []
    for engine, command in [
        ("cetta", [str(cetta), "--lang", "petta", "--quiet", str(workload)]),
        ("petta", ["bash", str(petta), "--silent", str(workload)]),
    ]:
        started = time.monotonic()
        result, output, error = run(engine, command, env=dict(os.environ, CETTA_PETTA_SEARCH_MACHINE="1"))
        rows = [line for line in output.splitlines() if line.startswith("(MaudeMaxNativeControl ")]
        envelope_rows = [line for line in output.splitlines() if line.startswith("(MaudeMaxEnvelopeControl ")]
        passed = result.returncode == 0 and not error and rows == expected_rows and envelope_rows == ["(MaudeMaxEnvelopeControl true true)"]
        results.append({"engine": engine, "exit": result.returncode, "passed": passed,
            "checks": 4 * len(rows) + 2 * len(envelope_rows), "seconds": time.monotonic() - started,
            "rows": rows, "envelope_rows": envelope_rows})
        (work / "results.json").write_text(json.dumps(results, indent=2) + "\n")
        print(json.dumps(results[-1]), flush=True)
        if not passed:
            raise RuntimeError(engine + ": native conditional max controls failed")
    unchanged = all(sha(path) == digest for path, digest in pins.items())
    record = {"passed": unchanged, "inputs_current": unchanged, "input_pins": pins,
        "controls": len(cases), "checks_per_engine": 4 * len(cases) + 2, "references": references,
        "refusals": refusals, "originalBOOLImportAdmitted": scope["originalBOOLImportAdmitted"],
        "scope": scope["scope"], "universalSourceRuntimeCorrespondence": False, "fullM0Qualified": False}
    (work / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")
    if not unchanged:
        raise RuntimeError("an input changed during qualification")


if __name__ == "__main__":
    main()
