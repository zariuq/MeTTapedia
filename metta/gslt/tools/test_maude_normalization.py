#!/usr/bin/env python3
"""Compare the oriented Peano-equation GSLT on both MeTTa engines and Maude.

This component gate builds the Peano source/emission proofs and compares
their emitted examples. Full M0 admission and ordinary source lowering
remain separate obligations.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--maude", type=Path, required=True)
    parser.add_argument("--cetta", type=Path)
    parser.add_argument("--petta-runner", type=Path)
    parser.add_argument("--program", action="append", choices=["zero", "add23", "mul23", "open", "open-stuck"])
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[3]
    gslt, lean = repo / "metta/gslt", repo / "lean/mettapedia"
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    programs = args.program or ["zero", "add23", "mul23", "open", "open-stuck"]
    targets = ["Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeNormalizationOSLFControls",
               "Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeNormalizationFiringControls",
               "Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudePeanoStageReflectionControls",
               "Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudePeanoEmissionAgreement",
               "Mettapedia.Languages.Maude.PeanoArithmetic",
               "Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission"]
    with (output / "build.log").open("w") as log:
        subprocess.run(["lake", "--wfail", "build", *targets], cwd=lean, stdout=log,
                       stderr=subprocess.STDOUT, check=True)
    cetta = (args.cetta or repo.parent / "hyperon/cetta-prime-2.0-draft-20260910/cetta").resolve()
    petta = (args.petta_runner or repo.parent / "hyperon/PeTTa/run.sh").resolve()
    maude = args.maude.resolve(strict=True)
    prelude = maude.parent / "prelude.maude"
    generator = gslt / "tools/generate_maude_normalization_controls.lean"
    source = gslt / "module/gold/Maude/examples/core_peano.maude"
    common = gslt / "tools/test_gslt_complete.sh"
    match = re.search(r"^libraries=\((.*?)^\)", common.read_text(), re.S | re.M)
    if match is None:
        raise RuntimeError("the shared runtime library list is missing")
    libraries = [gslt / "lib" / (name + ".metta") for name in match[1].split()]
    inputs = {Path(__file__).resolve(), generator, source, common, *libraries, cetta, petta, maude, prelude,
              lean / "lean-toolchain", lean / "lakefile.lean", lean / "lake-manifest.json"}
    inputs.update((petta.parent / "src").rglob("*.pl"))
    for target in targets:
        relative = Path(*target.split("."))
        setup = lean / ".lake/build/ir" / relative.with_suffix(".setup.json")
        inputs.update([setup, lean / relative.with_suffix(".lean"),
                       lean / ".lake/build/lib/lean" / relative.with_suffix(".olean")])
        for dependency, groups in json.loads(setup.read_text())["importArts"].items():
            if dependency.startswith("Mettapedia."):
                inputs.add(lean / Path(*dependency.split(".")).with_suffix(".lean"))
            inputs.update(Path(path) for group in groups for path in group)
    pins = {str(path): sha(path) for path in inputs}

    def save_pins():
        (output / "input-pins.json").write_text(json.dumps(pins, indent=2) + "\n")

    save_pins()
    version = subprocess.run([str(maude), "--version"], capture_output=True, text=True, check=True)
    if version.stdout.strip() != "3.5.1" or version.stderr:
        raise RuntimeError("expected the pinned Maude 3.5.1 reference")
    observations = {"zero": ("0", 0), "add23": ("s(s(0)) + s(s(s(0)))", 5),
                    "mul23": ("s(s(0)) * s(s(s(0)))", 6), "open": ("0 + N", "N"),
                    "open-stuck": ("N + 0", "N + 0")}
    results = []
    for label in programs:
        directory = output / label
        with (output / ("generate-" + label + ".log")).open("w") as log:
            subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", "--run", generator,
                            directory, label], cwd=lean, stdout=log, stderr=subprocess.STDOUT, check=True)
        scope = json.loads((directory / "scope.json").read_text())
        wanted = observations[label][1]
        observed = (scope["expectedVariableN"] is True if label == "open" else scope["expectedUnchanged"] is True
                    if label == "open-stuck" else type(scope["expectedNatural"]) is int and scope["expectedNatural"] == wanted)
        if not observed or (isinstance(wanted, str) and scope["expectedNatural"] is not None):
            raise RuntimeError(label + ": reducer readout disagrees with the independent reference expectation")
        reached = scope["oslfReachesExpected"]
        wrong_step = scope["oslfWrongOneStep"]
        if reached is not True:
            raise RuntimeError(label + ": OSLF did not establish reachability of the observed normalization result")
        if wrong_step is not False:
            raise RuntimeError(label + ": OSLF did not reject the separating one-step result")
        workload = directory / "workload.metta"
        workload.write_text("\n".join(path.read_text()
            for path in [*libraries, directory / "machine.metta", directory / "controls.metta"]))
        for path in [workload, directory / "machine.metta", directory / "controls.metta", directory / "scope.json"]:
            pins[str(path)] = sha(path)
        save_pins()
        engines = []
        for name, command in [("cetta", [str(cetta), "--lang", "petta", "--quiet", str(workload)]),
                              ("petta", ["bash", str(petta), "--silent", str(workload)])]:
            started = time.monotonic()
            with (directory / (name + ".out")).open("w") as out, (directory / (name + ".err")).open("w") as err:
                result = subprocess.run(command, cwd=lean, env=dict(os.environ, CETTA_PETTA_SEARCH_MACHINE="1"),
                                        stdout=out, stderr=err)
            rows = [line for line in (directory / (name + ".out")).read_text().splitlines()
                    if line.startswith("(MaudeNormalizationControl ")]
            parsed = [re.fullmatch(r'\(MaudeNormalizationControl "([^"]+)"' + r" (true|false)" * 3
                                  + r" ([0-9]+) ([0-9]+)\)", row) for row in rows]
            passed = (result.returncode == 0 and not (directory / (name + ".err")).read_bytes()
                      and len(parsed) == 1 and parsed[0] is not None and parsed[0].group(1) == label
                      and parsed[0].groups()[1:4] == ("true",) * 3)
            engines.append({"engine": name, "passed": passed, "exit_code": result.returncode,
                            "seconds": time.monotonic() - started, "controls": rows,
                            "stdout_sha256": sha(directory / (name + ".out"))})
            (directory / "engine-results.json").write_text(json.dumps(engines, indent=2) + "\n")
        term, value = observations[label]
        commands = source.read_text() + "\nset show timing off .\nred in GOLD-PEANO : " + term + " .\nquit\n"
        (directory / "reference.commands").write_text(commands)
        native = subprocess.run([str(maude), "-no-banner", "-no-advise", "-no-wrap"], input=commands,
                                cwd=maude.parent, env=dict(os.environ, MAUDE_LIB=str(maude.parent)),
                                capture_output=True, text=True)
        (directory / "maude.out").write_text(native.stdout)
        (directory / "maude.err").write_text(native.stderr)
        values = re.findall(r"^result Nat: (.+)$", native.stdout, re.M)
        expected = value if isinstance(value, str) else "s(" * value + "0" + ")" * value
        reference = native.returncode == 0 and not native.stderr and len(values) == 2 and values[-1] == expected
        same = engines[0]["controls"] == engines[1]["controls"]
        results.append({"program": label, "engines": engines, "outputs_identical": same,
                        "expected_readout": scope,
                        "oslf_reaches_expected": reached, "oslf_wrong_one_step": wrong_step,
                        "oslf_reachability_pending": reached is None,
                        "maude_reference_passed": reference, "maude_value": values[-1] if values else None,
                        "passed": reference and same and all(row["passed"] for row in engines)})
        (output / "program-results.json").write_text(json.dumps(results, indent=2) + "\n")
        print(json.dumps(results[-1]), flush=True)
        if not results[-1]["passed"]:
            raise RuntimeError(label + ": normalization-stage comparison did not pass")
    changed = [path for path, expected in pins.items() if sha(path) != expected]
    record = {"programs": results, "input_pins": pins, "changed_inputs": changed,
              "checks_per_engine": 3 * len(results), "passed": not changed and all(row["passed"] for row in results),
              "oslf_decided_checks": sum(1 + (row["oslf_reaches_expected"] is not None) for row in results),
              "oslf_pending_reachability": [row["program"] for row in results if row["oslf_reachability_pending"]],
              "scope": "oriented Peano equations through the shared runner, values and exact resumption",
              "normalization_certificates_complete": False, "full_maude_qualified": False,
              "source_lowering_qualified": False, "original_common_gate_requalified": False}
    (output / "component-gate.json").write_text(json.dumps(record, indent=2) + "\n")
    if not record["passed"]:
        raise RuntimeError("normalization-stage gate inputs changed")


if __name__ == "__main__":
    main()
