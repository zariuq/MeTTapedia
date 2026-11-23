#!/usr/bin/env python3
"""Run independently elaborated Peano source through the shared realizer.

The full IR must match the existing certified Peano schema. Missing, extra,
altered equations and altered algebra attributes must refuse that realizer.
This finite gate does not prove the general frontend or link checker.
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
    parser.add_argument("--source-work", type=Path, required=True)
    parser.add_argument("--cetta", type=Path, required=True)
    parser.add_argument("--petta-runner", type=Path, required=True)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[3]
    lean, gslt = repo / "lean/mettapedia", repo / "metta/gslt"
    work = args.output.resolve()
    work.mkdir(parents=True, exist_ok=False)
    source_work = args.source_work.resolve()
    source_record = json.loads((source_work / "qualification.json").read_text())
    if not source_record["passed"] or any(sha(path) != digest for path, digest in source_record["input_pins"].items()):
        raise RuntimeError("source/elaboration qualification is missing, failed or stale")
    source = gslt / "module/gold/Maude/examples/core_peano.maude"
    packet = source_work / "core_peano.packet"
    generator = gslt / "tools/emit_maude_peano_source.lean"
    common = gslt / "tools/test_gslt_complete.sh"
    matched = re.search(r"^libraries=\((.*?)^\)", common.read_text(), re.S | re.M)
    if matched is None:
        raise RuntimeError("shared library list missing")
    libraries = [gslt / "lib" / (name + ".metta") for name in matched[1].split()]
    cetta, petta = args.cetta.resolve(), args.petta_runner.resolve()
    inputs = [Path(__file__), generator, common, *libraries, cetta, petta, source, packet,
              source_work / "qualification.json"]
    inputs += sorted((petta.parent / "src").rglob("*.pl"))
    for name in ["MaudeSourceLowering", "MaudeSourceResolution", "MaudePeanoEmissionAgreement", "MaudeLinkedPeanoEmission"]:
        relative = Path("Mettapedia/GSLT/LanguageDef/ModuleFormat") / (name + ".lean")
        inputs += [lean / relative, lean / ".lake/build/lib/lean" / relative.with_suffix(".olean")]
    pins = {str(path): sha(path) for path in inputs}

    def emit(label, source, packet, directory):
        with (work / (label + ".out")).open("w") as out, (work / (label + ".err")).open("w") as err:
            return subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", "--run", generator,
                source, packet, directory, "GOLD-PEANO"], cwd=lean, stdout=out, stderr=err)

    original = source.read_text()
    mutations = {
        "altered_rhs": original.replace("eq 0 + M = M .", "eq 0 + M = 0 ."),
        "missing_equation": original.replace("  eq 0 * M = 0 .\n", ""),
        "extra_equation": original.replace("endfm", "  eq s(0) = 0 .\nendfm"),
        "altered_attributes": original.replace("ops _+_ _*_ : Nat Nat -> Nat .", "ops _+_ _*_ : Nat Nat -> Nat [comm] ."),
    }
    refusals = []
    for label, changed in mutations.items():
        if changed == original:
            raise RuntimeError("mutation did not change its source")
        candidate = work / (label + ".maude")
        candidate.write_text(changed)
        forest = work / (label + ".forest")
        parsed = subprocess.run([source_work / "native/source-reader", source_work / "grammar/reader.abi",
            source_work / "grammar/reader-start.term", candidate, forest, "--select",
            source_work / "grammar/selection.term", "256"], capture_output=True, text=True)
        (work / (label + "-parse.out")).write_text(parsed.stdout)
        (work / (label + "-parse.err")).write_text(parsed.stderr)
        lines = parsed.stdout.splitlines()
        if parsed.returncode or not lines:
            raise RuntimeError("mutation did not parse")
        metadata = json.loads(lines[0])
        if metadata["outcome"] != 0 or not metadata["semanticResults"]:
            raise RuntimeError("mutation replay remains incomplete")
        candidate_packet = work / (label + ".packet")
        candidate_packet.write_text("\n".join(lines[1:]) + "\n")
        rejected_output = work / (label + "-unexpected-emission")
        result = emit(label, candidate, candidate_packet, rejected_output)
        reason = (work / (label + ".err")).read_text()
        passed = result.returncode != 0 and "does not match the certified Peano theory" in reason and not rejected_output.exists()
        refusals.append({"name": label, "passed": passed, "exit": result.returncode})
        (work / "refusals.json").write_text(json.dumps(refusals, indent=2) + "\n")
        if not passed:
            raise RuntimeError(label + ": realizer link refusal failed")
    directory = work / "peano"
    result = emit("generate", source, packet, directory)
    if result.returncode:
        raise RuntimeError("source emission failed")
    workload = directory / "workload.metta"
    workload.write_text("\n".join(path.read_text() for path in [*libraries,
        directory / "machine.metta", directory / "controls.metta"]))
    for path in [workload, directory / "machine.metta", directory / "controls.metta", directory / "scope.json"]:
        pins[str(path)] = sha(path)
    (work / "input-pins.json").write_text(json.dumps(pins, indent=2) + "\n")
    results = []
    for engine, command in [("cetta", [str(cetta), "--lang", "petta", "--quiet", str(workload)]),
                            ("petta", ["bash", str(petta), "--silent", str(workload)])]:
        started = time.monotonic()
        with (directory / (engine + ".out")).open("w") as out, (directory / (engine + ".err")).open("w") as err:
            result = subprocess.run(command, cwd=lean, stdout=out, stderr=err,
                                    env=dict(os.environ, CETTA_PETTA_SEARCH_MACHINE="1"))
        rows = [row for row in (directory / (engine + ".out")).read_text().splitlines()
                if row.startswith("(MaudeSourceNativeControl ")]
        passed = result.returncode == 0 and not (directory / (engine + ".err")).read_bytes() and rows == [
            "(MaudeSourceNativeControl true true true)"]
        results.append({"engine": engine, "exit": result.returncode, "passed": passed,
                        "seconds": time.monotonic() - started, "controls": rows})
        (work / "results.json").write_text(json.dumps(results, indent=2) + "\n")
        print(json.dumps(results[-1]), flush=True)
        if not passed:
            raise RuntimeError("emitted source runtime control failed")
    changed = [path for path, digest in pins.items() if sha(path) != digest]
    record = {"passed": not changed, "results": results, "link_refusals": refusals,
              "input_pins": pins, "changed_inputs": changed,
              "scope": "Actual Peano source through independently elaborated IR and the existing shared realizer",
              "fresh_backend_build": False, "universal_frontend_correspondence": False,
              "structural_link_reflection_proved": True, "linked_ir_backend_agreement_proved": True,
              "full_M0_qualified": False}
    (work / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")
    if changed:
        raise RuntimeError("runtime qualification inputs changed")


if __name__ == "__main__":
    main()
