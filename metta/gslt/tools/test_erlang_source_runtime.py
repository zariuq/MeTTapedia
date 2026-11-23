#!/usr/bin/env python3
"""Check source-derived Erlang actor entries on explicit runtime profiles.

CeTTa runs the native rho boundary and compares the complete world with direct
dispatch. SWI PeTTa runs the portable dispatch profile; it is not assumed to
provide CeTTa's native Rhometta operations. Both retain exact resumption.
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
    parser.add_argument("--runtime-lib", type=Path,
                        help="rho/rhometta/lts library directory matching the CeTTa binary")
    parser.add_argument("--petta-runner", type=Path, required=True)
    parser.add_argument("--program", action="append", choices=["core_blocked", "core_selective", "core_function_message"])
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[3]
    lean, gslt = repo / "lean/mettapedia", repo / "metta/gslt"
    work = args.output.resolve()
    work.mkdir(parents=True, exist_ok=False)
    source = args.source_work.resolve()
    source_record = json.loads((source / "qualification.json").read_text())
    if not source_record["passed"] or any(sha(path) != digest for path, digest in source_record["input_pins"].items()):
        raise RuntimeError("the source/model gate is missing, stale or failed")
    programs = args.program or ["core_blocked", "core_selective", "core_function_message"]
    cetta_source, petta = args.cetta.resolve(), args.petta_runner.resolve()
    runtime_lib = (args.runtime_lib or cetta_source.parent / "lib").resolve()
    runtime = work / "runtime"
    (runtime / "lib").mkdir(parents=True)
    cetta = runtime / "cetta"
    cetta.write_bytes(cetta_source.read_bytes())
    cetta.chmod(0o755)
    native_libraries = []
    for name in ["rho.metta", "rhometta.metta", "lts.metta"]:
        original = runtime_lib / name
        if not original.is_file():
            raise RuntimeError("the rho comparison requires a matching runtime library directory: " + str(original))
        frozen = runtime / "lib" / name
        frozen.write_bytes(original.read_bytes())
        native_libraries += [original, frozen]
    generator = gslt / "tools/generate_erlang_source_controls.lean"
    mailbox_generator = gslt / "tools/generate_erlang_rho_mailbox_controls.lean"
    common = gslt / "tools/test_gslt_complete.sh"
    match = re.search(r"^libraries=\((.*?)^\)", common.read_text(), re.S | re.M)
    if match is None:
        raise RuntimeError("shared library list is missing")
    libraries = [gslt / "lib" / (name + ".metta") for name in match[1].split()]
    libraries += [gslt / "lib" / name for name in ["gslt_integer.metta", "gslt_word16.metta",
                  "gslt_snapshot_closure.metta", "gslt_erlang.metta"]]
    actor = gslt / "lib/gslt_erlang_actors.metta"
    portable = gslt / "lib/gslt_erlang_actors_portable.metta"
    rho = gslt / "lib/gslt_erlang_rho.metta"
    inputs = [Path(__file__), generator, mailbox_generator, common, *libraries, actor, portable, rho,
              cetta_source, cetta, petta, source / "qualification.json", *native_libraries]
    inputs += sorted((cetta.parent / "lib").glob("*.metta"))
    inputs += sorted((petta.parent / "src").rglob("*.pl"))
    inputs += [Path(path) for path in source_record["input_pins"]]
    inputs += [gslt / "module" / (name + ".module") for name in
        ["Radix16", "ErlangData", "ErlangSequentialIR", "ErlangSequentialMachine", "ErlangMailbox"]]
    for target in ["Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangExecutionData",
                   "Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangSourceLowering",
                   "Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox",
                   "Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxKernelEmission"]:
        relative = Path(*target.split("."))
        setup = lean / ".lake/build/ir" / relative.with_suffix(".setup.json")
        inputs += [setup, lean / relative.with_suffix(".lean"),
                   lean / ".lake/build/lib/lean" / relative.with_suffix(".olean")]
        for dependency, groups in json.loads(setup.read_text())["importArts"].items():
            if dependency.startswith("Mettapedia."):
                inputs.append(lean / Path(*dependency.split(".")).with_suffix(".lean"))
            inputs += [Path(path) for group in groups for path in group]
    for name in programs:
        inputs += [source / "core" / (name + ".core"), source / (name + ".packet")]
    pins = {str(path): sha(path) for path in set(inputs)}

    def generate(label, script, arguments):
        with (work / (label + ".out")).open("w") as out, (work / (label + ".err")).open("w") as err:
            subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", "--run", str(script),
                            *map(str, arguments)], cwd=lean, stdout=out, stderr=err, check=True)

    generate("mailbox", mailbox_generator, [work / "mailbox"])
    results = []
    for name in programs:
        for engine, profile in [("cetta", "compare"), ("petta", "portable")]:
            directory = work / (name + "-" + engine)
            generate("generate-" + name + "-" + engine, generator,
                     [directory, source / "core" / (name + ".core"), source / (name + ".packet"), name, profile])
            workload = directory / "workload.metta"
            runtime = libraries + [work / "mailbox/machine.metta"]
            if engine == "cetta":
                runtime.append(rho)
            runtime += [actor, portable, directory / "machine.metta", directory / "controls.metta"]
            workload.write_text("\n".join(path.read_text() for path in runtime))
            for path in [workload, directory / "machine.metta", directory / "controls.metta", work / "mailbox/machine.metta"]:
                pins[str(path)] = sha(path)
            (work / "input-pins.json").write_text(json.dumps(pins, indent=2) + "\n")
            command = ([str(cetta), "--lang", "petta", "--quiet", str(workload)] if engine == "cetta" else
                       ["bash", str(petta), "--silent", str(workload)])
            started = time.monotonic()
            with (directory / "stdout.txt").open("w") as out, (directory / "stderr.txt").open("w") as err:
                result = subprocess.run(command, cwd=lean, stdout=out, stderr=err,
                                        env=dict(os.environ, CETTA_PETTA_SEARCH_MACHINE="1"))
            tag = "ErlangSourceNativeControl" if engine == "cetta" else "ErlangSourcePortableControl"
            checks = 5 if engine == "cetta" else 4
            rows = [line for line in (directory / "stdout.txt").read_text().splitlines()
                    if line.startswith("(" + tag + " ")]
            expected = f'({tag} "{name}"' + " true" * checks + ")"
            passed = result.returncode == 0 and not (directory / "stderr.txt").read_bytes() and rows == [expected]
            results.append({"name": name, "engine": engine, "profile": profile, "passed": passed,
                            "exit": result.returncode, "checks": checks, "seconds": time.monotonic() - started,
                            "controls": rows, "stdout_sha256": sha(directory / "stdout.txt")})
            (work / "results.json").write_text(json.dumps(results, indent=2) + "\n")
            print(json.dumps(results[-1]), flush=True)
            if not passed:
                raise RuntimeError(name + ": explicit runtime-profile control failed")
    changed = [path for path, digest in pins.items() if sha(path) != digest]
    record = {"passed": not changed and all(row["passed"] for row in results), "results": results,
              "input_pins": pins, "changed_inputs": changed, "fresh_backend_build": False,
              "scope": "Source entries: CeTTa rho/direct equality and SWI portable actor execution",
              "universal_frontend_or_DCE_correspondence": False, "universal_profile_equivalence": False,
              "complete_schedule_exploration_qualified": False, "full_E0_qualified": False}
    (work / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")
    if not record["passed"]:
        raise RuntimeError("runtime-profile inputs changed")


if __name__ == "__main__":
    main()
