#!/usr/bin/env python3
"""Qualify pending and waiting mailbox callback branches on both engines.

Source waiting worlds retain queued network messages. Other carriers test
raw argument transport and malformed-response refusal. Complete generated
kernel linkage and actor scheduling are separate obligations.
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
    parser.add_argument("--cetta", type=Path, required=True)
    parser.add_argument("--petta-runner", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=120)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[3]
    lean, gslt = repo / "lean/mettapedia", repo / "metta/gslt"
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    common = gslt / "tools/test_gslt_complete.sh"
    match = re.search(r"^libraries=\((.*?)^\)", common.read_text(), re.M | re.S)
    if match is None:
        raise RuntimeError("shared library list is missing")
    libraries = [gslt / "lib" / (name + ".metta") for name in match[1].split()]
    libraries += [gslt / "lib" / name for name in ["gslt_integer.metta", "gslt_word16.metta",
        "gslt_snapshot_closure.metta", "gslt_provider_cache.metta", "gslt_erlang.metta",
        "gslt_erlang_rho.metta", "gslt_erlang_actors.metta", "gslt_erlang_actors_portable.metta"]]
    generator = gslt / "tools/generate_erlang_mailbox_callback_controls.lean"
    cetta, petta = args.cetta.resolve(), args.petta_runner.resolve()
    inputs = [Path(__file__), generator, common, cetta, petta, *libraries]
    inputs += sorted((petta.parent / "src").rglob("*.pl"))
    for relative in [
        "Languages/Erlang/Actors", "Languages/Erlang/ActorIdentity",
        "Languages/Erlang/ActorIdentityPreservation", "Languages/Erlang/ActorProcessStore",
        "Languages/Erlang/ActorMailboxReplies",
        "GSLT/LanguageDef/ModuleFormat/ErlangActorProcessWire",
        "GSLT/LanguageDef/ModuleFormat/ErlangActorWorldWire",
        "GSLT/LanguageDef/ConstructorCertificates",
        "GSLT/LanguageDef/ModuleFormat/ErlangValueTyping",
        "GSLT/LanguageDef/ModuleFormat/ErlangValueShape",
        "GSLT/LanguageDef/ModuleFormat/ErlangMailboxValueAdmission",
        "Languages/MeTTa/PeTTa/Bridges/MeTTaIL/ErlangControllerSource",
        "Languages/MeTTa/PeTTa/Bridges/MeTTaIL/ErlangActorStoreCall",
        "Languages/MeTTa/PeTTa/Bridges/MeTTaIL/ErlangActorProcessStoreExecution",
        "Languages/MeTTa/PeTTa/Bridges/MeTTaIL/ErlangActorProcessStoreCorrespondence",
        "Languages/MeTTa/PeTTa/Bridges/MeTTaIL/ErlangActorWorldStoreExecution",
        "Languages/MeTTa/PeTTa/Bridges/MeTTaIL/ErlangActorMailboxCall",
        "Languages/MeTTa/PeTTa/Bridges/MeTTaIL/ErlangActorMailboxExecution",
    ]:
        path = Path("Mettapedia") / (relative + ".lean")
        inputs += [lean / path, lean / ".lake/build/lib/lean" / path.with_suffix(".olean")]
    pins = {str(path): sha(path) for path in inputs}

    def run(label, command, env=None):
        with (output / (label + ".out")).open("w") as out, (output / (label + ".err")).open("w") as err:
            result = subprocess.run(command, cwd=lean, stdout=out, stderr=err,
                env=env, timeout=args.timeout, check=False)
        return result.returncode, (output / (label + ".out")).read_text(), (output / (label + ".err")).read_text()

    generated = output / "generated"
    code, text, error = run("generate", ["lake", "env", "lean", "-DwarningAsError=true", "--run", str(generator), str(generated)])
    if code:
        raise RuntimeError("source-model controls failed to generate: " + (text + error)[-1500:])
    cases = json.loads((generated / "cases.json").read_text())
    controls = generated / "controls.metta"
    workload = output / "run.metta"
    workload.write_text("\n".join(path.read_text() for path in [*libraries, controls]))
    for path in [workload, *generated.iterdir()]:
        pins[str(path)] = sha(path)
    expected = [f'(ErActorMailboxControl "{label}" true true true)' for label in cases["labels"]]
    results = []
    for engine, command in [("cetta", [str(cetta), "--lang", "petta", "--quiet", str(workload)]),
                            ("petta", ["bash", str(petta), "--silent", str(workload)])]:
        started = time.monotonic()
        code, text, error = run(engine, command, dict(os.environ, CETTA_PETTA_SEARCH_MACHINE="1"))
        normalized = text.replace("True", "true").replace("False", "false")
        rows = [line.strip() for line in normalized.splitlines() if line.startswith("(ErActorMailboxControl ")]
        passed = code == 0 and rows == expected and "(Error" not in text and not error
        result = {"engine": engine, "exit": code, "passed": passed, "checks": 3 * len(rows),
            "seconds": time.monotonic() - started, "rows": rows, "command": command, "stderr": error}
        results.append(result)
        (output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
        print(json.dumps(result), flush=True)
        if not passed:
            raise RuntimeError(engine + ": mailbox callback controls failed")
    changed = [path for path, digest in pins.items() if sha(path) != digest]
    if changed:
        raise RuntimeError("qualification inputs changed: " + repr(changed))
    record = {"passed": True, "cases": len(expected), "checks_per_engine": 3 * len(expected),
        "identical": results[0]["rows"] == results[1]["rows"], "results": results,
        "input_pins": pins, "scope": cases["scope"], "full_E0_qualified": False}
    (output / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")


if __name__ == "__main__":
    main()
