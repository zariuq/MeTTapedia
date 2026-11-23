#!/usr/bin/env python3
"""Qualify actual CeTTa array lifetimes against independent Lean packets.

Requires a private build manifest from build_cetta_qualification.py with
runtime counters enabled. Sanitizer and ordinary builds are recorded separately.
The workload retains the original
array while extending it, reuses aliases, and carries computed GMP payloads.
Positive collection counters are required in CeTTa's Prime mode. This is a
finite native qualification, not a proof of garbage collection or allocation
failure behavior. Run under the same Lean environment as test_inductive_append.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build-manifest", required=True, type=Path)
    parser.add_argument("--library", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--rounds", type=int, default=1024)
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error("rounds must be positive")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    report = output / "qualification.json"
    record = dict(qualified=False, status="running", rounds=args.rounds,
                  started_at=datetime.now(timezone.utc).isoformat(), records=[])

    def save():
        report.write_text(json.dumps(record, indent=2) + "\n")

    save()
    root = Path(__file__).resolve().parents[1]
    lean_root = root.parents[1] / "lean/mettapedia"
    oracle = root / "tools/qualify_inductive_append.lean"
    library = args.library.resolve()
    manifest = args.build_manifest.resolve()
    inputs = [Path(__file__).resolve(), oracle, manifest, library,
              root / "module/IndexedNatVecAppend.module"]
    try:
        build = json.loads(manifest.read_text())
        if build.get("qualified") is not True or build.get("status") != "passed":
            raise RuntimeError("native build is not qualified")
        config = build["configuration"]
        if config.get("ENABLE_RUNTIME_STATS") != "1":
            raise RuntimeError("requires an actual runtime-statistics build")
        sanitized = "-fsanitize=address,undefined" in config["CFLAGS"]
        if "-fsanitize=" in config["CFLAGS"] and not sanitized:
            raise RuntimeError("unsupported partial sanitizer configuration")
        binary = Path(build["binary"])
        if digest(binary) != build["binary_sha256"]:
            raise RuntimeError("binary differs from its build manifest")
        inputs += [binary]
        # Linked system libraries are trusted implementations but still part
        # of the reproducible runtime input inventory.
        linked = subprocess.run(["ldd", str(binary)], capture_output=True, text=True, check=True)
        if linked.stderr or "not found" in linked.stdout:
            raise RuntimeError("unresolved dynamic runtime libraries")
        (output / "linked-libraries.txt").write_text(linked.stdout)
        for line in linked.stdout.splitlines():
            match = re.search(r"(?:=>\s+)?(/\S+)\s+\(", line)
            if match:
                inputs.append(Path(match.group(1)).resolve())
        before = {str(path): digest(path) for path in inputs}
        record.update(source_pins=before, native_build_sha256=digest(manifest),
                      binary_sha256=digest(binary), native_build_inputs=build["inputs"],
                      sanitizers_enabled=sanitized, native_cflags=config["CFLAGS"],
                      trust_boundary="C toolchain, system libraries and GMP; finite native qualification",
                      client_scope="Captured natural-integer array values; no global bind! or arbitrary executable payloads")
        save()

        def run(label, command, *, env=None, accepted=True):
            start = time.monotonic()
            result = subprocess.run(command, cwd=lean_root, env=env, capture_output=True,
                                    text=True, timeout=180)
            (output / f"{label}.out").write_text(result.stdout)
            (output / f"{label}.err").write_text(result.stderr)
            record["records"].append(dict(label=label, returncode=result.returncode,
                                          seconds=round(time.monotonic() - start, 6)))
            save()
            if (result.returncode == 0) != accepted:
                raise RuntimeError(f"{label}: unexpected return code {result.returncode}")
            return result

        run("generate", ["lean", "--run", str(oracle), "emit-lifetime", str(library),
                         str(args.rounds), str(output)])
        altered = output / "altered-emission.metta"
        altered.write_text(library.read_text() + "\n(= (unlicensed) 1)\n")
        refused = run("changed-emission", ["lean", "--run", str(oracle), "emit-lifetime",
                      str(altered), str(args.rounds), str(output / "refused")], accepted=False)
        if "submitted emission differs from the proved library" not in refused.stdout + refused.stderr:
            raise RuntimeError("changed emission failed for an unrelated reason")
        workload = output / "array-lifetime.metta"
        inputs.append(workload)
        before[str(workload)] = digest(workload)
        packets = {}
        counters = {}
        for mode in ("prime", "petta"):
            for budget in (1, 64):
                label = f"cetta-{mode}-budget-{budget}"
                environment = dict(os.environ, CETTA_GC="1", CETTA_GC_BUDGET_MB=str(budget),
                    ASAN_OPTIONS="detect_leaks=1:halt_on_error=1",
                    UBSAN_OPTIONS="halt_on_error=1:print_stacktrace=1")
                actual = run(label, [str(binary), "--lang", mode, "--quiet", "--emit-runtime-stats",
                                     str(workload)], env=environment)
                counts = {}
                for line in actual.stderr.splitlines():
                    match = re.fullmatch(r"runtime-counter ([a-z0-9-]+) (-?\d+)", line)
                    if not match or match.group(1) in counts:
                        raise RuntimeError(f"{label}: unexpected diagnostic or duplicate counter: {line}")
                    counts[match.group(1)] = int(match.group(2))
                counters[label] = counts
                run(label + "-check", ["lean", "--run", str(oracle), "check-lifetime",
                    str(args.rounds), str(output / f"{label}.out")])
                packets[label] = [line for line in actual.stdout.splitlines()
                                  if line.startswith("(ArrayLifetimePacket ")]
        observed = packets["cetta-prime-budget-1"]
        if any(value != observed for value in packets.values()):
            raise RuntimeError("exact lifetime packets differ across modes or collection budgets")
        gc = counters["cetta-prime-budget-1"]
        if gc.get("eval-tail-safe-point-count", 0) <= 0 or gc.get("eval-tail-reclaimed-bytes", 0) <= 0:
            raise RuntimeError("workload did not demonstrate actual Prime collection and reclamation")

        mutations = {
            "missing-packet": observed[1:],
            "duplicate-packet": observed + observed[:1],
            "lost-original-occurrence": [line.replace("ArrayState (3 1 1 2)", "ArrayState (3 1 2)") for line in observed],
            "reordered-original": [line.replace("ArrayState (3 1 1 2)", "ArrayState (1 3 1 2)") for line in observed],
            "changed-large-payload": [line.replace("340282366920938463463374607431768211461", "5") for line in observed],
            "lost-growth-entry": [line.replace(" 0 0 ", " 0 ", 1) for line in observed],
            "extra-growth-entry": [line.replace(" 0 0 ", " 0 0 0 ", 1) for line in observed],
            "alias-deduplicated": [line.replace("(7 7 7 7 7 7 7 7)", "(7)") for line in observed],
        }
        for label, changed in mutations.items():
            if changed == observed:
                raise RuntimeError(f"{label}: negative control did not change its packet")
            path = output / f"{label}.input"
            path.write_text("\n".join(changed) + "\n")
            run(label, ["lean", "--run", str(oracle), "check-lifetime", str(args.rounds), str(path)], accepted=False)
        after = {str(path): digest(path) for path in inputs}
        if before != after:
            raise RuntimeError("runtime or oracle inputs changed during qualification")
        record.update(status="passed", qualified=True, counters=counters,
                      packet_count=len(observed), negative_controls=list(mutations), source_pins=before,
                      changed_emission_refused=True,
                      allocation_failure_qualified=False,
                      proof_scope="Existing append/source theorem plus independent finite lifetime packets; no collector proof")
        print(f"{len(observed)} exact packets in {len(packets)} runs; {len(mutations)} corruptions refused; "
              f"Prime collections {gc['eval-tail-safe-point-count']}")
    except Exception as error:
        record.update(status="failed", error=str(error))
        raise
    finally:
        record["finished_at"] = datetime.now(timezone.utc).isoformat()
        save()


if __name__ == "__main__":
    main()
