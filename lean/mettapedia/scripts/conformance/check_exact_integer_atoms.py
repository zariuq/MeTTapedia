#!/usr/bin/env python3
"""Qualify production CeTTa Atom/GMP arithmetic and retained-value lifetimes.

The probe includes the actual grounded.c helper and links the actual Atom
implementation. It does not implement a replacement adapter. Python integer
arithmetic supplies independent expectations. GMP and the C toolchain remain
trusted; this gate is not a proof of C or a resource-availability guarantee.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import random
import shlex
import shutil
import subprocess
import time
import uuid


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command: list[str], cwd: Path, *, data: str | None = None,
        environment: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(command, cwd=cwd, input=data, text=True, capture_output=True,
                            env=environment, timeout=240)
    if result.returncode:
        raise RuntimeError(f"command failed ({result.returncode}): {shlex.join(command)}\n"
                           f"{result.stdout}\n{result.stderr}")
    return result


def vectors() -> list[tuple[str, int, int]]:
    limits = [0, 1, -1, -(2**63), 2**63 - 1, 2**63, -(2**63) - 1,
              2**64, -(2**64), 2**128 + 7, -(2**128) + 7]
    rows = [(op, a, b) for op in ("+", "-", "*") for a in limits for b in limits]
    rng = random.Random(20261020)
    for bits in (65, 128, 257, 1024, 2048):
        for _ in range(24):
            a = rng.getrandbits(bits) * rng.choice((-1, 1))
            b = rng.getrandbits(bits) * rng.choice((-1, 1))
            rows.extend((op, a, b) for op in ("+", "-", "*"))
            rows.append(("+", a, -a + rng.randrange(-128, 128)))
    return rows


def expected(rows: list[tuple[str, int, int]]) -> str:
    lines = ["lifecycle\tpassed"]
    for op, a, b in rows:
        result = a + b if op == "+" else a - b if op == "-" else a * b
        tag = "word" if -(2**63) <= result < 2**63 else "storage"
        lines.append(f"{result}\t{tag}")
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cetta-tree", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--compiler", default=os.environ.get("CC", "clang"))
    parser.add_argument("--sanitize", action="store_true")
    args = parser.parse_args()
    root = args.cetta_tree.resolve()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    record = {"run_id": uuid.uuid4().hex, "started_at": datetime.now(timezone.utc).isoformat(),
              "status": "running", "qualified": False}
    report = out / "qualification.json"

    def save() -> None:
        report.write_text(json.dumps(record, indent=2) + "\n")

    save()
    try:
        here = Path(__file__).resolve().parent
        probe = here / "exact_integer_atom_probe.c"
        sources = [probe] + [root / "src" / path for path in (
            "atom.c", "symbol.c", "scalar_trie.c", "binding/frame_identity.c",
            "name_key.c", "atom_blob.c", "term_canon.c", "space.c")]
        compiler = shlex.split(args.compiler)
        executable = shutil.which(compiler[0])
        if executable is None:
            raise RuntimeError("C compiler is unavailable: " + compiler[0])
        compiler[0] = str(Path(executable).resolve())
        common = ["-std=gnu11", "-Wall", "-Wextra", "-Werror", "-DCETTA_BUILD_WITH_GMP=1",
                  "-DCETTA_RUNTIME_STATS_NOOP=1", "-ffunction-sections", "-fdata-sections",
                  "-I" + str(root), "-I" + str(root / "src")]

        def dependencies() -> set[Path]:
            found = {Path(__file__).resolve(), Path(compiler[0])}
            for source in sources:
                result = run(compiler + common + ["-MM", "-MT", "probe", str(source)], out)
                if result.stderr:
                    raise RuntimeError(result.stderr)
                dependency_text = result.stdout.replace("\\\n", " ").split(":", 1)[1]
                found.update(Path(path).resolve() for path in shlex.split(dependency_text))
            return found

        inputs = dependencies()
        before = {str(path): digest(path) for path in sorted(inputs)}
        record["inputs"] = before
        save()
        rows = vectors()
        data = "".join(f"{op}\t{a}\t{b}\n" for op, a, b in rows)
        golden = expected(rows)
        (out / "requests.tsv").write_text(data)
        (out / "expected.tsv").write_text(golden)
        # The output contract must reject lost results, extra results, altered
        # mathematical values, altered representation tags and missing checks.
        mutations = [golden.replace("0\tword", "1\tword", 1),
                     golden.replace("0\tword", "0\tstorage", 1),
                     golden.split("\n", 1)[1], golden + "0\tword\n",
                     "\n".join(golden.splitlines()[:-1]) + "\n"]
        assert all(changed != golden for changed in mutations)
        modes = [("optimized", ["-O2"])]
        if args.sanitize:
            modes.append(("sanitized", ["-O1", "-g", "-fsanitize=address,undefined",
                                         "-fno-sanitize-recover=all", "-fno-omit-frame-pointer"]))
        executions = []
        for name, flags in modes:
            binary = out / ("atom-probe-" + name)
            command = compiler + common + flags + list(map(str, sources)) + [
                "-Wl,--gc-sections", "-pthread", "-lgmp", "-lm", "-o", str(binary)]
            started = time.monotonic()
            environment = dict(os.environ, TMPDIR=str(out))
            result = run(command, out, environment=environment)
            (out / (name + ".build.log")).write_text(result.stdout + result.stderr)
            if result.stderr:
                raise RuntimeError("unexpected compiler diagnostics: " + result.stderr)
            if name == "sanitized":
                environment.update(ASAN_OPTIONS="detect_leaks=1:halt_on_error=1",
                                   UBSAN_OPTIONS="halt_on_error=1:print_stacktrace=1")
            executed = run([str(binary)], out, data=data, environment=environment)
            (out / (name + ".actual.tsv")).write_text(executed.stdout)
            (out / (name + ".stderr")).write_text(executed.stderr)
            if executed.stderr or executed.stdout != golden:
                raise RuntimeError("incorrect result, tag, lifecycle or sanitizer output: " + name)
            executions.append({"mode": name, "arithmetic_cases": len(rows), "lifecycle": "passed",
                               "binary_sha256": digest(binary), "command": command,
                               "build_and_run_seconds": round(time.monotonic() - started, 6)})
            record["executions"] = executions
            save()
        after_inputs = dependencies()
        after = {str(path): digest(path) for path in sorted(after_inputs)}
        if before != after:
            record["changed_inputs"] = sorted(key for key in before.keys() | after.keys()
                                               if before.get(key) != after.get(key))
            raise RuntimeError("production inputs changed during qualification")
        record.update(status="passed", qualified=True, rejected_output_mutations=len(mutations),
                      compiler=run(compiler + ["--version"], out).stdout.splitlines()[0],
                      gmp_version=run(["pkg-config", "--modversion", "gmp"], out).stdout.strip(),
                      boundary="Actual Atom/grounded helper; separate probe configuration, not an entire "
                      "CeTTa build. GMP/toolchain trusted. No recoverable allocation failure, array "
                      "append, arbitrary dialect payload or infinite-run guarantee.")
        print(f"Atom/GMP: {len(rows)} arithmetic cases and lifecycle checks in {len(executions)} builds")
    except Exception as error:
        record.update(status="failed", error=str(error))
        raise
    finally:
        record["finished_at"] = datetime.now(timezone.utc).isoformat()
        save()


if __name__ == "__main__":
    main()
