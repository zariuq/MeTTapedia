#!/usr/bin/env python3
"""Run emitted articles through the existing generic MeTTa inference checker.

The consumer is assembled from unchanged authored modules. Expectations come
from the Lean checker exporter. This differential gate establishes these finite
observations, not native implementation refinement or full-corpus coverage.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def bundle(directory):
    seen, active, pins = set(), set(), {}

    def visit(name):
        if name in active:
            raise ValueError("cyclic authored imports")
        if name in seen:
            return ""
        active.add(name)
        path = directory / (name + ".metta")
        text = path.read_text()
        pins[name] = digest(path)
        text = re.sub(r"^!\(import! &self ([A-Za-z0-9_]+)\)[ \t]*$",
                      lambda match: visit(match[1]), text, flags=re.M)
        active.remove(name)
        seen.add(name)
        return text

    return visit("generic_inference_checker_v0"), pins


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--kernel-directory", type=Path, required=True)
    parser.add_argument("--artifacts", type=Path, required=True, action="append")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=float, default=90)
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("timeout must be positive")
    args.output.mkdir(parents=True, exist_ok=True)
    code, pins = bundle(args.kernel_directory)
    binary = args.binary.resolve()
    binary_hash = digest(binary)
    results = []
    for index, directory in enumerate(args.artifacts):
        records = json.loads((directory / "checked.json").read_text())["cases"]
        if not records or len({r["name"] for r in records}) != len(records):
            raise ValueError("missing or duplicate case identities")
        language = (directory / "language.sexp").read_text().strip()
        calls, expected, inputs = [], [], {"language.sexp": digest(directory / "language.sexp"),
                                         "checked.json": digest(directory / "checked.json")}
        for record in records:
            name = record["name"]
            if not re.fullmatch(r"[a-z0-9-]+", name) or type(record["accepted"]) is not bool:
                raise ValueError("invalid case identity or expected verdict")
            goal_path, proof_path = directory / (name + ".goal.sexp"), directory / (name + ".proof.sexp")
            inputs[goal_path.name], inputs[proof_path.name] = digest(goal_path), digest(proof_path)
            goal, proof = goal_path.read_text().strip(), proof_path.read_text().strip()
            calls.append(f"!(gic-check {language} {goal} {proof})")
            expected.append("[True]" if record["accepted"] else "[False]")
        source = args.output / f"presentation-{index}.metta"
        source.write_text(code + "\n" + "\n".join(calls) + "\n")
        expected_text = "\n".join(expected) + "\n"
        (args.output / f"presentation-{index}.expected").write_text(expected_text)
        start = time.monotonic()
        timed_out = False
        try:
            run = subprocess.run([str(binary), "--lang", "he", "--fuel", "-1", "--quiet", str(source)],
                                 capture_output=True, timeout=args.timeout)
            status, stdout, stderr = run.returncode, run.stdout, run.stderr
        except subprocess.TimeoutExpired as error:
            status, stdout, stderr = None, error.stdout or b"", error.stderr or b""
            timed_out = True
        (args.output / f"presentation-{index}.stdout").write_bytes(stdout)
        (args.output / f"presentation-{index}.stderr").write_bytes(stderr)
        unchanged = all(digest(directory / name) == pin for name, pin in inputs.items())
        passed = (not timed_out and status == 0 and stdout == expected_text.encode()
                  and not stderr and unchanged)
        results.append(dict(program=index, cases=records, input_sha256=inputs,
                            source_sha256=digest(source), passed=passed, exit_code=status,
                            timed_out=timed_out, seconds=time.monotonic() - start,
                            inputs_unchanged=unchanged))
        print(index, len(records), "PASS" if passed else "FAIL", flush=True)
    unchanged = digest(binary) == binary_hash and all(
        digest(args.kernel_directory / (name + ".metta")) == pin for name, pin in pins.items())
    passed = unchanged and all(result["passed"] for result in results)
    report = dict(passed=passed, binary_sha256=binary_hash, authored_source_sha256=pins,
                  sources_unchanged=unchanged, dialect="he", programs=results)
    (args.output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
