#!/usr/bin/env python3
"""Run the fixed ground-CHR reference controls in independent SWI stores."""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--swipl", type=Path)
    parser.add_argument("--timeout", type=float, default=30, help="seconds allowed for each reference control")
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    source = Path(__file__).resolve().parents[1] / "module/gold/CHR/examples/ground_core.pl"
    swipl = (args.swipl or Path(shutil.which("swipl") or "swipl")).resolve()
    version = subprocess.run([str(swipl), "--version"], text=True, capture_output=True, check=True).stdout.strip()
    configuration = subprocess.run([str(swipl), "--dump-runtime-variables"], text=True, capture_output=True, check=True).stdout
    (output / "build-configuration.txt").write_text(configuration)
    library_query = ("forall(member(L,[chr,'chr/chr_translate','chr/chr_compiler_options']),"
                     "(absolute_file_name(library(L),F,[file_type(prolog),access(read)]),writeln(F))),halt")
    libraries = subprocess.run([str(swipl), "-q", "-g", library_query], text=True, capture_output=True, check=True).stdout.splitlines()
    pins = {str(path): digest(path) for path in [Path(__file__).resolve(), source, swipl, *map(Path, libraries)]}
    labels = ["gcd", "sieve", "minimum_duplicates", "fibonacci", "cyclic_paths", "empty",
              "propagation_occurrences", "ordered_propagation_heads", "propagation_needs_two",
              "removed_head_first", "two_resources", "one_resource", "disabled_head", "allocation", "guard_false", "guard_true",
              "partner_choice", "partner_choice_wide", "partner_pair", "guarded_partner"]
    records = []
    for label in labels:
        started = time.monotonic()
        try:
            result = subprocess.run([str(swipl), "-q", "-s", str(source), "--", label], text=True,
                                    capture_output=True, timeout=args.timeout)
            (output / f"{label}.out").write_text(result.stdout)
            (output / f"{label}.err").write_text(result.stderr)
            record = json.loads(result.stdout) if result.returncode == 0 else {"passed": False}
            record["passed"] = record["passed"] and not result.stderr.strip()
            record.update(exit_code=result.returncode, completed=result.returncode == 0)
        except subprocess.TimeoutExpired as fault:
            (output / f"{label}.out").write_text((fault.stdout or b"").decode())
            (output / f"{label}.err").write_text((fault.stderr or b"").decode())
            record = {"passed": False, "completed": False, "reason": "reference budget exhausted"}
        record.update(control=label, seconds=time.monotonic() - started)
        records.append(record)
    changed = [path for path, before in pins.items() if digest(Path(path)) != before]
    record = {"version": version, "build_configuration_sha256": digest(output / "build-configuration.txt"),
              "controls": records, "pins": pins, "changed_inputs": changed,
              "all_passed": all(row["passed"] for row in records) and not changed,
              "scope": "Native reference fixtures only; CHR source-to-native correspondence remains open"}
    (output / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record, indent=2))
    if not record["all_passed"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
