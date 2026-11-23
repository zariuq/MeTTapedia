#!/usr/bin/env python3
"""External-oracle checks for the source clauses modeled by the Lean query modes."""

import argparse
import os
from pathlib import Path
import shutil
import subprocess


def run_checked(command, cwd, expected, env=None):
    result = subprocess.run(command, cwd=cwd, env=env, capture_output=True, text=True, check=True)
    if result.stderr or result.stdout != expected:
        raise AssertionError(
            f"Unexpected source-engine result\nstdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--petta", type=Path, required=True, help="PeTTa checkout")
    args = parser.parse_args()
    source = args.petta.resolve()
    fixture = Path(__file__).resolve().parent
    environment = os.environ.copy()
    python312 = shutil.which("python3.12")
    if python312:
        libdir = subprocess.check_output(
            [python312, "-c", 'import sysconfig; print(sysconfig.get_config_var("LIBDIR") or "")'],
            text=True,
        ).strip()
        if (Path(libdir) / "libpython3.12.so.1.0").is_file():
            environment["LD_LIBRARY_PATH"] = os.pathsep.join(
                filter(None, [libdir, environment.get("LD_LIBRARY_PATH")])
            )
    run_checked(
        ["bash", str(source / "run.sh"), "--silent", str(fixture / "petta_query_modes.metta")],
        source,
        (fixture / "petta_query_modes.expected").read_text(),
        environment,
    )
    run_checked(
        ["bash", str(source / "run.sh"), "--silent", str(fixture / "petta_v106_call_contracts.metta")],
        source,
        (fixture / "petta_v106_call_contracts.expected").read_text(),
        environment,
    )
    run_checked(
        ["swipl", "-q", "-s", "src/metta.pl", "-s", str(fixture / "petta_query_modes.pl"),
         "-g", "type_query_mode_controls,halt", "-t", "halt(1)"],
        source,
        "PASS: fresh output, bound output, primitive cuts and bound recursive arguments\n",
        environment,
    )
    print("PASS: PeTTa query modes, argument/result checks and held Atom arguments")


if __name__ == "__main__":
    main()
