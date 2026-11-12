#!/usr/bin/env python3
"""Check existing Git dependencies before Lake can replace their checkouts.

An inaccessible repository must not be mistaken for a changed origin URL.
Missing dependencies are left to Lake's normal initial checkout mechanism.
This check does not change Git trust settings, pins, sources, or artifacts.
"""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path


def git_output(checkout: Path, *arguments: str) -> str:
    result = subprocess.run(
        ["git", "-C", str(checkout), *arguments],
        capture_output=True, text=True,
    )
    if result.returncode:
        raise ValueError("Git ownership or repository access check failed")
    return result.stdout.strip()


def check_existing_checkouts(root: Path) -> list[str]:
    manifest = json.loads((root / "lake-manifest.json").read_text())
    packages = root / manifest.get("packagesDir", ".lake/packages")
    failures = []
    for entry in manifest["packages"]:
        if entry["type"] != "git":
            continue
        name = entry["name"].removeprefix("«").removesuffix("»")
        checkout = packages / name
        if not checkout.exists():
            continue
        try:
            actual_root = Path(git_output(checkout, "rev-parse", "--show-toplevel"))
            if actual_root.resolve() != checkout.resolve():
                raise ValueError("the dependency is not its own Git checkout")
            origin = git_output(checkout, "config", "--get", "remote.origin.url")
            if origin != entry["url"]:
                raise ValueError("cached origin differs from the manifest; inspect before replacing it")
        except (ValueError, OSError) as error:
            failures.append(f"{name}: {error}")
    return failures


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project-root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    failures = check_existing_checkouts(args.project_root.resolve())
    for failure in failures:
        print(failure)
    if failures:
        print("Dependency checkout check failed; Lake was not invoked.")
    return int(bool(failures))


if __name__ == "__main__":
    raise SystemExit(main())
