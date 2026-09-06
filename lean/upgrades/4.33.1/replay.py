#!/usr/bin/env python3
"""Check or apply the recorded external migration to an exact, clean base."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args])


def contained(root, relative):
    path = root / relative
    if Path(relative).is_absolute() or not path.resolve().is_relative_to(root.resolve()):
        raise ValueError(f"Path escapes its root: {relative}")
    return path


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def verify_sources(repo, entry):
    for relative, expected in entry["files"].items():
        path = contained(repo, relative)
        if expected is None:
            if path.exists():
                raise ValueError(f"Expected absent file: {relative}")
        elif not path.is_file() or sha256(path.read_bytes()) != expected:
            raise ValueError(f"Source fingerprint differs: {relative}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repository", help="Repository path relative to lean/")
    parser.add_argument("--lean-root", type=Path, help="Alternate dependency workspace")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--apply", action="store_true", help="Apply to a clean, pinned checkout")
    mode.add_argument("--verify", action="store_true", help="Verify already migrated source fingerprints")
    args = parser.parse_args()
    bundle = Path(__file__).resolve().parent
    lean = args.lean_root or bundle.parent.parent
    manifest = json.loads((bundle / "externals.json").read_text())
    entry = manifest["repositories"][args.repository]
    repo = contained(lean, args.repository)
    patch = contained(bundle, entry["patch"])
    if sha256(patch.read_bytes()) != entry["patch_sha256"]:
        raise ValueError("Migration patch fingerprint differs")
    if args.verify:
        verify_sources(repo, entry)
        print(f"Verified migration: {args.repository}")
        return
    if git(repo, "rev-parse", "HEAD").decode().strip() != entry["base"]:
        raise ValueError("Repository is not at the recorded base revision")
    if git(repo, "status", "--porcelain", "--untracked-files=all").strip():
        raise ValueError("Migration requires a clean checkout; existing work is preserved")
    if not patch.stat().st_size:
        print(f"No migration changes: {args.repository}")
        return
    git(repo, "apply", "--check", str(patch))
    if args.apply:
        git(repo, "apply", str(patch))
        verify_sources(repo, entry)
        print(f"Applied migration: {args.repository}")
    else:
        print(f"Patch applies cleanly: {args.repository}")


if __name__ == "__main__":
    main()
