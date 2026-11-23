#!/usr/bin/env python3
"""Check that the tracked Lean sources build from a clean checkout.

A clean checkout contains only tracked files. A tracked module that imports an
untracked module, or quotes an untracked MeTTa source with `petta_source_file%`,
builds only in a working tree that happens to contain the untracked file.

For every tracked `.lean` file under lean/mettapedia this reports:
  * imports of local `Mettapedia.*` modules whose file is untracked;
  * `petta_source_file%` targets that are missing, untracked or differ from
    their sha256 pin;
  * lakefile `input_file` / `input_dir` paths that are untracked.

Files named in an add-list (one repository-relative or absolute path per line)
count as tracked, so the check can be run against a proposed addition.
`--suggest` prints the smallest add-list that closes the import graph: the
untracked modules reachable from tracked ones, their own untracked imports,
and the untracked sources they quote.

Exit status: 0 when nothing is reported, 1 otherwise.
"""

from __future__ import annotations

import argparse
import hashlib
import os
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
LEAN_ROOT = REPO / "lean" / "mettapedia"
IMPORT = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*$")
PIN = re.compile(r'petta_source_file%\s*"([^"]+)"\s*sha256\s*"([0-9a-f]{64})"')
INPUT = re.compile(r"^(input_file|input_dir)\s+(\S+)\s+where\s*$")
INPUT_PATH = re.compile(r'^\s+path\s*:=\s*"([^"]+)"')


def git_tracked(path: Path) -> bool:
    """Whether `path` is tracked by the git repository that contains it."""
    directory = path if path.is_dir() else path.parent
    if not directory.exists():
        return False
    if path.is_dir():
        listing = subprocess.run(
            ["git", "-C", str(directory), "ls-files", "--", "."],
            capture_output=True, text=True)
        return listing.returncode == 0 and bool(listing.stdout.strip())
    result = subprocess.run(
        ["git", "-C", str(directory), "ls-files", "--error-unmatch", "--", path.name],
        capture_output=True, text=True)
    return result.returncode == 0


def repository_of(path: Path) -> Path | None:
    directory = path if path.is_dir() else path.parent
    result = subprocess.run(
        ["git", "-C", str(directory), "rev-parse", "--show-toplevel"],
        capture_output=True, text=True)
    return Path(result.stdout.strip()) if result.returncode == 0 else None


def tracked_lean_files() -> list[Path]:
    listing = subprocess.run(
        ["git", "-C", str(REPO), "ls-files", "--", "lean/mettapedia/*.lean"],
        capture_output=True, text=True, check=True)
    return [REPO / line for line in listing.stdout.splitlines()
            if "/.lake/" not in line and line.endswith(".lean")]


def header_imports(path: Path) -> list[tuple[int, str]]:
    """Module names imported in the header, with their line numbers."""
    imports: list[tuple[int, str]] = []
    in_comment = 0
    for number, line in enumerate(path.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
        stripped = line.strip()
        if in_comment:
            in_comment += stripped.count("/-") - stripped.count("-/")
            continue
        if not stripped or stripped.startswith("--"):
            continue
        if stripped.startswith("/-"):
            in_comment = stripped.count("/-") - stripped.count("-/")
            continue
        if stripped in ("prelude", "module"):
            continue
        match = IMPORT.match(line)
        if not match:
            break
        for name in match.group(1).split():
            if name != "runtime":
                imports.append((number, name))
    return imports


def module_file(name: str) -> Path | None:
    if name != "Mettapedia" and not name.startswith("Mettapedia."):
        return None
    return LEAN_ROOT / (name.replace(".", "/") + ".lean")


def pins(path: Path) -> list[tuple[Path, str]]:
    text = path.read_text(encoding="utf-8", errors="replace")
    return [((path.parent / relative).resolve(), digest)
            for relative, digest in PIN.findall(text)]


def lakefile_inputs() -> list[tuple[int, str, Path]]:
    lakefile = LEAN_ROOT / "lakefile.lean"
    found: list[tuple[int, str, Path]] = []
    pending: str | None = None
    for number, line in enumerate(lakefile.read_text(encoding="utf-8").splitlines(), 1):
        header = INPUT.match(line)
        if header:
            pending = header.group(2)
            continue
        path = INPUT_PATH.match(line)
        if pending and path:
            found.append((number, pending, (LEAN_ROOT / path.group(1)).resolve()))
            pending = None
    return found


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--add-list", type=Path,
                        help="paths that will be added; they count as tracked")
    parser.add_argument("--suggest", action="store_true",
                        help="print the smallest add-list that closes the graph")
    parser.add_argument("--target", action="append", default=[],
                        help="check only what this module reaches, e.g. Mettapedia "
                             "(repeatable); every reached file must be tracked")
    arguments = parser.parse_args()

    added: set[Path] = set()
    if arguments.add_list:
        for line in arguments.add_list.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if line and not line.startswith("#"):
                candidate = Path(line)
                added.add((candidate if candidate.is_absolute() else REPO / candidate).resolve())

    listing = subprocess.run(["git", "-C", str(REPO), "ls-files"],
                             capture_output=True, text=True, check=True)
    in_repository = {(REPO / line).resolve() for line in listing.stdout.splitlines()}
    tracked_cache: dict[Path, bool] = {}

    def tracked(path: Path) -> bool:
        path = path.resolve()
        if path in added:
            return True
        if path.is_relative_to(REPO) and not path.is_dir():
            return path in in_repository
        if path not in tracked_cache:
            tracked_cache[path] = git_tracked(path)
        return tracked_cache[path]

    problems: list[str] = []
    suggestion: list[Path] = []
    seen: set[Path] = set()
    reach_all = bool(arguments.target)
    if reach_all:
        queue = []
        for name in arguments.target:
            path = module_file(name)
            if path is None or not path.exists():
                parser.error(f"{name} is not a local module with a file")
            queue.append(path.resolve())
    else:
        queue = [path.resolve() for path in tracked_lean_files()]
        queue += [path for path in sorted(added)
                  if path.suffix == ".lean" and path.is_relative_to(LEAN_ROOT) and path.exists()]
    queued = set(queue)
    roots = set(queue)

    while queue:
        source = queue.pop()
        if source in seen:
            continue
        seen.add(source)
        shown = source.relative_to(REPO)
        for number, name in header_imports(source):
            target = module_file(name)
            if target is None:
                continue
            if not target.exists():
                problems.append(f"{shown}:{number}: imports {name}, which has no file")
            elif not tracked(target):
                if reach_all or source in roots:
                    problems.append(f"{shown}:{number}: imports untracked {name}")
                if target.resolve() not in queued:
                    suggestion.append(target.resolve())
                    queued.add(target.resolve())
                    queue.append(target.resolve())
            elif reach_all and target.resolve() not in queued:
                queued.add(target.resolve())
                queue.append(target.resolve())
        for target, digest in pins(source):
            if not target.exists():
                problems.append(f"{shown}: quotes missing {target}")
                continue
            if hashlib.sha256(target.read_bytes()).hexdigest() != digest:
                problems.append(f"{shown}: quotes {target}, which differs from its pin")
            if not tracked(target):
                if reach_all or source in roots:
                    problems.append(f"{shown}: quotes untracked {target}")
                if target not in suggestion:
                    suggestion.append(target)
            elif repository_of(target) != REPO:
                print(f"note: {shown} quotes {target} from another repository",
                      file=sys.stderr)

    for number, name, path in ([] if reach_all else lakefile_inputs()):
        if not path.exists():
            problems.append(f"lean/mettapedia/lakefile.lean:{number}: input {name} is missing: {path}")
        elif not tracked(path):
            problems.append(f"lean/mettapedia/lakefile.lean:{number}: input {name} is untracked: {path}")

    if arguments.suggest:
        for path in suggestion:
            print(path.relative_to(REPO) if path.is_relative_to(REPO) else path)
        return 0

    for problem in problems:
        print(problem)
    scope = (f"reached from {', '.join(arguments.target)} ({len(seen)} files)" if reach_all
             else f"in {len(roots)} tracked Lean files")
    print(f"{len(problems)} problem(s) {scope}", file=sys.stderr)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
