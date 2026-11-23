#!/usr/bin/env python3
"""Capture a Lean import closure for isolated source checks.

Run under the intended Lake environment. The manifest records the pinned Lean
binary, copied artifacts, input sources, and any requested Lake freshness check.
Run rechecks with the recorded Lean binary and LEAN_SYSROOT, LEAN_PATH set to
the snapshot's objects directory, and --root set to the recorded copied root.
A custom module setup, native plugin, or other filesystem input needs its own snapshot.
"""

import argparse
from collections import defaultdict
from datetime import datetime, timezone
from hashlib import sha256
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys


def run_text(command, env=None):
    return subprocess.check_output(command, env=env, text=True).strip()


def contents_digest(path):
    return sha256(path.read_bytes()).hexdigest()


def stamp(path):
    try:
        stat = path.stat()
    except FileNotFoundError:
        return None
    return (stat.st_dev, stat.st_ino, stat.st_size, stat.st_mtime_ns, stat.st_ctime_ns)


def import_graph(lean, helper, sources, env=None):
    bootstrap = dict(os.environ if env is None else env)
    path = bootstrap.pop("LEAN_PATH", "")
    modules = json.loads(run_text([lean, "--run", helper, path, *sources], bootstrap))
    return sorted(modules, key=lambda module: module["name"])


def copy_plan(modules):
    files = {}
    for module in modules:
        source = Path(module["object"]).absolute()
        relative = Path(module["relative"])
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError(f"invalid module path {relative}")
        prefix = source.parents[len(relative.parts) - 1]
        if prefix / relative != source:
            raise ValueError(f"{source} does not resolve as {relative}")
        candidates = {
            relative: True,
            relative.with_suffix(".olean.private"): module["moduleSystem"],
            relative.with_suffix(".olean.server"): module["moduleSystem"],
            relative.with_suffix(".ir"): False,
            relative.with_suffix(".ir.sig"): False,
        }
        for artifact, required in candidates.items():
            live = prefix / artifact
            identity = stamp(live)
            if required and identity is None:
                raise FileNotFoundError(f"missing compiled import part {live}")
            if artifact in files and files[artifact][0] != prefix:
                raise ValueError(f"conflicting import resolutions for {artifact}")
            files[artifact] = (prefix, identity)
        if files[relative.with_suffix(".ir.sig")][1] is not None:
            ir = relative.with_suffix(".ir")
            if files[ir][1] is None:
                raise FileNotFoundError(f"missing compiled import part {prefix / ir}")
    return files


def copy_artifacts(files, objects):
    by_prefix = defaultdict(list)
    for relative, (prefix, identity) in files.items():
        if identity is not None:
            by_prefix[prefix].append(relative)
    for prefix, paths in sorted(by_prefix.items()):
        for start in range(0, len(paths), 256):
            batch = sorted(paths[start:start + 256])
            subprocess.run(
                ["cp", "--reflink=auto", "--parents", "--", *batch, objects],
                cwd=prefix,
                check=True,
            )


def capture(args):
    cwd = Path.cwd()
    sources = [file.resolve(strict=True) for file in args.sources]
    output = args.output.resolve()
    helper = Path(__file__).with_name("lean_import_graph.lean").resolve()
    prefix = Path(run_text(["lean", "--print-prefix"])).resolve(strict=True)
    lean = prefix / "bin" / "lean"
    lean_env = {**os.environ, "LEAN_SYSROOT": str(prefix)}
    source_root = args.source_root.resolve(strict=True) if args.source_root else cwd
    if not source_root.is_dir():
        raise ValueError(f"source root is not a directory: {source_root}")
    if args.source_root:
        for path in sources:
            if not path.is_relative_to(source_root):
                raise ValueError(f"source is outside the specified root: {path}")
    initial_sources = {path: stamp(path) for path in sources}
    package_files = [
        path for name in ("lean-toolchain", "lakefile.lean", "lakefile.toml", "lake-manifest.json")
        if (path := cwd / name).is_file()
    ]
    package_digests = {
        path.relative_to(cwd).as_posix(): contents_digest(path) for path in package_files
    }
    modules = import_graph(lean, helper, sources, lean_env)
    files = copy_plan(modules)
    output.mkdir(parents=True, exist_ok=False)
    objects = output / "objects"
    objects.mkdir()
    code = None
    if args.fresh_target:
        with (output / "lake-freshness.log").open("w") as log:
            code = subprocess.run(
                ["lake", "--no-build", "build", *args.fresh_target],
                stdout=log, stderr=subprocess.STDOUT, check=False,
            ).returncode
    copy_artifacts(files, objects)
    recorded_sources = []
    for index, path in enumerate(sources):
        root = source_root if path.is_relative_to(source_root) else path.parent
        copied_root = output / "sources" / f"{index:03d}"
        saved = copied_root / path.relative_to(root)
        saved.parent.mkdir(parents=True)
        shutil.copyfile(path, saved)
        recorded_sources.append({
            "source": str(path), "copy": str(saved.relative_to(output)),
            "root": str(copied_root.relative_to(output)),
            "sha256": contents_digest(saved),
        })
    for relative, (directory, identity) in files.items():
        if stamp(directory / relative) != identity:
            raise RuntimeError(f"compiled import changed during capture: {directory / relative}")
    for path, identity in initial_sources.items():
        if stamp(path) != identity:
            raise RuntimeError(f"source changed during capture: {path}")
    for path in package_files:
        if contents_digest(path) != package_digests[path.relative_to(cwd).as_posix()]:
            raise RuntimeError(f"package configuration changed during capture: {path}")
    if import_graph(lean, helper, sources, lean_env) != modules:
        raise RuntimeError("live import resolution changed during capture")

    frozen_env = {**lean_env, "LEAN_PATH": str(objects)}
    frozen_sources = [output / record["copy"] for record in recorded_sources]
    frozen = import_graph(lean, helper, frozen_sources, frozen_env)
    if len(frozen) != len(modules):
        raise RuntimeError("the frozen dependency closure has a different size")
    for recorded, actual in zip(modules, frozen, strict=True):
        if actual["object"] != str(objects / actual["relative"]):
            raise RuntimeError(f"compiled import resolved outside the snapshot: {actual['name']}")
        if {**actual, "object": recorded["object"]} != recorded:
            raise RuntimeError(f"compiled import header changed during capture: {actual['name']}")

    manifest = {
        "captured_at": datetime.now(timezone.utc).isoformat(),
        "lean": str(lean), "lean_sysroot": str(prefix),
        "lean_version": run_text([lean, "--version"], lean_env),
        "package_files": package_digests,
        "sources": recorded_sources,
        "modules": modules,
        "files": [{"path": str(path), "identity": identity}
                  for path, (_, identity) in sorted(files.items()) if identity is not None],
        "lake_freshness": {"targets": args.fresh_target, "exit_code": code},
    }
    (output / "snapshot.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Captured {len(modules)} modules and {len(manifest['files'])} artifact parts")
    if code is not None:
        print(f"Lake freshness check exit status {code}. See lake-freshness.log.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="new snapshot directory")
    parser.add_argument("sources", type=Path, nargs="+", help="Lean inputs to recheck")
    parser.add_argument("--source-root", type=Path,
                        help="common Lean module root for the input sources")
    parser.add_argument("--fresh-target", action="append", default=[],
                        help="Lake target to check with --no-build during capture")
    try:
        capture(parser.parse_args())
    except subprocess.CalledProcessError as error:
        print(f"snapshot capture failed: {Path(error.cmd[0]).name} exited with status {error.returncode}",
              file=sys.stderr)
        return 1
    except (OSError, ValueError, RuntimeError) as error:
        print(f"snapshot capture failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
