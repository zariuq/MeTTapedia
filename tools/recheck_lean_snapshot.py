#!/usr/bin/env python3
"""Recheck named Lean sources from freeze_lean_imports.py in dependency order.

Use a new output directory. Rechecked providers are visible to their
consumers and a failed provider blocks its dependent checks. All other
imports come from the snapshot. The receipt includes Lake's freshness
status at capture. Custom module setups and external inputs such as
compile-time file reads need separate qualification.
"""

import argparse
from functools import cache
from graphlib import TopologicalSorter
import json
import os
from pathlib import Path
import subprocess
import sys

from freeze_lean_imports import contents_digest, copy_artifacts


def plan(snapshot, manifest, requested, env):
    objects = snapshot / "objects"
    modules = {entry["name"]: entry for entry in manifest["modules"]}
    object_names = {Path(entry["relative"]).as_posix(): name for name, entry in modules.items()}
    sources = {}
    for entry in manifest["sources"]:
        source = snapshot / entry["copy"]
        root = snapshot / entry["root"]
        relative = source.relative_to(root)
        name = ".".join(relative.with_suffix("").parts)
        if name in requested:
            if name in sources:
                raise ValueError(f"multiple captured sources for {name}")
            if contents_digest(source) != entry["sha256"]:
                raise ValueError(f"captured source changed: {name}")
            sources[name] = (source, root, relative.with_suffix(".olean"))
    if missing := requested.difference(sources):
        raise ValueError(f"missing captured sources: {', '.join(sorted(missing))}")
    artifacts = {Path(entry["path"]): (objects, entry["identity"]) for entry in manifest["files"]}
    for path in artifacts:
        if not (objects / path).is_file():
            raise ValueError(f"missing captured artifact: {path}")

    @cache
    def rebuilt_imports(name):
        if name in sources:
            return frozenset({name})
        return frozenset().union(*(rebuilt_imports(dep) for dep in modules[name]["imports"]))

    graph = {}
    for name, (source, root, _) in sources.items():
        paths = subprocess.check_output(
            [manifest["lean"], "--deps", "--root", root, source], env=env, text=True,
        ).splitlines()
        dependencies = set()
        for path in paths:
            file = Path(path).resolve()
            if not file.is_relative_to(objects):
                raise ValueError(f"{name} resolved an import outside the snapshot: {file}")
            imported = object_names.get(file.relative_to(objects).as_posix())
            if imported is None:
                raise ValueError(f"{name} resolved an unrecorded import: {file}")
            if imported in sources:
                dependencies.add(imported)
            elif providers := rebuilt_imports(imported):
                raise ValueError(
                    f"{name} imports {imported}, whose captured objects depend on "
                    f"{', '.join(sorted(providers))}. Include {imported} in the recheck."
                )
        graph[name] = sorted(dependencies)
    return sources, graph, artifacts


def recheck(snapshot, output, requested, max_memory, measure=False):
    manifest_path = snapshot / "snapshot.json"
    manifest = json.loads(manifest_path.read_text())
    env = {**os.environ, "LEAN_SYSROOT": manifest["lean_sysroot"],
           "LEAN_PATH": str(snapshot / "objects")}
    sources, graph, artifacts = plan(snapshot, manifest, requested, env)
    order = tuple(TopologicalSorter(graph).static_order())
    output.mkdir(parents=True, exist_ok=False)
    products = output / "objects"
    logs = output / "logs"
    logs.mkdir()
    products.mkdir()
    # Lean resolves a whole package prefix in one search-path entry.
    # Omit every old part of a rechecked module from the private copy.
    for _, _, relative in sources.values():
        for extension in (".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig"):
            artifacts.pop(relative.with_suffix(extension), None)
    copy_artifacts(artifacts, products)
    env["LEAN_PATH"] = str(products)
    command = [manifest["lean"], "-j1"]
    if max_memory is not None:
        command += ["-M", str(max_memory)]
    results = {}
    for name in order:
        blockers = [dep for dep in graph[name] if results[dep]["status"] != "passed"]
        if blockers:
            results[name] = {"status": "blocked", "dependencies": blockers}
            print(f"blocked {name} ({', '.join(blockers)})", flush=True)
            continue
        source, root, relative = sources[name]
        olean = products / relative
        olean.parent.mkdir(parents=True, exist_ok=True)
        log = logs / f"{name}.log"
        invocation = [*command, "--root", root, source, "-o", olean]
        if measure:
            timing = log.with_suffix(".time")
            invocation = ["/usr/bin/time", "-q", "-f", "%e %U %S %M", "-o", timing, *invocation]
        with log.open("w") as handle:
            code = subprocess.run(invocation, env=env, stdout=handle,
                                  stderr=subprocess.STDOUT, check=False).returncode
        status = "passed" if code == 0 and olean.is_file() else "failed"
        entry = {"status": status, "returncode": code, "log": str(log.relative_to(output))}
        if measure:
            wall, user, system, rss = timing.read_text().split()
            entry["measurement"] = {
                "wall_seconds": float(wall),
                "cpu_seconds": round(float(user) + float(system), 2),
                "peak_rss_kib": int(rss),
                "olean_bytes": olean.stat().st_size if status == "passed" else None,
            }
        results[name] = entry
        print(f"{status} {name}", flush=True)
    receipt = {
        "snapshot_manifest_sha256": contents_digest(manifest_path),
        "lean_version": manifest["lean_version"],
        "lake_freshness_at_capture": manifest["lake_freshness"],
        "results": results,
    }
    (output / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    return int(any(entry["status"] != "passed" for entry in results.values()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("snapshot", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("modules", nargs="+", help="captured module names")
    parser.add_argument("--max-memory", type=int, help="Lean memory limit in MiB")
    parser.add_argument("--measure", action="store_true",
                        help="record GNU time and olean size for each executed module")
    args = parser.parse_args()
    try:
        return recheck(args.snapshot.resolve(), args.output.resolve(),
                       set(args.modules), args.max_memory, args.measure)
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print(f"snapshot recheck failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
