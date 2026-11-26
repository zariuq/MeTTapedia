#!/usr/bin/env python3
"""Recheck named Lean sources from freeze_lean_imports.py in dependency order.

Use a new output directory. Rechecked providers are visible to their
consumers and a failed provider blocks its dependent checks. All other
imports and declared elaboration inputs come from the snapshot. The receipt
includes Lake's freshness status at capture. Custom module setups and native
plugins need separate qualification.
"""

import argparse
from collections import deque
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from functools import cache
from graphlib import TopologicalSorter
import json
import os
from pathlib import Path
import stat
import subprocess
import sys

from freeze_lean_imports import contents_digest, copy_artifacts, sealed_identity


ARTIFACT_GROUPS = ((".olean", ".olean.server", ".olean.private"), (".ir.sig", ".ir"))


def rebuilt_artifacts(sources):
    return {
        relative.with_suffix(extension)
        for _, _, relative in sources.values()
        for group in ARTIFACT_GROUPS
        for extension in group
    }


def plan(snapshot, manifest, requested, env, *, link_imports=False):
    objects = snapshot / "objects"
    for entry in manifest.get("elaboration_inputs", []):
        path = snapshot / entry["copy"]
        link = os.readlink(path) if path.is_symlink() else None
        if (link != entry.get("link") or not path.resolve().is_relative_to(snapshot / "sources")
                or contents_digest(path) != entry["sha256"]):
            raise ValueError(f"captured elaboration input changed: {entry['copy']}")
    modules = {entry["name"]: entry for entry in manifest["modules"]}
    source_only = set(manifest.get("source_only_modules", []))
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
    rebuilt_parts = rebuilt_artifacts(sources) if link_imports else set()
    for path in artifacts:
        artifact = objects / path
        if not artifact.resolve().is_relative_to(objects):
            raise ValueError(f"recorded artifact is outside the snapshot: {path}")
        try:
            mode = artifact.stat().st_mode
        except FileNotFoundError:
            raise ValueError(f"missing captured artifact: {path}") from None
        if not stat.S_ISREG(mode):
            raise ValueError(f"missing captured artifact: {path}")
        if link_imports and path not in rebuilt_parts and mode & 0o222:
            raise ValueError(f"shared compiled import must be read-only inside the snapshot: {path}")

    @cache
    def rebuilt_imports(name):
        if name in sources or name in source_only:
            return frozenset({name})
        return frozenset().union(*(rebuilt_imports(dep) for dep in modules[name]["imports"]))

    # Parse source imports in one Lean invocation so a requested provider can
    # be checked before its first compiled artifact exists.
    headers = json.loads(subprocess.check_output(
        [manifest["lean"], "--deps-json", *(row[0] for row in sources.values())],
        env=env, text=True,
    ))["imports"]
    graph = {}
    for name, header in zip(sources, headers, strict=True):
        if header["errors"]:
            raise ValueError(f"invalid import header of {name}: {header['errors']}")
        dependencies = set()
        for entry in header["result"]["imports"]:
            imported = entry["module"]
            if imported in sources:
                dependencies.add(imported)
            elif imported in source_only:
                raise ValueError(f"{name} requires source-only module {imported}. "
                                 f"Include {imported} in the recheck.")
            elif imported not in modules:
                raise ValueError(f"{name} has an unrecorded import: {imported}")
            elif providers := rebuilt_imports(imported):
                raise ValueError(
                    f"{name} imports {imported}, whose captured objects depend on "
                    f"{', '.join(sorted(providers))}. Include {imported} in the recheck."
                )
        graph[name] = sorted(dependencies)
    return sources, graph, artifacts


def validate_sealed_imports(snapshot, manifest, artifacts):
    sealed = manifest.get("sealed_artifacts")
    if sealed is None:
        raise ValueError("mapped imports require a sealed snapshot")
    for relative in artifacts:
        status = (snapshot / "objects" / relative).lstat()
        if (not stat.S_ISREG(status.st_mode) or status.st_mode & 0o222
                or sealed_identity(status) != sealed.get(str(relative))):
            raise ValueError(f"captured import changed: {relative}")


def module_artifacts(root, relative, present):
    return [
        [os.fspath(root / part) for suffix in group
         if present(part := relative.with_suffix(suffix))]
        for group in ARTIFACT_GROUPS
    ]


def recheck(snapshot, output, requested, max_memory, measure=False, jobs=1,
            link_imports=False, map_imports=False):
    if jobs < 1:
        raise ValueError("jobs must be positive")
    if link_imports and map_imports:
        raise ValueError("select one retained import mode")
    manifest_path = snapshot / "snapshot.json"
    manifest = json.loads(manifest_path.read_text())
    env = {**os.environ, "LEAN_SYSROOT": manifest["lean_sysroot"],
           "LEAN_PATH": str(snapshot / "objects")}
    sources, graph, artifacts = plan(snapshot, manifest, requested, env,
                                     link_imports=link_imports or map_imports)
    scheduler = TopologicalSorter(graph)
    scheduler.prepare()
    # Every rebuilt module supplies its new artifact parts to dependent checks.
    for path in rebuilt_artifacts(sources):
        artifacts.pop(path, None)
    if map_imports:
        validate_sealed_imports(snapshot, manifest, artifacts)
        retained = {}
        for entry in manifest["modules"]:
            if entry["name"] in sources:
                continue
            relative = Path(entry["relative"])
            parts = module_artifacts(snapshot / "objects", relative, artifacts.__contains__)
            if (relative not in artifacts
                    or entry["moduleSystem"] and len(parts[0]) != len(ARTIFACT_GROUPS[0])):
                raise ValueError(f"missing recorded import parts: {entry['name']}")
            retained[entry["name"]] = parts
    output.mkdir(parents=True, exist_ok=False)
    products = output / "objects"
    logs = output / "logs"
    logs.mkdir()
    products.mkdir()
    if map_imports:
        env["LEAN_PATH"] = ""
    else:
        copy_artifacts(artifacts, products, link=link_imports)
        env["LEAN_PATH"] = str(products)
    command = [manifest["lean"], "-j1"]
    if max_memory is not None:
        command += ["-M", str(max_memory)]

    def check(name, setup):
        source, root, relative = sources[name]
        olean = products / relative
        olean.parent.mkdir(parents=True, exist_ok=True)
        log = logs / f"{name}.log"
        invocation = [*command, "--root", root, source, "-o", olean]
        if setup is not None:
            invocation.append("--setup=/dev/stdin")
        if measure:
            timing = log.with_suffix(".time")
            invocation = ["/usr/bin/time", "-q", "-f", "%e %U %S %M", "-o", timing, *invocation]
        with log.open("w") as handle:
            code = subprocess.run(invocation, env=env, input=setup, stdout=handle,
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
        return entry

    results = {}
    ready = deque(scheduler.get_ready())
    running = {}
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        while ready or running:
            while ready and len(running) < jobs:
                name = ready.popleft()
                blockers = [dep for dep in graph[name] if results[dep]["status"] != "passed"]
                if blockers:
                    results[name] = {"status": "blocked", "dependencies": blockers}
                    print(f"blocked {name} ({', '.join(blockers)})", flush=True)
                    scheduler.done(name)
                    ready.extend(scheduler.get_ready())
                else:
                    setup = None
                    if map_imports:
                        # Leave import flags and module-system participation to
                        # the source header. Lean reads only the selected paths.
                        setup = json.dumps({
                            "name": name, "isModule": False, "importArts": retained,
                            "dynlibs": [], "plugins": [], "options": {},
                        }).encode()
                    running[pool.submit(check, name, setup)] = name
            if running:
                finished, _ = wait(running, return_when=FIRST_COMPLETED)
                for future in sorted(finished, key=running.__getitem__):
                    name = running.pop(future)
                    entry = future.result()
                    results[name] = entry
                    if map_imports and entry["status"] == "passed":
                        relative = sources[name][2]
                        retained[name] = module_artifacts(
                            products, relative, lambda part: (products / part).is_file())
                    print(f"{entry['status']} {name}", flush=True)
                    scheduler.done(name)
                ready.extend(scheduler.get_ready())
    receipt = {
        "snapshot_manifest_sha256": contents_digest(manifest_path),
        "lean_version": manifest["lean_version"],
        "lake_freshness_at_capture": manifest["lake_freshness"],
        "jobs": jobs,
        "results": dict(sorted(results.items())),
    }
    if link_imports:
        receipt["linked_retained_imports"] = len(artifacts)
    if map_imports:
        validate_sealed_imports(snapshot, manifest, artifacts)
        receipt["mapped_retained_imports"] = len(artifacts)
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
    imports = parser.add_mutually_exclusive_group()
    imports.add_argument("--link-imports", action="store_true",
                         help="link the snapshot's read-only retained imports into the product view")
    imports.add_argument("--map-imports", action="store_true",
                         help="load sealed imports in place with a Lean module setup")
    parser.add_argument("--jobs", type=int, default=1,
                        help="maximum independent Lean checks running at once")
    args = parser.parse_args()
    try:
        return recheck(args.snapshot.resolve(), args.output.resolve(),
                       set(args.modules), args.max_memory, args.measure, args.jobs,
                       args.link_imports, args.map_imports)
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print(f"snapshot recheck failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
