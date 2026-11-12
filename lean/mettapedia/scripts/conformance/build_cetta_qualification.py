#!/usr/bin/env python3
"""Compile a private CeTTa qualification artifact from its Makefile inputs.

This replays the selected ordinary C object/link recipes into an evidence
directory. Generated source/header artifacts must already exist and are pinned
as inputs; their generators are not rerun. No shared objects or executable are
overwritten. Selected runtime libraries may be staged beside the private
binary; their source and staged digests are retained. Success binds the
resulting artifact to its complete discovered project input inventory, not to
a claim about authored-source generation.
"""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import time
import uuid


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cetta-tree", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--compiler", required=True,
                        help="C compiler executable (an absolute path avoids environment ambiguity)")
    parser.add_argument("--build", choices=("core", "python"), default="python")
    parser.add_argument("--sanitize", action="store_true")
    parser.add_argument("--runtime-stats", action="store_true",
                        help="Enable the runtime's existing counters for coverage evidence")
    parser.add_argument("--stage-runtime-library", action="append", default=[],
                        help="Project-relative runtime library to copy beside the private binary")
    parser.add_argument("--jobs", type=int, default=2)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    root, out = args.cetta_tree.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    compiler_path = shutil.which(args.compiler)
    if compiler_path is None:
        parser.error("compiler executable not found")
    compiler = str(Path(compiler_path).resolve())
    staged_libraries = []
    for spelling in dict.fromkeys(args.stage_runtime_library):
        relative = Path(spelling)
        if (relative.is_absolute() or ".." in relative.parts or
                not relative.parts or relative.parts[0] != "lib"):
            parser.error("staged runtime libraries must be project-relative members of lib/")
        source = (root / relative).resolve()
        try:
            source.relative_to(root)
        except ValueError:
            parser.error("staged runtime library escapes the CeTTa tree")
        if not source.is_file():
            parser.error(f"staged runtime library does not exist: {spelling}")
        staged_libraries.append((relative, source))
    record = dict(status="running", qualified=False, run_id=uuid.uuid4().hex,
                  started_at=datetime.now(timezone.utc).isoformat(),
                  generated_inputs="Existing generated C/header artifacts, not regeneration")
    report = out / "build.json"

    def save() -> None:
        report.write_text(json.dumps(record, indent=2) + "\n")

    save()
    environment = dict(os.environ, TMPDIR=str(out / "temporary"))
    (out / "temporary").mkdir(exist_ok=True)
    (out / "objects").mkdir(exist_ok=True)
    (out / "logs").mkdir(exist_ok=True)

    def run(command: list[str], *, timeout: int = 600) -> str:
        result = subprocess.run(command, cwd=root, env=environment, text=True,
                                capture_output=True, timeout=timeout)
        if result.returncode or result.stderr:
            raise RuntimeError(f"command failed or emitted diagnostics ({result.returncode}): "
                               f"{shlex.join(command)}\n{result.stdout}\n{result.stderr}")
        return result.stdout

    try:
        # No prerequisites: the supplemental target only reads Make variables.
        # In particular it cannot regenerate the shared bootstrap artifacts.
        names = ("SRC", "OBJ", "CPPFLAGS", "CFLAGS", "LDFLAGS", "BUILD_CONFIG_HEADER",
                 "PARSER_BAKED_HEADER", "BRIDGE_DEPS", "BUILD_OBJ_TAG", "CC",
                 "MAKEFILE_LIST", "ENABLE_RUNTIME_STATS", "PARSER_BAKED_OBJ")
        request = out / "inputs.mk"
        request.write_text(".PHONY: qualification-inputs\nqualification-inputs:\n\t@:\n" +
                           "".join(f"$(info QUAL_{name}=$({name}))\n" for name in names))
        make = ["make", "-s", "-f", "Makefile", "-f", str(request),
                f"BUILD={args.build}", f"ENABLE_SANITIZERS={int(args.sanitize)}",
                f"ENABLE_RUNTIME_STATS={int(args.runtime_stats)}",
                f"CC={compiler}", "qualification-inputs"]

        def read_make() -> dict[str, str]:
            text = run(make)
            fields = dict(line[5:].split("=", 1) for line in text.splitlines()
                          if line.startswith("QUAL_"))
            if set(fields) != set(names):
                raise RuntimeError("Makefile did not return the complete requested build inputs")
            return fields

        config = read_make()
        # Additional object owners need their own replay qualification. Refuse
        # an unsupported recipe instead of silently omitting its inputs.
        if config["BRIDGE_DEPS"].strip():
            raise RuntimeError("this replay requires the ordinary C link without Rust bridge objects")
        sources = list(dict.fromkeys(shlex.split(config["SRC"])))
        if "native/parser_baked_v1.c" not in sources:
            raise RuntimeError("missing ordinary baked-parser translation unit")
        suffix = ("." + config["BUILD_OBJ_TAG"] +
                  (".runtime-stats" if args.runtime_stats else "") + ".o")
        expected_objects = [source[:-2] + suffix for source in sources
                            if source != "native/parser_baked_v1.c"]
        expected_objects.append(config["PARSER_BAKED_OBJ"])
        if shlex.split(config["OBJ"]) != expected_objects:
            raise RuntimeError("Make's ordered object list has an unsupported source/object recipe")
        # Make appends the specially compiled parser object after the ordinary
        # objects. Preserve that order at link time as well as its flags.
        sources = [source for source in sources if source != "native/parser_baked_v1.c"] + ["native/parser_baked_v1.c"]
        objects = [out / "objects" / (str(index) + ".o") for index in range(len(sources))]
        cpp = shlex.split(config["CPPFLAGS"])
        cflags, ldflags = shlex.split(config["CFLAGS"]), shlex.split(config["LDFLAGS"])

        def flags(source: str) -> list[str]:
            extra = ([f'-DCETTA_PARSER_BAKED_HEADER="{config["PARSER_BAKED_HEADER"]}"']
                     if source == "native/parser_baked_v1.c" else [])
            return [compiler] + cpp + cflags + extra

        def dependencies(source: str) -> set[Path]:
            text = run(flags(source) + ["-MM", "-MT", "qualification", source])
            words = shlex.split(text.replace("\\\n", " ").split(":", 1)[1])
            return {(root / name).resolve() for name in words}

        inputs = {Path(__file__).resolve(), Path(compiler), root / "VERSION", request}
        inputs.update(source for _, source in staged_libraries)
        inputs.update((root / name).resolve() for name in shlex.split(config["MAKEFILE_LIST"]))
        # Dependency files included by Make describe previous builds, not the
        # current C input closure. Their names may change independently. Pin
        # the actual Make rule sources and rediscover C headers below.
        inputs = {path for path in inputs if path.suffix != ".d"}
        source_dependencies = {}
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            futures = {pool.submit(dependencies, source): source for source in sources}
            for future in as_completed(futures):
                source = futures[future]
                found = future.result()
                source_dependencies[source] = found
                inputs.update(found)
        before = {str(path): digest(path) for path in sorted(inputs)}
        record.update(inputs=before, configuration=config, source_count=len(sources))
        save()
        (out / "configuration.json").write_text(json.dumps(config, indent=2) + "\n")
        started = time.monotonic()

        def compile_one(index: int) -> dict:
            source = sources[index]
            command = flags(source) + ["-MMD", "-MF", str(out / "objects" / f"{index}.d"),
                                       "-c", source, "-o", str(objects[index])]
            began = time.monotonic()
            result = subprocess.run(command, cwd=root, env=environment, text=True,
                                    capture_output=True, timeout=600)
            (out / "logs" / f"{index}.log").write_text(result.stdout + result.stderr)
            if result.returncode or result.stderr:
                raise RuntimeError(f"compilation failed/diagnosed {source}; see logs/{index}.log")
            return dict(source=source, command=command, sha256=digest(objects[index]),
                        seconds=round(time.monotonic() - began, 6))

        compiled = []
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            futures = {pool.submit(compile_one, index): index for index in range(len(sources))}
            try:
                for future in as_completed(futures):
                    compiled.append(future.result())
                    if len(compiled) % 25 == 0:
                        print(f"Compiled {len(compiled)}/{len(sources)} translation units", flush=True)
            except Exception:
                for future in futures:
                    future.cancel()
                raise
        record["objects"] = sorted(compiled, key=lambda item: item["source"])
        save()
        binary = out / "cetta"
        link = [compiler] + cflags + ["-Wl,--export-dynamic", "-o", str(binary)] + list(map(str, objects)) + ldflags
        run(link)
        after = {str(path): digest(path) for path in sorted(inputs)}
        config_after = read_make()
        # Make's list of included historical dependency files is not itself
        # an executable setting; every other emitted setting must agree.
        same_config = all(config[key] == config_after[key] for key in names if key != "MAKEFILE_LIST")
        compiled_dependencies = set()
        for index in range(len(sources)):
            emitted = (out / "objects" / f"{index}.d").read_text()
            compiled_dependencies.update((root / name).resolve() for name in
                shlex.split(emitted.replace("\\\n", " ").split(":", 1)[1]))
        if before != after or not same_config or not compiled_dependencies.issubset(inputs):
            record["changed_inputs"] = sorted(path for path in before if before[path] != after[path])
            raise RuntimeError("build inputs or discovered dependency closure changed while compiling")
        staged = {}
        for relative, source in staged_libraries:
            destination = out / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, destination)
            source_hash = before[str(source)]
            staged_hash = digest(destination)
            if source_hash != staged_hash:
                raise RuntimeError(f"staged runtime library differs: {relative}")
            staged[str(relative)] = {"source": str(source), "sha256": staged_hash}
        record.update(status="passed", qualified=True, binary=str(binary), binary_sha256=digest(binary),
                      runtime_libraries=staged,
                      link_command=link, build_seconds=round(time.monotonic() - started, 6),
                      compiler_version=run([compiler, "--version"]).splitlines()[0])
        print(f"Private CeTTa build: {len(sources)} translation units, {len(inputs)} pinned inputs", flush=True)
    except Exception as error:
        record.update(status="failed", error=str(error))
        raise
    finally:
        record["finished_at"] = datetime.now(timezone.utc).isoformat()
        save()


if __name__ == "__main__":
    main()
