#!/usr/bin/env python3
"""Capture a Lean import closure for isolated source checks.

Run under the intended Lake environment or select its Lean with --lean. The
manifest records the pinned binary, copied artifacts, input sources, and any
requested Lake freshness check.
Run rechecks with the recorded Lean binary and LEAN_SYSROOT, LEAN_PATH set to
the snapshot's objects directory, and --root set to the recorded copied root.
Use --workspace-root to preserve known source-relative literal file reads.
Pass other inputs explicitly with --elaboration-input. Native plugins and custom
module setups need separate capture.
"""

import argparse
from collections import defaultdict
from datetime import datetime, timezone
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
from tempfile import TemporaryDirectory


FILE_TRIVIA = (
    r'(?P<comment>/-)|--[^\n]*|r(?P<hashes>#+)".*?"(?P=hashes)|«[^»]*»|'
    r"""'(?:[^'\\\n]|\\.)'|"""
)
STRING_LITERAL = r'"(?:[^"\\\n]|\\.)*"'
OTHER_STRING = r'"(?:[^"\\]|\\.)*"'
FILE_READ_TOKEN = re.compile(
    FILE_TRIVIA +
    r'(?<![\w.])(?:(?P<tree>#module_tree)|#module_file|petta_source_file%|'
    r'parser_(?:pack_text|snapshot_grammar)_file%|'
    r'metta_sexpr_(?:(?:pinned|program|commands|command_chunks|lines)_)?file%\s+(?:petta|he)|'
    r'include_str|include_bytes)'
    r'\s+(?P<path>' + STRING_LITERAL + r')|' + OTHER_STRING,
    re.DOTALL,
)
MODULE_IMPORT_TOKEN = re.compile(
    FILE_TRIVIA +
    r'(?<![\w.])import\s+(?P<path>' + STRING_LITERAL + r')\s+as\b|'
    r'(?P<body>\bModule\b)|' + OTHER_STRING,
    re.DOTALL,
)
BLOCK_COMMENT_MARKER = re.compile(r"/-|-/")


def file_tokens(text, pattern):
    """Skip nested block comments before considering a file-form token."""
    offset = 0
    while match := pattern.search(text, offset):
        offset = match.end()
        if match["comment"]:
            depth = 1
            for marker in BLOCK_COMMENT_MARKER.finditer(text, offset):
                depth += 1 if marker[0] == "/-" else -1
                if depth == 0:
                    offset = marker.end()
                    break
            else:
                return
        else:
            yield match


def literal_path(literal, directory):
    try:
        spelling = Path(json.loads(literal))
    except json.JSONDecodeError:
        # Other Lean string escapes can be captured explicitly.
        return None
    if not spelling.is_absolute():
        return Path(os.path.abspath(directory / spelling))
    return None


def module_tree_inputs(root, workspace_root):
    """Follow the ModuleSource import prelude relative to the loaded file."""
    visited = set()
    pending = [root]
    while pending:
        path = pending.pop()
        resolved = path.resolve(strict=True)
        if workspace_root is not None and not resolved.is_relative_to(workspace_root):
            raise ValueError(f"module input is outside the workspace root: {path}")
        yield path
        if resolved in visited:
            continue
        visited.add(resolved)
        if resolved != path:
            yield resolved
        children = []
        for match in file_tokens(resolved.read_text(), MODULE_IMPORT_TOKEN):
            if match["body"]:
                break
            if match["path"] and (child := literal_path(match["path"], resolved.parent)) is not None:
                children.append(child)
        pending.extend(reversed(children))


def literal_elaboration_inputs(source, workspace_root=None, *, text=None):
    """Recognize source-relative file forms outside comments and strings."""
    seen = set()
    for match in file_tokens(source.read_text() if text is None else text, FILE_READ_TOKEN):
        if not match["path"]:
            continue
        path = literal_path(match["path"], source.parent)
        if path is None or not path.is_file():
            continue
        paths = module_tree_inputs(path, workspace_root) if match["tree"] else [path]
        for included in paths:
            if included not in seen:
                seen.add(included)
                yield included


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


def import_graph(lean, helper, sources, env=None, source_only=()):
    bootstrap = dict(os.environ if env is None else env)
    payload = {"searchPath": bootstrap.pop("LEAN_PATH", ""),
               "sourceOnly": sorted(source_only),
               "sources": [os.fspath(source) for source in sources]}
    with TemporaryDirectory(prefix="lean-import-graph-") as temporary:
        request = Path(temporary) / "request.json"
        request.write_text(json.dumps(payload, ensure_ascii=False), encoding="utf-8")
        modules = json.loads(run_text([lean, "--run", helper, "--request", request], bootstrap))
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


def copy_artifacts(files, objects, *, link=False):
    mode = ["--link", "--dereference"] if link else ["--reflink=auto"]
    by_prefix = defaultdict(list)
    for relative, (prefix, identity) in files.items():
        if identity is not None:
            by_prefix[prefix].append(relative)
    for prefix, paths in sorted(by_prefix.items()):
        for start in range(0, len(paths), 256):
            batch = sorted(paths[start:start + 256])
            subprocess.run(
                ["cp", *mode, "--parents", "--", *batch, objects],
                cwd=prefix,
                check=True,
            )


def sealed_identity(status):
    # A new hard link changes ctime. The copied inode and content metadata
    # can still be checked against the sealed snapshot's receipt.
    return [status.st_dev, status.st_ino, status.st_size, status.st_mtime_ns]


def retained_imports(parent, files, device):
    root = parent.resolve(strict=True)
    objects = root / "objects"
    manifest = json.loads((root / "snapshot.json").read_text())
    retained = {}
    identities = {}
    sealed = manifest.get("sealed_artifacts", {})
    for entry in manifest["files"]:
        relative = Path(entry["path"])
        source = files.get(relative)
        copied = sealed.get(entry["path"])
        if source is None or source[1] is None or copied is None:
            continue
        if entry["identity"] != list(source[1]) and copied != list(source[1][:4]):
            continue
        old = objects / relative
        try:
            status = old.lstat()
        except FileNotFoundError:
            continue
        if (not stat.S_ISREG(status.st_mode) or status.st_mode & 0o222
                or status.st_dev != device or sealed_identity(status) != copied
                or not old.resolve().is_relative_to(objects)):
            continue
        retained[relative] = (objects, source[1])
        identities[relative] = copied
    return retained, identities


def capture(args):
    cwd = Path.cwd()
    sources = [file.resolve(strict=True) for file in args.sources]
    output = args.output.resolve()
    helper = Path(__file__).with_name("lean_import_graph.lean").resolve()
    prefix = Path(run_text([args.lean, "--print-prefix"])).resolve(strict=True)
    lean = prefix / "bin" / "lean"
    lean_env = {**os.environ, "LEAN_SYSROOT": str(prefix)}
    source_root = args.source_root.resolve(strict=True) if args.source_root else cwd
    if not source_root.is_dir():
        raise ValueError(f"source root is not a directory: {source_root}")
    if args.source_root:
        for path in sources:
            if not path.is_relative_to(source_root):
                raise ValueError(f"source is outside the specified root: {path}")
    source_only = set(args.from_source)
    if source_only:
        named_sources = set()
        for path in sources:
            root = source_root if path.is_relative_to(source_root) else path.parent
            named_sources.add(".".join(path.relative_to(root).with_suffix("").parts))
        if missing := source_only - named_sources:
            raise ValueError(f"missing source for --from-source: {', '.join(sorted(missing))}")
    workspace_root = args.workspace_root.resolve(strict=True) if args.workspace_root else None
    initial_inputs = {path: stamp(path) for path in sources}
    elaboration_inputs = {Path(os.path.abspath(path)) for path in args.elaboration_input}
    if elaboration_inputs and workspace_root is None:
        raise ValueError("--elaboration-input requires --workspace-root")
    if workspace_root is not None:
        for source in sources:
            elaboration_inputs.update(literal_elaboration_inputs(source, workspace_root))
        elaboration_inputs.update(path.resolve(strict=True) for path in tuple(elaboration_inputs))
        for path in [source_root, *sources, *elaboration_inputs]:
            if not path.is_relative_to(workspace_root) or not path.resolve().is_relative_to(workspace_root):
                raise ValueError(f"input is outside the workspace root: {path}")
    elaboration_inputs = sorted(elaboration_inputs)
    for path in elaboration_inputs:
        if not path.is_file():
            raise FileNotFoundError(f"missing elaboration input: {path}")
    initial_inputs.update({path: stamp(path) for path in elaboration_inputs})
    input_links = {path: path.resolve(strict=True) for path in elaboration_inputs
                   if path.resolve(strict=True) != path}
    package_files = [
        path for name in ("lean-toolchain", "lakefile.lean", "lakefile.toml", "lake-manifest.json")
        if (path := cwd / name).is_file()
    ]
    package_digests = {
        path.relative_to(cwd).as_posix(): contents_digest(path) for path in package_files
    }
    modules = import_graph(lean, helper, sources, lean_env, source_only)
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
    retained, copied_identities = {}, {}
    if args.reuse_imports is not None:
        retained, copied_identities = retained_imports(args.reuse_imports, files, objects.stat().st_dev)
    fresh = files
    if retained:
        fresh = {relative: item for relative, item in files.items() if relative not in retained}
    copy_artifacts(fresh, objects)
    copy_artifacts(retained, objects, link=True)
    if args.seal_imports or args.reuse_imports is not None:
        for relative, (_, identity) in fresh.items():
            if identity is not None:
                artifact = objects / relative
                artifact.chmod(artifact.stat().st_mode & ~0o222)
                copied_identities[relative] = sealed_identity(artifact.stat())
    source_area = output / "sources"
    recorded_sources = []
    for index, path in enumerate(sources):
        root = source_root if path.is_relative_to(source_root) else path.parent
        copied_root = (source_area / root.relative_to(workspace_root) if workspace_root is not None
                       else source_area / f"{index:03d}")
        saved = copied_root / path.relative_to(root)
        saved.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, saved)
        recorded_sources.append({
            "source": str(path), "copy": str(saved.relative_to(output)),
            "root": str(copied_root.relative_to(output)),
            "sha256": contents_digest(saved),
        })
    recorded_inputs = []
    for path in elaboration_inputs:
        if path in input_links:
            continue
        saved = source_area / path.relative_to(workspace_root)
        saved.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, saved)
    for path, target in input_links.items():
        saved = source_area / path.relative_to(workspace_root)
        saved.parent.mkdir(parents=True, exist_ok=True)
        saved.symlink_to(os.path.relpath(source_area / target.relative_to(workspace_root), saved.parent))
    for path in elaboration_inputs:
        saved = source_area / path.relative_to(workspace_root)
        record = {
            "source": str(path), "copy": str(saved.relative_to(output)),
            "sha256": contents_digest(saved),
        }
        if path in input_links:
            record["link"] = os.readlink(saved)
        recorded_inputs.append(record)
    for relative, (directory, identity) in files.items():
        path = directory / relative
        observed = stamp(path)
        if observed == identity:
            continue
        # Linking from the sealed copy itself changes its ctime.
        resident = copied_identities.get(relative)
        if (relative in retained and observed is not None and identity is not None
                and resident == list(identity[:4]) == list(observed[:4])
                and not path.stat().st_mode & 0o222):
            continue
        raise RuntimeError(f"compiled import changed during capture: {path}")
    for path, target in input_links.items():
        if path.resolve(strict=True) != target:
            raise RuntimeError(f"elaboration input target changed during capture: {path}")
    for path, identity in initial_inputs.items():
        if stamp(path) != identity:
            raise RuntimeError(f"input changed during capture: {path}")
    for path in package_files:
        if contents_digest(path) != package_digests[path.relative_to(cwd).as_posix()]:
            raise RuntimeError(f"package configuration changed during capture: {path}")
    if import_graph(lean, helper, sources, lean_env, source_only) != modules:
        raise RuntimeError("live import resolution changed during capture")

    frozen_env = {**lean_env, "LEAN_PATH": str(objects)}
    frozen_sources = [output / record["copy"] for record in recorded_sources]
    frozen = import_graph(lean, helper, frozen_sources, frozen_env, source_only)
    if len(frozen) != len(modules):
        raise RuntimeError("the frozen dependency closure has a different size")
    for recorded, actual in zip(modules, frozen, strict=True):
        if actual["object"] != str(objects / actual["relative"]):
            raise RuntimeError(f"compiled import resolved outside the snapshot: {actual['name']}")
        if {**actual, "object": recorded["object"]} != recorded:
            raise RuntimeError(f"compiled import header changed during capture: {actual['name']}")

    for relative, identity in copied_identities.items():
        status = (objects / relative).stat()
        if status.st_mode & 0o222 or sealed_identity(status) != identity:
            raise RuntimeError(f"sealed import changed during capture: {relative}")

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
    if recorded_inputs:
        manifest["elaboration_inputs"] = recorded_inputs
    if source_only:
        manifest["source_only_modules"] = sorted(source_only)
    if copied_identities:
        manifest["sealed_artifacts"] = {str(path): identity for path, identity in sorted(copied_identities.items())}
    if args.reuse_imports is not None:
        manifest["retained_imports"] = len(retained)
    (output / "snapshot.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Captured {len(modules)} modules and {len(manifest['files'])} artifact parts")
    if code is not None:
        print(f"Lake freshness check exit status {code}. See lake-freshness.log.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="new snapshot directory")
    parser.add_argument("sources", type=Path, nargs="+", help="Lean inputs to recheck")
    parser.add_argument("--lean", default="lean", metavar="EXECUTABLE",
                        help="Lean executable used to discover the pinned capture toolchain")
    parser.add_argument("--source-root", type=Path,
                        help="common Lean module root for the input sources")
    parser.add_argument("--from-source", action="append", default=[], metavar="MODULE",
                        help="capture this supplied module without its compiled artifacts")
    parser.add_argument("--workspace-root", type=Path,
                        help="preserve the directory layout relative to this root")
    parser.add_argument("--seal-imports", action="store_true",
                        help="make copied compiled imports read-only for shared rechecks")
    parser.add_argument("--reuse-imports", type=Path, metavar="SNAPSHOT",
                        help="link matching imports from a sealed snapshot and seal the remaining copies")
    parser.add_argument("--elaboration-input", type=Path, action="append", default=[],
                        help="file read by the source during elaboration, such as include_str")
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
