#!/usr/bin/env python3
"""Run a source-bound pure streaming proof DAG across bounded processes.

This is an untrusted orchestration layer around the generic checker.  Every
worker receives the exact state emitted by its predecessor; the admitted GSLT
source rechecks every chunk, and the final worker reconstructs both conversion
goals before invoking the indexed LF kernel.  Any parsing or transport error in
this script therefore fails closed in a later checker invocation.
"""

from __future__ import annotations

import argparse
import hashlib
import subprocess
from pathlib import Path


STREAM_PLACEHOLDER = "__GIC_PURE_STREAM_STATE__"
TERM_PLACEHOLDER = "__GIC_PURE_TERM_STATE__"
TYPE_PLACEHOLDER = "__GIC_PURE_TYPE_STATE__"
INITIAL_STATE = "(GICPureStreamState 0 DEnvNil)"
STREAM_PREFIX = "[(GICPureStreamOK "
STREAM_SUFFIX = ")]"
STREAM_FAILURE_LINES = {"[GICPureStreamFail]", "GICPureStreamFail"}


def read_manifest(path: Path) -> dict[str, str]:
    fields: dict[str, str] = {}
    for number, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not raw:
            continue
        if "\t" not in raw:
            raise ValueError(f"{path.name}:{number}: missing tab separator")
        key, value = raw.split("\t", 1)
        if not key or key in fields:
            raise ValueError(f"{path.name}:{number}: invalid or duplicate key")
        fields[key] = value
    required = {
        "schema",
        "entry_index",
        "term_chunk_count",
        "type_chunk_count",
        "expected_summary",
    }
    missing = sorted(required.difference(fields))
    if missing:
        raise ValueError(f"{path.name}: missing fields: {', '.join(missing)}")
    if fields["schema"] != "gic-pure-process-bundle-v1":
        raise ValueError(f"{path.name}: unsupported schema")
    return fields


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def snapshot(paths: list[Path]) -> dict[Path, str]:
    return {path: file_sha256(path) for path in paths}


def require_unchanged(expected: dict[Path, str]) -> None:
    changed = [
        path.name
        for path, digest in expected.items()
        if not path.is_file() or file_sha256(path) != digest
    ]
    if changed:
        raise RuntimeError("bundle changed during replay: " + ", ".join(changed))


def replace_once(template: str, placeholder: str, value: str) -> str:
    count = template.count(placeholder)
    if count != 1:
        raise ValueError(f"expected one {placeholder}, found {count}")
    return template.replace(placeholder, value)


def balanced_state(state: str) -> bool:
    if not state.startswith("(GICPureStreamState ") or not state.endswith(")"):
        return False
    depth = 0
    quoted = False
    escaped = False
    for character in state:
        if escaped:
            escaped = False
        elif quoted and character == "\\":
            escaped = True
        elif character == '"':
            quoted = not quoted
        elif not quoted and character == "(":
            depth += 1
        elif not quoted and character == ")":
            depth -= 1
            if depth < 0:
                return False
    return depth == 0 and not quoted and not escaped


def run_worker(
    cetta: str,
    run_directory: Path,
    stem: str,
    source: str,
) -> list[str]:
    run_path = run_directory / f"{stem}.run.metta"
    stdout_path = run_directory / f"{stem}.stdout.log"
    stderr_path = run_directory / f"{stem}.stderr.log"
    run_path.write_text(source, encoding="utf-8")
    completed = subprocess.run(
        [
            cetta,
            "--quiet",
            "--import-mode",
            "ancestor-walk",
            run_path.name,
        ],
        cwd=run_directory,
        text=True,
        capture_output=True,
        check=False,
    )
    stdout_path.write_text(completed.stdout, encoding="utf-8")
    stderr_path.write_text(completed.stderr, encoding="utf-8")
    if completed.returncode != 0:
        raise RuntimeError(
            f"{stem}: CeTTa exited {completed.returncode}; see {stderr_path.name}"
        )
    combined = completed.stdout + "\n" + completed.stderr
    if "Error" in combined or "❌" in combined:
        raise RuntimeError(f"{stem}: checker reported failure")
    lines = [line.strip() for line in completed.stdout.splitlines() if line.strip()]
    if any(line in STREAM_FAILURE_LINES for line in lines):
        raise RuntimeError(f"{stem}: checker reported failure")
    return lines


def extract_stream_state(lines: list[str], stem: str) -> str:
    matches = [
        line
        for line in lines
        if line.startswith(STREAM_PREFIX) and line.endswith(STREAM_SUFFIX)
    ]
    if len(matches) != 1:
        raise RuntimeError(
            f"{stem}: expected one pure-stream success, found {len(matches)}"
        )
    state = matches[0][len(STREAM_PREFIX) : -len(STREAM_SUFFIX)]
    if not balanced_state(state):
        raise RuntimeError(f"{stem}: malformed returned stream state")
    return state


def run_chain(
    cetta: str,
    run_directory: Path,
    kind: str,
    templates: list[Path],
    transport_snapshot: dict[Path, str],
) -> str:
    state = INITIAL_STATE
    for index, template_path in enumerate(templates):
        require_unchanged(transport_snapshot)
        template = template_path.read_text(encoding="utf-8")
        source = replace_once(template, STREAM_PLACEHOLDER, state)
        stem = f"{kind}_{index:03d}"
        state = extract_stream_state(
            run_worker(cetta, run_directory, stem, source), stem
        )
    return state


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("bundle_directory", type=Path)
    parser.add_argument("--cetta", default="cetta")
    parser.add_argument("--run-directory", type=Path)
    arguments = parser.parse_args()

    bundle = arguments.bundle_directory.resolve()
    manifest_path = bundle / "manifest.tsv"
    common_path = bundle / "common.metta"
    final_path = bundle / "final.template.metta"
    manifest = read_manifest(manifest_path)

    term_templates = sorted(bundle.glob("term_chunk_*.template.metta"))
    type_templates = sorted(bundle.glob("type_chunk_*.template.metta"))
    expected_term = int(manifest["term_chunk_count"])
    expected_type = int(manifest["type_chunk_count"])
    if len(term_templates) != expected_term:
        raise ValueError(
            f"expected {expected_term} term chunks, found {len(term_templates)}"
        )
    if len(type_templates) != expected_type:
        raise ValueError(
            f"expected {expected_type} type chunks, found {len(type_templates)}"
        )
    required_paths = [
        manifest_path,
        common_path,
        final_path,
        *term_templates,
        *type_templates,
    ]
    missing = [path.name for path in required_paths if not path.is_file()]
    if missing:
        raise FileNotFoundError("missing bundle files: " + ", ".join(missing))
    bundle_snapshot = snapshot(required_paths)

    run_directory = (
        arguments.run_directory.resolve()
        if arguments.run_directory
        else bundle / "runs"
    )
    run_directory.mkdir(parents=True, exist_ok=True)
    run_common_path = run_directory / "common.metta"
    if run_common_path.resolve() != common_path.resolve():
        run_common_path.write_bytes(common_path.read_bytes())
    transport_snapshot = dict(bundle_snapshot)
    transport_snapshot[run_common_path] = file_sha256(common_path)

    term_state = run_chain(
        arguments.cetta,
        run_directory,
        "term",
        term_templates,
        transport_snapshot,
    )
    type_state = run_chain(
        arguments.cetta,
        run_directory,
        "type",
        type_templates,
        transport_snapshot,
    )
    require_unchanged(transport_snapshot)

    final_source = final_path.read_text(encoding="utf-8")
    final_source = replace_once(final_source, TERM_PLACEHOLDER, term_state)
    final_source = replace_once(final_source, TYPE_PLACEHOLDER, type_state)
    final_lines = run_worker(
        arguments.cetta, run_directory, "final", final_source
    )
    expected_summary = manifest["expected_summary"]
    if final_lines.count(expected_summary) != 1:
        raise RuntimeError("final source-bound kernel summary absent or duplicated")
    require_unchanged(transport_snapshot)

    (run_directory / "term_state_final.metta").write_text(
        term_state + "\n", encoding="utf-8"
    )
    (run_directory / "type_state_final.metta").write_text(
        type_state + "\n", encoding="utf-8"
    )
    digest_lines = [
        f"{digest}\t{path.relative_to(bundle)}"
        for path, digest in sorted(
            bundle_snapshot.items(), key=lambda item: str(item[0])
        )
    ]
    (run_directory / "bundle_sha256.tsv").write_text(
        "\n".join(digest_lines) + "\n", encoding="utf-8"
    )
    (run_directory / "summary.tsv").write_text(
        "schema\tgic-pure-process-replay-v1\n"
        f"entry_index\t{manifest['entry_index']}\n"
        f"term_chunks\t{len(term_templates)}\n"
        f"type_chunks\t{len(type_templates)}\n"
        "status\tPASS\n",
        encoding="utf-8",
    )
    print(
        "PURE STREAMING PROCESS BUNDLE: PASS "
        f"(entry {manifest['entry_index']}; "
        f"{len(term_templates)} term chunks; "
        f"{len(type_templates)} type chunks)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
