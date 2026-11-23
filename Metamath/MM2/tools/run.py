#!/usr/bin/env python3
"""Run the fixed MM2 verifier with native translation or passive source data."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

from assemble import load_verifier, write_atomic
from mm2_atoms import atom_digest, parse_atoms
from protocol import observe_result, validate_passive_data


def file_sha256(path: str | Path) -> str:
    digest = hashlib.sha256()
    with Path(path).open("rb") as source:
        for chunk in iter(lambda: source.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def executable(path: str | Path) -> Path:
    located = shutil.which(str(path))
    if located is None:
        raise ValueError(f"Executable not found or not executable: {path}")
    return Path(located).resolve()


def performed_steps(stdout: str) -> int | None:
    matches = re.findall(r"^executing ([0-9]+) steps took ", stdout, re.MULTILINE)
    return int(matches[0]) if len(matches) == 1 else None


def translator_identity(translator: Path, timeout: float) -> dict:
    reply = subprocess.run([str(translator), "--identity"], capture_output=True, text=True, timeout=timeout)
    if reply.returncode:
        raise ValueError("Translator identity query failed")
    identity = json.loads(reply.stdout)
    if not isinstance(identity, dict) or identity.get("schema") != "mm2-source-data-v1" or identity.get("profile") != "zar" or identity.get("version") != "1":
        raise ValueError("Translator identity does not match mm2-source-data-v1 / zar / version 1")
    return identity


def run_case(*, input_path: str | Path | None = None, data_path: str | Path | None = None,
             translator: str | Path | None = None, mork: str | Path,
             work_dir: str | Path, steps: int = 1000000, timeout: float = 300.0,
             manifest: str | Path | None = None, owner: str = "metamath-test-unit",
             root_name: str = "unit.mm", profile: str = "zar") -> dict:
    """Return one of accepted, rejected, incomplete-proof, execution-failure.

    Native tool failures, timeouts, exhausted budgets, and missing completion
    never count as mathematical rejection. Artifacts use a fresh run directory
    so stale result files cannot provide a terminal observation.

    Pretranslated data must be trusted translator output or a separately
    qualified artifact. Its shape is checked; source recomputation is not.
    """
    started = time.monotonic()
    result: dict = {
        "schema": "mm2-run-receipt-v1", "outcome": "execution-failure",
        "detail": "Execution did not reach an outcome", "steps_ifparsed": None,
        "step_limit": steps, "profile": profile, "owner": owner,
    }
    run_directory: Path | None = None
    native_phase = "native tool"
    log_stem = "native"

    def finish(outcome: str, detail: str) -> dict:
        result.update(outcome=outcome, detail=detail, elapsed=time.monotonic() - started)
        if run_directory is not None:
            write_atomic(run_directory / "receipt.json", json.dumps(result, indent=2) + "\n")
        return result

    try:
        if (input_path is None) == (data_path is None):
            raise ValueError("Exactly one input_path or data_path is required")
        result["input_kind"] = "native-source" if input_path is not None else "structurally-checked-data"
        if steps <= 0 or timeout <= 0:
            raise ValueError("Step limit and timeout must be positive")
        if profile != "zar":
            raise ValueError("This verifier manifest supports the zar profile")
        assembly = load_verifier() if manifest is None else load_verifier(manifest)
        result["verifier_parsed_sha256"] = assembly.manifest["parsed_sha256"]
        work = Path(work_dir).resolve()
        work.mkdir(parents=True, exist_ok=True)
        run_directory = Path(tempfile.mkdtemp(prefix="run-", dir=work))
        result["artifacts"] = {name: str(run_directory / name) for name in (
            "source-data.mm2", "program.mm2", "result.mm2", "translator.stdout",
            "translator.stderr", "mork.stdout", "mork.stderr", "receipt.json")}
        mork_path = executable(mork)
        result["mork_sha256"] = file_sha256(mork_path)
        passive_path = run_directory / "source-data.mm2"
        if input_path is not None:
            if translator is None:
                raise ValueError("Native source input requires a translator executable")
            translate_path = executable(translator)
            result["translator_sha256"] = file_sha256(translate_path)
            native_phase, log_stem = "Translator identity query", "translator-identity"
            result["translator_identity"] = translator_identity(translate_path, timeout)
            source_path = Path(input_path).resolve()
            result["input_sha256"] = file_sha256(source_path)
            command = [str(translate_path), str(source_path), "--output", str(passive_path),
                       "--profile", profile, "--owner", owner, "--root-name", root_name]
            native_phase, log_stem = "Translator", "translator"
            reply = subprocess.run(command, capture_output=True, text=True, timeout=timeout)
            write_atomic(run_directory / "translator.stdout", reply.stdout)
            write_atomic(run_directory / "translator.stderr", reply.stderr)
            result["translator_exit"] = reply.returncode
            if reply.returncode == 1:
                if passive_path.exists():
                    return finish("execution-failure", "Translator rejected source but left a passive output")
                return finish("rejected", "Native frontend rejected malformed or structurally invalid source: " + reply.stderr.strip())
            if reply.returncode:
                return finish("execution-failure", "Native translator failed: " + reply.stderr.strip())
            passive = passive_path.read_text(encoding="utf-8")
        else:
            passive = Path(data_path).read_text(encoding="utf-8")
            write_atomic(passive_path, passive)
        data_atoms = parse_atoms(passive)
        source = validate_passive_data(data_atoms, owner=owner)
        result["data_parsed_sha256"] = atom_digest(data_atoms)
        result["source_statements"] = source.end
        result["source_theorems"] = len(source.theorem_positions)
        write_atomic(run_directory / "program.mm2", assembly.text + passive.rstrip("\n") + "\n")
        command = [str(mork_path), "run", "--steps", str(steps), "--instrumentation", "0",
                   str(run_directory / "program.mm2"), str(run_directory / "result.mm2")]
        native_phase, log_stem = "MORK", "mork"
        reply = subprocess.run(command, capture_output=True, text=True, timeout=timeout)
        write_atomic(run_directory / "mork.stdout", reply.stdout)
        write_atomic(run_directory / "mork.stderr", reply.stderr)
        result["mork_exit"] = reply.returncode
        if reply.returncode:
            return finish("execution-failure", "MORK failed: " + reply.stderr.strip())
        performed = performed_steps(reply.stdout)
        result["steps_ifparsed"] = performed
        if performed is None:
            return finish("execution-failure", "MORK did not report a unique executed-step count")
        if performed >= steps:
            return finish("execution-failure", "MORK exhausted the step budget; no rejection is inferred")
        observation = observe_result(parse_atoms((run_directory / "result.mm2").read_text(encoding="utf-8")), source)
        result.update(observation)
        return finish(observation["outcome"], observation["detail"])
    except subprocess.TimeoutExpired as error:
        def text_output(value: str | bytes | None) -> str:
            return value.decode("utf-8", errors="replace") if isinstance(value, bytes) else value or ""

        if run_directory is not None:
            for suffix, partial in (("stdout", error.stdout), ("stderr", error.stderr)):
                name = f"{log_stem}.{suffix}"
                path = run_directory / name
                write_atomic(path, text_output(partial))
                result["artifacts"][name] = str(path)
        result["timeout_phase"] = native_phase
        return finish("execution-failure", f"{native_phase} exceeded the timeout; no rejection is inferred")
    except (OSError, ValueError, TypeError, KeyError, IndexError) as error:
        return finish("execution-failure", str(error))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    inputs = parser.add_mutually_exclusive_group(required=True)
    inputs.add_argument("--input", type=Path, help="Metamath source for native translation")
    inputs.add_argument("--data", type=Path, help="Trusted native-B or prequalified mm2-source-data-v1; only structure is checked here")
    parser.add_argument("--translator", type=Path)
    parser.add_argument("--mork", type=Path, required=True)
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--steps", type=int, default=1000000)
    parser.add_argument("--timeout", type=float, default=300.0)
    parser.add_argument("--profile", default="zar")
    parser.add_argument("--owner", default="metamath-test-unit")
    parser.add_argument("--root-name", default="unit.mm")
    args = parser.parse_args(argv)
    result = run_case(input_path=args.input, data_path=args.data, translator=args.translator,
                      mork=args.mork, work_dir=args.work_dir, manifest=args.manifest,
                      steps=args.steps, timeout=args.timeout, profile=args.profile,
                      owner=args.owner, root_name=args.root_name)
    print(json.dumps(result, sort_keys=True))
    return {"accepted": 0, "incomplete-proof": 0, "rejected": 1, "execution-failure": 2}[result["outcome"]]


if __name__ == "__main__":
    raise SystemExit(main())
