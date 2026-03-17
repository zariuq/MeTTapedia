#!/usr/bin/env python3
"""
Simple runtime performance gate against PeTTa baseline on heavy subset.

Gate:
- Lean simple runtime (`simpleMeTTa run --dialect petta --json`) median time
  must be <= max_ratio * PeTTa median time over measured files.
- Both engines must succeed for all measured files.
"""

from __future__ import annotations

import argparse
import json
import statistics
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


def list_metta_files(path: Path) -> list[Path]:
    if path.is_file():
        return [path]
    if not path.exists():
        raise FileNotFoundError(f"subset path does not exist: {path}")
    files = sorted(p for p in path.rglob("*.metta") if p.is_file())
    if not files:
        raise ValueError(f"no .metta files found under subset path: {path}")
    return files


def first_json_object(stdout: str) -> dict[str, Any]:
    for ln in reversed(stdout.splitlines()):
        s = ln.strip()
        if s.startswith("{") and s.endswith("}"):
            payload = json.loads(s)
            if isinstance(payload, dict):
                return payload
    raise ValueError("no JSON object found in Lean stdout")


def run_lean_once(
    algorithms_root: Path, file_path: Path, timeout_sec: int
) -> tuple[float, bool, str, str]:
    cmd = f"lake exe simpleMeTTa run --dialect petta --json {file_path}"
    t0 = time.perf_counter()
    try:
        proc = subprocess.run(
            ["bash", "-lc", cmd],
            cwd=algorithms_root,
            capture_output=True,
            text=True,
            timeout=timeout_sec,
        )
        elapsed_ms = (time.perf_counter() - t0) * 1000.0
        ok = False
        if proc.returncode == 0:
            try:
                payload = first_json_object(proc.stdout)
                diagnostics = payload.get("diagnostics", {})
                errors = diagnostics.get("errors", 1) if isinstance(diagnostics, dict) else 1
                ok = isinstance(errors, int) and errors == 0
            except Exception:  # noqa: BLE001
                ok = False
        return elapsed_ms, ok, proc.stdout, proc.stderr
    except subprocess.TimeoutExpired as exc:
        elapsed_ms = (time.perf_counter() - t0) * 1000.0
        stdout = exc.stdout if isinstance(exc.stdout, str) else ""
        stderr = exc.stderr if isinstance(exc.stderr, str) else ""
        return elapsed_ms, False, stdout, f"timeout after {timeout_sec}s\n{stderr}"


def run_petta_once(
    petta_root: Path, file_path: Path, timeout_sec: int
) -> tuple[float, bool, str, str]:
    cmd = f"./run.sh {file_path} --silent"
    t0 = time.perf_counter()
    try:
        proc = subprocess.run(
            ["bash", "-lc", cmd],
            cwd=petta_root,
            capture_output=True,
            text=True,
            timeout=timeout_sec,
        )
        elapsed_ms = (time.perf_counter() - t0) * 1000.0
        return elapsed_ms, proc.returncode == 0, proc.stdout, proc.stderr
    except subprocess.TimeoutExpired as exc:
        elapsed_ms = (time.perf_counter() - t0) * 1000.0
        stdout = exc.stdout if isinstance(exc.stdout, str) else ""
        stderr = exc.stderr if isinstance(exc.stderr, str) else ""
        return elapsed_ms, False, stdout, f"timeout after {timeout_sec}s\n{stderr}"


def main() -> int:
    parser = argparse.ArgumentParser(description="Check Lean simple runtime perf gate (<=10x).")
    parser.add_argument(
        "--algorithms-root",
        default="../algorithms",
        help="Path to algorithms repo root",
    )
    parser.add_argument(
        "--petta-root",
        default="../../hyperon/PeTTa",
        help="Path to PeTTa root containing run.sh",
    )
    parser.add_argument(
        "--subset",
        default="../algorithms/artifacts/strict_subset_heavy",
        help="Heavy subset file or directory (.metta files)",
    )
    parser.add_argument(
        "--repeats",
        type=int,
        default=1,
        help="Runs per file per engine (default: 1)",
    )
    parser.add_argument(
        "--max-ratio",
        type=float,
        default=10.0,
        help="Gate threshold for median ratio Lean/PeTTa",
    )
    parser.add_argument(
        "--timeout-sec",
        type=int,
        default=60,
        help="Per-run timeout in seconds for each engine",
    )
    parser.add_argument(
        "--report",
        default="artifacts/conformance/simple_runtime_perf_gate_latest.json",
        help="Path to write JSON report",
    )
    args = parser.parse_args()

    root = Path(__file__).resolve().parents[2]
    algorithms_root = (root / args.algorithms_root).resolve()
    petta_root = (root / args.petta_root).resolve()
    subset_path = (root / args.subset).resolve()
    report_path = root / args.report

    if args.repeats <= 0:
        raise ValueError("--repeats must be >= 1")
    if args.timeout_sec <= 0:
        raise ValueError("--timeout-sec must be >= 1")
    has_lakefile = (algorithms_root / "lakefile.lean").exists() or (
        algorithms_root / "lakefile.toml"
    ).exists()
    if not has_lakefile:
        raise FileNotFoundError(f"invalid algorithms root: {algorithms_root}")
    if not (petta_root / "run.sh").exists():
        raise FileNotFoundError(f"missing PeTTa runner: {petta_root / 'run.sh'}")

    files = list_metta_files(subset_path)
    rows: list[dict[str, Any]] = []
    lean_fail = 0
    petta_fail = 0
    ratios: list[float] = []

    print(
        f"perf gate: files={len(files)} repeats={args.repeats} "
        f"max_ratio={args.max_ratio}"
        f" timeout_sec={args.timeout_sec}",
        flush=True,
    )
    for file_path in files:
        lean_times: list[float] = []
        petta_times: list[float] = []
        lean_ok_all = True
        petta_ok_all = True
        lean_last_stdout = ""
        lean_last_stderr = ""
        petta_last_stdout = ""
        petta_last_stderr = ""
        for _ in range(args.repeats):
            lean_ms, lean_ok, lean_stdout, lean_stderr = run_lean_once(
                algorithms_root, file_path, args.timeout_sec
            )
            petta_ms, petta_ok, petta_stdout, petta_stderr = run_petta_once(
                petta_root, file_path, args.timeout_sec
            )
            lean_times.append(lean_ms)
            petta_times.append(petta_ms)
            lean_ok_all = lean_ok_all and lean_ok
            petta_ok_all = petta_ok_all and petta_ok
            lean_last_stdout = lean_stdout
            lean_last_stderr = lean_stderr
            petta_last_stdout = petta_stdout
            petta_last_stderr = petta_stderr

        lean_med = statistics.median(lean_times)
        petta_med = statistics.median(petta_times)
        ratio = lean_med / max(petta_med, 1.0)
        ratios.append(ratio)
        if not lean_ok_all:
            lean_fail += 1
        if not petta_ok_all:
            petta_fail += 1
        rel = str(file_path.relative_to(subset_path.parent))
        print(
            f"[{rel}] lean_med_ms={lean_med:.2f} petta_med_ms={petta_med:.2f} "
            f"ratio={ratio:.4f} lean_ok={lean_ok_all} petta_ok={petta_ok_all}"
            ,
            flush=True,
        )
        rows.append(
            {
                "file": str(file_path),
                "relative": rel,
                "lean_median_ms": lean_med,
                "petta_median_ms": petta_med,
                "ratio": ratio,
                "lean_ok": lean_ok_all,
                "petta_ok": petta_ok_all,
                "lean_stdout": lean_last_stdout,
                "lean_stderr": lean_last_stderr,
                "petta_stdout": petta_last_stdout,
                "petta_stderr": petta_last_stderr,
            }
        )

    overall_ratio = statistics.median(ratios) if ratios else float("inf")
    ok = lean_fail == 0 and petta_fail == 0 and overall_ratio <= args.max_ratio
    print(
        "perf gate summary: "
        f"files={len(files)} lean_fail={lean_fail} petta_fail={petta_fail} "
        f"median_ratio={overall_ratio:.4f} threshold={args.max_ratio} status={'PASS' if ok else 'FAIL'}"
        ,
        flush=True,
    )

    payload = {
        "suite": "simple_runtime_perf_gate",
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "algorithms_root": str(algorithms_root),
        "petta_root": str(petta_root),
        "subset": str(subset_path),
        "repeats": args.repeats,
        "max_ratio": args.max_ratio,
        "median_ratio": overall_ratio,
        "lean_fail": lean_fail,
        "petta_fail": petta_fail,
        "status": "pass" if ok else "fail",
        "rows": rows,
    }
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(json.dumps(payload, ensure_ascii=True, indent=2) + "\n", encoding="utf-8")
    print(f"report: {report_path}", flush=True)
    return 0 if ok else 3


if __name__ == "__main__":
    sys.exit(main())
