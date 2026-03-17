#!/usr/bin/env python3
"""
Run HE I/O conformance fixtures against Hyperon Experimental (metta 0.2.10).

Comparator policy:
- Bag equivalence (order-insensitive)
- Multiplicity-preserving (duplicates matter)

Optional parity mode:
- Compare Lean simple runtime HE output against Hyperon output on the same fixtures.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

APPLY_PREFIX = "MeTTailCore.MeTTaIL.Syntax.Pattern.apply"
FVAR_PREFIX = "MeTTailCore.MeTTaIL.Syntax.Pattern.fvar"
BVAR_PREFIX = "MeTTailCore.MeTTaIL.Syntax.Pattern.bvar"


def normalize_term(term: str) -> str:
    return re.sub(r"\s+", " ", term.strip())


def split_top_level_commas(payload: str) -> list[str]:
    parts: list[str] = []
    buf: list[str] = []
    paren = 0
    bracket = 0
    in_str = False
    esc = False
    for ch in payload:
        if in_str:
            buf.append(ch)
            if esc:
                esc = False
                continue
            if ch == "\\":
                esc = True
            elif ch == '"':
                in_str = False
            continue
        if ch == '"':
            in_str = True
            buf.append(ch)
            continue
        if ch == "(":
            paren += 1
            buf.append(ch)
            continue
        if ch == ")":
            paren -= 1
            buf.append(ch)
            continue
        if ch == "[":
            bracket += 1
            buf.append(ch)
            continue
        if ch == "]":
            bracket -= 1
            buf.append(ch)
            continue
        if ch == "," and paren == 0 and bracket == 0:
            token = "".join(buf).strip()
            if token:
                parts.append(token)
            buf = []
            continue
        buf.append(ch)
    tail = "".join(buf).strip()
    if tail:
        parts.append(tail)
    return parts


def parse_metta_result_line(raw_line: str) -> list[str]:
    line = raw_line.strip()
    if not (line.startswith("[") and line.endswith("]")):
        raise ValueError(f"expected bracketed MeTTa result line, got: {line!r}")
    inner = line[1:-1].strip()
    if inner == "":
        return []
    return [normalize_term(tok) for tok in split_top_level_commas(inner)]


def run_hyperon_case(
    project_root: Path,
    fixture_id: str,
    setup: list[str],
    query: str,
    env_name: str,
    scratch_dir: Path,
) -> tuple[int, str, str]:
    case_path = scratch_dir / f"{fixture_id}.metta"
    lines = list(setup) + [query]
    case_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    cmd = (
        "source ~/.bashrc && "
        f"conda run -n {env_name} metta {case_path}"
    )
    proc = subprocess.run(
        ["bash", "-lc", cmd],
        cwd=project_root,
        capture_output=True,
        text=True,
    )
    return proc.returncode, proc.stdout, proc.stderr


def run_lean_case(algorithms_root: Path, case_path: Path) -> tuple[int, str, str]:
    cmd = (
        "ulimit -v 6291456 && "
        f"lake exe simpleMeTTa he-run --json {case_path}"
    )
    proc = subprocess.run(
        ["bash", "-lc", cmd],
        cwd=algorithms_root,
        capture_output=True,
        text=True,
    )
    return proc.returncode, proc.stdout, proc.stderr


def first_result_line(stdout: str) -> str:
    for ln in stdout.splitlines():
        s = ln.strip()
        if s.startswith("[") and s.endswith("]"):
            return s
    raise ValueError("no bracketed result line found in stdout")


def first_json_object(stdout: str) -> dict[str, Any]:
    for ln in reversed(stdout.splitlines()):
        s = ln.strip()
        if s.startswith("{") and s.endswith("}"):
            payload = json.loads(s)
            if isinstance(payload, dict):
                return payload
    raise ValueError("no JSON object found in Lean stdout")


def metta_atom(head: str) -> str:
    if head == "()":
        return "()"
    if len(head) >= 2 and head[0] == '"' and head[-1] == '"':
        return head
    if re.search(r'[\s()\[\],"]', head):
        return json.dumps(head, ensure_ascii=False)
    return head


class LeanPatternReader:
    def __init__(self, text: str):
        self.text = text
        self.i = 0

    def peek(self) -> str:
        return self.text[self.i] if self.i < len(self.text) else ""

    def skip_ws(self) -> None:
        while self.i < len(self.text) and self.text[self.i].isspace():
            self.i += 1

    def consume(self, token: str) -> bool:
        if self.text.startswith(token, self.i):
            self.i += len(token)
            return True
        return False

    def expect(self, token: str) -> None:
        if not self.consume(token):
            raise ValueError(f"expected {token!r} at offset {self.i} in {self.text!r}")

    def read_quoted(self) -> str:
        self.skip_ws()
        if self.peek() != '"':
            raise ValueError(f"expected quoted string at offset {self.i} in {self.text!r}")
        self.i += 1
        out: list[str] = []
        esc = False
        while self.i < len(self.text):
            ch = self.text[self.i]
            self.i += 1
            if esc:
                mapping = {"n": "\n", "t": "\t", "r": "\r", '"': '"', "\\": "\\"}
                out.append(mapping.get(ch, ch))
                esc = False
                continue
            if ch == "\\":
                esc = True
                continue
            if ch == '"':
                return "".join(out)
            out.append(ch)
        raise ValueError("unterminated quoted string in Lean pattern repr")

    def read_nat(self) -> int:
        self.skip_ws()
        start = self.i
        while self.i < len(self.text) and self.text[self.i].isdigit():
            self.i += 1
        if self.i == start:
            raise ValueError(f"expected nat at offset {self.i} in {self.text!r}")
        return int(self.text[start:self.i])

    def read_pattern(self) -> tuple[str, Any]:
        self.skip_ws()
        if self.consume(APPLY_PREFIX):
            self.skip_ws()
            head = self.read_quoted()
            self.skip_ws()
            self.expect("[")
            args: list[tuple[str, Any]] = []
            self.skip_ws()
            if self.peek() != "]":
                while True:
                    args.append(self.read_pattern())
                    self.skip_ws()
                    if self.peek() == ",":
                        self.i += 1
                        continue
                    break
            self.skip_ws()
            self.expect("]")
            return ("apply", (head, args))
        if self.consume(FVAR_PREFIX):
            self.skip_ws()
            return ("fvar", self.read_quoted())
        if self.consume(BVAR_PREFIX):
            self.skip_ws()
            return ("bvar", self.read_nat())
        raise ValueError(
            f"unsupported Lean pattern constructor at offset {self.i} in {self.text!r}"
        )


def render_metta_term(node: tuple[str, Any]) -> str:
    tag, payload = node
    if tag == "apply":
        head, args = payload
        if head == "Expr":
            if not args:
                return "()"
            return "(" + " ".join(render_metta_term(a) for a in args) + ")"
        head_txt = metta_atom(head)
        if not args:
            return head_txt
        rendered_args = " ".join(render_metta_term(a) for a in args)
        return f"({head_txt} {rendered_args})"
    if tag == "fvar":
        return f"${payload}"
    if tag == "bvar":
        return f"${payload}"
    raise ValueError(f"unknown Lean pattern node tag: {tag}")


def parse_lean_result_atom(text: str) -> str:
    reader = LeanPatternReader(text)
    node = reader.read_pattern()
    reader.skip_ws()
    if reader.i != len(reader.text):
        raise ValueError(f"unparsed Lean pattern tail: {reader.text[reader.i:]!r}")
    return normalize_term(render_metta_term(node))


def parse_lean_results(stdout: str) -> list[str]:
    payload = first_json_object(stdout)
    queries = payload.get("queries", [])
    if not isinstance(queries, list) or not queries:
        return []
    last = queries[-1]
    if not isinstance(last, dict):
        return []
    results = last.get("results", [])
    if not isinstance(results, list):
        raise ValueError("Lean JSON queries[*].results must be a list")
    out: list[str] = []
    for raw in results:
        if not isinstance(raw, str):
            raise ValueError("Lean JSON query result must be a string repr")
        out.append(parse_lean_result_atom(raw))
    return out


def load_fixtures(path: Path) -> list[dict[str, Any]]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, list):
        raise ValueError("fixture file must be a JSON list")
    out: list[dict[str, Any]] = []
    for i, row in enumerate(data):
        if not isinstance(row, dict):
            raise ValueError(f"fixture index {i} is not an object")
        fid = row.get("id")
        setup = row.get("setup", [])
        query = row.get("query")
        expected = row.get("expected", [])
        if not isinstance(fid, str) or fid.strip() == "":
            raise ValueError(f"fixture index {i}: invalid id")
        if not isinstance(setup, list) or not all(isinstance(x, str) for x in setup):
            raise ValueError(f"fixture {fid}: setup must be list[str]")
        if not isinstance(query, str) or query.strip() == "":
            raise ValueError(f"fixture {fid}: invalid query")
        if not isinstance(expected, list) or not all(isinstance(x, str) for x in expected):
            raise ValueError(f"fixture {fid}: expected must be list[str]")
        out.append(
            {
                "id": fid,
                "tier": str(row.get("tier", "")).strip(),
                "lean_theorem": str(row.get("lean_theorem", "")).strip(),
                "implementation_priority": str(row.get("implementation_priority", "")).strip(),
                "implementation_group": str(row.get("implementation_group", "")).strip(),
                "setup": setup,
                "query": query,
                "expected": [normalize_term(x) for x in expected],
                "source_note": row.get("source_note", ""),
            }
        )
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description="Run HE I/O conformance (bag equivalence).")
    parser.add_argument(
        "--fixtures",
        default="scripts/conformance/he_io_fixtures.json",
        help="Path to HE I/O fixtures JSON",
    )
    parser.add_argument(
        "--results",
        default="artifacts/conformance/he_io_results_latest.jsonl",
        help="Path to write JSONL results",
    )
    parser.add_argument(
        "--conda-env",
        default="hyperon",
        help="Conda env containing `metta` binary (default: hyperon)",
    )
    parser.add_argument(
        "--scratch-dir",
        default="artifacts/conformance/he_io_cases",
        help="Directory for generated .metta case files",
    )
    parser.add_argument(
        "--compare-lean",
        action="store_true",
        help="Also run Lean simple runtime (he-run --json) and record parity vs Hyperon",
    )
    parser.add_argument(
        "--require-lean-parity",
        action="store_true",
        help="Fail suite when Lean/Hyperon bag parity fails (requires --compare-lean)",
    )
    parser.add_argument(
        "--algorithms-root",
        default="../algorithms",
        help="Path to algorithms repo root (used when --compare-lean is set)",
    )
    args = parser.parse_args()

    project_root = Path(__file__).resolve().parents[2]
    fixtures_path = project_root / args.fixtures
    results_path = project_root / args.results
    scratch_dir = project_root / args.scratch_dir
    algorithms_root = (project_root / args.algorithms_root).resolve()

    if args.require_lean_parity and not args.compare_lean:
        raise ValueError("--require-lean-parity requires --compare-lean")
    if args.compare_lean and not algorithms_root.exists():
        raise ValueError(f"algorithms root does not exist: {algorithms_root}")

    fixtures = load_fixtures(fixtures_path)
    scratch_dir.mkdir(parents=True, exist_ok=True)
    results_path.parent.mkdir(parents=True, exist_ok=True)

    rows: list[dict[str, Any]] = []
    pass_count = 0
    parity_pass_count = 0
    parity_total = 0

    for case in fixtures:
        fid = case["id"]
        expected = case["expected"]
        exp_counter = Counter(expected)
        status = "fail"
        reason = ""
        actual_terms_hyperon: list[str] = []
        actual_terms_lean: list[str] = []
        stdout_hyperon = ""
        stderr_hyperon = ""
        stdout_lean = ""
        stderr_lean = ""
        exit_code_hyperon = 0
        exit_code_lean = 0
        parity_status = "not_run"
        parity_reason = ""
        case_path = scratch_dir / f"{fid}.metta"
        try:
            exit_code_hyperon, stdout_hyperon, stderr_hyperon = run_hyperon_case(
                project_root=project_root,
                fixture_id=fid,
                setup=case["setup"],
                query=case["query"],
                env_name=args.conda_env,
                scratch_dir=scratch_dir,
            )
            if exit_code_hyperon != 0:
                reason = f"metta exited with code {exit_code_hyperon}"
            else:
                line = first_result_line(stdout_hyperon)
                actual_terms_hyperon = parse_metta_result_line(line)
                act_counter = Counter(actual_terms_hyperon)
                if act_counter == exp_counter:
                    status = "pass"
                else:
                    reason = (
                        f"bag mismatch expected={dict(exp_counter)} "
                        f"actual={dict(act_counter)}"
                    )

                if args.compare_lean:
                    parity_total += 1
                    exit_code_lean, stdout_lean, stderr_lean = run_lean_case(
                        algorithms_root=algorithms_root,
                        case_path=case_path,
                    )
                    try:
                        actual_terms_lean = parse_lean_results(stdout_lean)
                        lean_counter = Counter(actual_terms_lean)
                        if lean_counter == act_counter:
                            parity_status = "pass"
                            parity_pass_count += 1
                            if exit_code_lean != 0:
                                parity_reason = (
                                    f"Lean exited {exit_code_lean} but produced matching output"
                                )
                        else:
                            parity_status = "fail"
                            parity_reason = (
                                f"Lean/Hyperon bag mismatch lean={dict(lean_counter)} "
                                f"hyperon={dict(act_counter)}"
                            )
                    except Exception as lean_exc:  # noqa: BLE001
                        parity_status = "fail"
                        parity_reason = (
                            f"Lean simpleMeTTa exited {exit_code_lean} and "
                            f"output parse failed: {lean_exc}"
                        )
                    if args.require_lean_parity and parity_status != "pass":
                        if reason:
                            reason = reason + "; " + parity_reason
                        else:
                            reason = parity_reason
                        status = "fail"
        except Exception as exc:  # noqa: BLE001
            reason = str(exc)

        if status == "pass":
            pass_count += 1
            print(f"[pass] {fid}")
        else:
            print(f"[fail] {fid}: {reason}")
        if args.compare_lean:
            if parity_status == "pass":
                print(f"[parity-pass] {fid}")
            elif parity_status == "fail":
                print(f"[parity-fail] {fid}: {parity_reason}")

        rows.append(
            {
                "suite": "he_io",
                "id": fid,
                "status": status,
                "parity_status": parity_status,
                "tier": case.get("tier", ""),
                "lean_theorem": case.get("lean_theorem", ""),
                "implementation_priority": case.get("implementation_priority", ""),
                "implementation_group": case.get("implementation_group", ""),
                "expected": expected,
                "actual": actual_terms_hyperon,
                "actual_hyperon": actual_terms_hyperon,
                "actual_lean": actual_terms_lean,
                "source_note": case.get("source_note", ""),
                "query": case["query"],
                "exit_code": exit_code_hyperon,
                "stdout": stdout_hyperon,
                "stderr": stderr_hyperon,
                "exit_code_hyperon": exit_code_hyperon,
                "stdout_hyperon": stdout_hyperon,
                "stderr_hyperon": stderr_hyperon,
                "exit_code_lean": exit_code_lean,
                "stdout_lean": stdout_lean,
                "stderr_lean": stderr_lean,
                "reason": reason,
                "parity_reason": parity_reason,
                "timestamp_utc": datetime.now(timezone.utc).isoformat(),
            }
        )

    with results_path.open("w", encoding="utf-8") as f:
        for row in rows:
            f.write(json.dumps(row, ensure_ascii=True) + "\n")

    total = len(rows)
    fail_count = total - pass_count
    print(f"he_io summary: pass={pass_count} fail={fail_count} total={total}")
    if args.compare_lean:
        parity_fail = parity_total - parity_pass_count
        print(
            f"he_io parity summary: pass={parity_pass_count} "
            f"fail={parity_fail} total={parity_total}"
        )
    print(f"results: {results_path}")
    if fail_count != 0:
        return 1
    if args.require_lean_parity and parity_total != parity_pass_count:
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
