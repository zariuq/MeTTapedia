#!/usr/bin/env python3
"""Exercise the fixture reader's process-level rejection contract.

This checks failure reporting, not completeness of the source parser. Supply a
retained work directory so malformed-input evidence and logs remain inspectable.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def child_spans(text, start=0):
    """Locate children for fixture mutation, preserving quoted strings verbatim."""
    if text[start] != "(":
        raise ValueError("expected a list in the fixture")
    spans, index = [], start + 1
    while True:
        while text[index].isspace():
            index += 1
        if text[index] == ")":
            return spans
        begin, depth, quoted, escaped = index, 0, False, False
        while index < len(text):
            char = text[index]
            if quoted:
                if escaped:
                    escaped = False
                elif char == "\\":
                    escaped = True
                elif char == '"':
                    quoted = False
            elif char == '"':
                quoted = True
            elif char == "(":
                depth += 1
            elif char == ")":
                if depth == 0:
                    break
                depth -= 1
            elif char.isspace() and depth == 0:
                break
            index += 1
            if depth == 0 and not quoted and text[begin] in '("':
                break
        if index == begin or quoted or depth:
            raise ValueError("malformed fixture during mutation")
        spans.append((begin, index))


def main():
    tools = Path(__file__).resolve().parent
    repository = tools.parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, default=tools / "out/module_reads.metta")
    parser.add_argument("--work-dir", type=Path, required=True)
    args = parser.parse_args()
    work = args.work_dir.resolve()
    work.mkdir(parents=True, exist_ok=True)
    original = args.packet.read_text().strip()
    command = ["lake", "env", "lean", "--run", str(tools / "check_module_reader.lean")]
    inventory = subprocess.run(command + ["--labels"], cwd=repository / "lean/mettapedia",
                               text=True, capture_output=True, timeout=120)
    (work / "inventory.log").write_text(inventory.stdout + inventory.stderr)
    inventory.check_returncode()
    labels = inventory.stdout.splitlines()
    if not labels or len(labels) != len(set(labels)) or inventory.stderr:
        raise RuntimeError("invalid reader fixture inventory")
    expected_controls = [f"(ModuleReaderControl {name} true)" for name in labels]
    mutations = [
        ("wrong-envelope", "ModuleReads", "WrongEnvelope"),
        ("unknown-production", '"MFile"', '"MissingProduction"'),
        ("changed-name", "bnf-v1:text-cons 85 ", "bnf-v1:text-cons 86 "),
        ("refused-parse", "LangDef:AuthoredParseAccepted", "LangDef:AuthoredParseRejected"),
    ]
    cases = [("valid", original, True), ("empty", "", False),
             ("duplicate-envelope", original + "\n" + original, False),
             ("truncated", original[:len(original) // 2], False)]
    for name, before, after in mutations:
        if before not in original:
            raise SystemExit(f"mutation {name} no longer applies to the fixture")
        cases.append((name, original.replace(before, after, 1), False))
    root = child_spans(original)
    if len(root) != len(labels) + 1:
        raise RuntimeError("fixture envelope does not match the reader inventory")
    first = child_spans(original, root[1][0])
    if len(first) != 5 or original[slice(*first[0])] != "LangDef:AuthoredParseAccepted":
        raise RuntimeError("unexpected authored parse packet")
    begin, end = first[-1]
    trees = child_spans(original, begin)
    if len(trees) != 1:
        raise RuntimeError("the valid fixture must have exactly one first parse")
    tree = original[slice(*trees[0])]
    cases.extend([
        ("missing-tree", original[:begin] + "()" + original[end:], False),
        ("multiple-trees", original[:begin] + "(" + tree + " " + tree + ")" + original[end:], False),
    ])
    results = []
    for name, text, expected in cases:
        packet = work / f"{name}.metta"
        packet.write_text(text)
        result = subprocess.run(
            command + [str(packet)],
            cwd=repository / "lean/mettapedia", text=True, capture_output=True, timeout=120,
        )
        (work / f"{name}.log").write_text(result.stdout + result.stderr)
        accepted = result.returncode == 0
        controls = [line for line in result.stdout.splitlines() if line.startswith("(ModuleReaderControl")]
        correct = accepted == expected and (not expected or controls == expected_controls)
        if name in {"missing-tree", "multiple-trees"}:
            correct = correct and "expected one tree" in result.stdout + result.stderr
        results.append({"name": name, "expected_acceptance": expected,
                        "returncode": result.returncode, "passed": correct})
        print(f"{'PASS' if correct else 'FAIL'} {name}")
    report = {"fixture_sha256": hashlib.sha256(original.encode()).hexdigest(),
              "fixture_labels": labels, "results": results}
    (work / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    if not all(row["passed"] for row in results):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
