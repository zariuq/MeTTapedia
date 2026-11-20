#!/usr/bin/env python3
"""Check fresh generic-fact output of a supplied CeTTa direct compiler in Lean.

This authoring check prepares concrete kernel controls from emitted equation
trees. Each run rereads the source fixture, invokes the compiler and checks a
fresh Lean file. CeTTa's ordinary build and tests do not depend on this tool.
The source fixture uses canonical question-variable spellings. Scalar
spellings may differ after printing: the kernel checks their typed readbacks.
Operational correspondence and other branches have separate qualification gates.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile


def map_tokens(value, function):
    result = [None]
    pending = [(value, result, 0)]
    while pending:
        node, parent, index = pending.pop()
        if isinstance(node, str):
            parent[index] = function(node)
        else:
            children = [None] * len(node)
            parent[index] = children
            pending.extend((child, children, i) for i, child in enumerate(node))
    return result[0]


def tokens(value):
    pending = [value]
    while pending:
        node = pending.pop()
        if isinstance(node, str):
            yield node
        else:
            pending.extend(reversed(node))


def lean_string(value):
    if any(not character.isprintable() for character in value):
        return "(String.ofList [" + ", ".join(
            f"Char.ofNat {ord(character)}" for character in value) + "])"
    return json.dumps(value, ensure_ascii=False)


def lean_tree(value):
    output, pending = [], [(False, value)]
    while pending:
        literal, node = pending.pop()
        if literal:
            output.append(node)
        elif isinstance(node, str):
            output.append("(SExpr.atom " + lean_string(node) + ")")
        else:
            output.append("(SExpr.list [")
            pending.append((True, "])"))
            for i in range(len(node) - 1, -1, -1):
                pending.append((False, node[i]))
                if i:
                    pending.append((True, ", "))
    return "".join(output)


def controls(heads, emitted):
    lines = ["import Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPatternRealization",
        "open Algorithms.MeTTa.Simple.Parser (SExpr)",
        "open Mettapedia.Languages.MeTTa.OSLFCore (Atom)",
        "open Mettapedia.Languages.MeTTa.PeTTa",
        "open Mettapedia.Languages.ProcessCalculi.MORK (Subst)",
        "open Mettapedia.GSLT.Parsing.GeneratedPeTTaFactSyntax",
        "open Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPattern (encode encodeList)"]
    for i, (source, equation) in enumerate(zip(heads, emitted)):
        # This is an untrusted candidate. The kernel independently reads it
        # against SOURCE, then checks the entire clause, selector included.
        head = equation[2][3][1]
        slot = equation[1][1]
        lines += [f"def source{i} : SExpr := " + lean_tree(source),
            f"def expected{i} : SExpr := " + lean_tree(head),
            f"def actual{i} : SExpr := " + lean_tree(equation),
            f"theorem actual{i}_checked : check expected{i} actual{i} = true := by",
            f"  apply check_equation (slot := {lean_string(slot)})",
            f"  · simp [freshSlot, expected{i}, containsToken, containsTokenList]",
            f"  · simp [equation?, equation, expected{i}, actual{i}, encode, encodeList]",
            f"theorem source{i}_checked : checkSource source{i} actual{i} = true := by",
            f"  have same : readbacksAgree source{i} expected{i} = true := by decide +kernel",
            f"  simp only [checkSource, checked_body_parts actual{i}_checked, actual{i}_checked, same, Bool.and_self]",
            f"def selector{i} : SExpr := " + lean_tree(equation[2][1]),
            f"theorem actual{i}_parts : bodyParts? actual{i} = some (selector{i}, expected{i}) := rfl",
            f"theorem actual{i}_selector_run (registry : SpaceSemantics.Program)",
            "    (base : Unifying.Configuration) (bindings : Subst)",
            "    (valid : Unifying.Idempotent bindings) :",
            f"    ∃ atom code, SpaceSemantics.readRawExpression source{i} = .ok atom ∧",
            f"      SpaceSemantics.readRawExpression selector{i} = .ok code ∧",
            "      ∃ spent, ∀ remaining,",
            "        Unifying.run registry (spent + remaining)",
            "          {base with control := .evaluate bindings code, frames := []} =",
            "        .complete base.state [Unifying.resolve bindings atom] base.input base.output :=",
            f"  checked_source_selector_run source{i}_checked actual{i}_parts registry base bindings valid",
            f"#print axioms actual{i}_selector_run"]
    count = len(heads)
    lines += ["def expectedHeads : List SExpr := [" + ", ".join(f"expected{i}" for i in range(count)) + "]",
        "def sourceHeads : List SExpr := [" + ", ".join(f"source{i}" for i in range(count)) + "]",
        "def actualClauses : List SExpr := [" + ", ".join(f"actual{i}" for i in range(count)) + "]",
        "theorem actual_batch_checked : checkMany expectedHeads actualClauses = true := by",
        "  simp [expectedHeads, actualClauses, checkMany, " +
            ", ".join(f"actual{i}_checked" for i in range(count)) + "]",
        "theorem source_batch_checked : List.Forall₂ (fun source emitted => checkSource source emitted = true)",
        "    sourceHeads actualClauses := by",
        "  simp [sourceHeads, actualClauses, " + ", ".join(f"source{i}_checked" for i in range(count)) + "]"]

    wrong = map_tokens(emitted[0], lambda word: word)
    wrong[2][-1] = ["quote", "corrupted-result"]
    lines += ["def wrongResult : SExpr := " + lean_tree(wrong),
        "theorem wrong_result_rejected : check expected0 wrongResult = false := by",
        "  simp [check, inputSlot?, freshSlot, expected0, wrongResult, equation?, equation, "
            "containsToken, containsTokenList, encode, encodeList]"]
    plain_selector = map_tokens(emitted[0], lambda word: word)
    plain_selector[2][1] = plain_selector[2][3][1]
    lines += ["def plainSelector : SExpr := " + lean_tree(plain_selector),
        "theorem wrong_selector_rejected : check expected0 plainSelector = false := by",
        "  decide +kernel"]
    old_slot = emitted[1][1][1]
    captured = next(word for word in tokens(heads[1]) if word.startswith("$"))
    changed = map_tokens(emitted[1], lambda word: captured if word == old_slot else word)
    lines += ["def capturedSlot : SExpr := " + lean_tree(changed),
        "theorem captured_slot_rejected : check expected1 capturedSlot = false := by",
        "  simp [check, inputSlot?, freshSlot, expected1, capturedSlot, containsToken, containsTokenList]",
        "theorem missing_occurrence_rejected : checkMany expectedHeads actualClauses.tail = false := by",
        "  cases result : checkMany expectedHeads actualClauses.tail with",
        "  | false => rfl",
        "  | true =>",
        "      have count := checked_occurrence_count result",
        "      simp [expectedHeads, actualClauses] at count",
        "theorem extra_occurrence_rejected : checkMany expectedHeads (actualClauses ++ [actual0]) = false := by",
        "  cases result : checkMany expectedHeads (actualClauses ++ [actual0]) with",
        "  | false => rfl",
        "  | true =>",
        "      have count := checked_occurrence_count result",
        "      simp [expectedHeads, actualClauses] at count"]
    boolean = next(i for i, head in enumerate(heads) if head[1:] == ["True"])
    string = next(i for i, head in enumerate(heads) if head[1:] == ['"True"'])
    lines += ["theorem changed_value_kind_rejected :",
        f"    checkSource source{boolean} actual{string} = false := by",
        "  decide +kernel",
        "#print axioms actual_batch_checked", "#print axioms source_batch_checked",
        "#print axioms wrong_result_rejected",
        "#print axioms wrong_selector_rejected",
        "#print axioms captured_slot_rejected", "#print axioms missing_occurrence_rejected",
        "#print axioms extra_occurrence_rejected", "#print axioms changed_value_kind_rejected"]
    return "\n".join(lines) + "\n"


def qualify(args, repository, work):
    source = repository / "metta/fixtures/gslt_direct_fact_evidence_v1.metta"
    compiler = args.compiler.resolve()
    source_bytes = source.read_bytes()
    compiler_sha = hashlib.sha256(compiler.read_bytes()).hexdigest()
    snapshot = work / "source.metta"
    snapshot.write_bytes(source_bytes)
    sys.path.insert(0, str(args.cetta_root.resolve() / "tests/support"))
    from check_transform_swi_differential import read_forms
    native, proof = work / "native.metta", work / "evidence.lean"
    # A successful process must produce a new payload. An old artifact in
    # WORK cannot satisfy a compiler that exits without writing its output.
    with tempfile.TemporaryDirectory(prefix="compile-", dir=work) as directory:
        fresh = Path(directory) / "native.metta"
        result = subprocess.run([str(compiler), "petta-direct", "--source", str(snapshot), "--out", str(fresh)],
                                capture_output=True, text=True, timeout=60)
        native_bytes = fresh.read_bytes() if result.returncode == 0 else None
    (work / "compiler.log").write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError("compiler did not complete successfully: " + result.stderr)
    native.write_bytes(native_bytes)
    presentation, = read_forms(source_bytes.decode("utf-8"))
    rules = next(part[1:] for part in presentation if isinstance(part, list) and part[0] == "rewrites")
    if not all(next(part for part in rule if isinstance(part, list) and part[0] == "body") == ["body"]
               for rule in rules):
        raise ValueError("the generic-fact fixture must have empty premise lists")
    heads = [map_tokens(next(part[1] for part in rule if isinstance(part, list) and part[0] == "head"),
        lambda word: "$" + word[1:] if word.startswith("?") and len(word) > 1 else word) for rule in rules]
    names = {"gslt:" + head[0] for head in heads}
    emitted = [form for form in read_forms(native_bytes.decode("utf-8")) if isinstance(form, list) and len(form) == 3
        and form[0] == "=" and isinstance(form[1], list) and form[1] and form[1][0] in names]
    if len(emitted) != len(heads) or len(heads) < 2:
        raise ValueError("native clause occurrences differ from source")
    if len(set(map(json.dumps, heads))) == len(heads):
        raise ValueError("fixture needs duplicate source occurrences")
    proof_bytes = controls(heads, emitted).encode("utf-8")
    proof.write_bytes(proof_bytes)
    if not args.prepare_only:
        lean_root = repository / "lean/mettapedia"
        subprocess.run(["lake", "build", "Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPatternRealization"],
                       cwd=lean_root, check=True)
        checked = subprocess.run(["lake", "env", "lean", str(proof)], cwd=lean_root,
                                 capture_output=True, text=True)
        (work / "proof.log").write_text(checked.stdout + checked.stderr)
        if checked.returncode:
            raise RuntimeError("kernel controls failed: " + checked.stdout + checked.stderr)
        standard = {"propext", "Classical.choice", "Quot.sound"}
        names = ["actual_batch_checked", "source_batch_checked", "wrong_result_rejected",
                 "wrong_selector_rejected",
                     "captured_slot_rejected", "missing_occurrence_rejected",
                 "extra_occurrence_rejected", "changed_value_kind_rejected"]
        names += [f"actual{i}_selector_run" for i in range(len(heads))]
        for name in names:
            audit = re.search("'" + name + r"' depends on axioms:\s*\[([^]]*)\]", checked.stdout)
            if audit:
                axioms = {item.strip() for item in audit[1].split(",") if item.strip()}
                if not axioms <= standard:
                    raise RuntimeError("nonstandard axioms in " + name + ": " + ", ".join(sorted(axioms)))
            elif "'" + name + "' does not depend on any axioms" not in checked.stdout:
                raise RuntimeError("missing axiom audit for " + name)
    if source.read_bytes() != source_bytes or hashlib.sha256(compiler.read_bytes()).hexdigest() != compiler_sha:
        raise RuntimeError("source fixture or compiler changed during qualification")
    if native.read_bytes() != native_bytes or proof.read_bytes() != proof_bytes:
        raise RuntimeError("compiler payload or kernel evidence changed during qualification")
    return dict(status="prepared" if args.prepare_only else "checked", clauses=len(heads),
        rejected_mutants=0 if args.prepare_only else 6,
        finite_selector_runs=0 if args.prepare_only else len(heads),
        source_sha256=hashlib.sha256(source_bytes).hexdigest(), compiler_sha256=compiler_sha,
        payload_sha256=hashlib.sha256(native_bytes).hexdigest(), evidence_sha256=hashlib.sha256(proof_bytes).hexdigest())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", required=True, type=Path)
    parser.add_argument("--cetta-root", required=True, type=Path)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--prepare-only", action="store_true")
    args = parser.parse_args()
    repository = Path(__file__).resolve().parents[3]
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=True)
    receipt = work / "summary.json"
    receipt.write_text(json.dumps(dict(status="pending")) + "\n")
    try:
        summary = qualify(args, repository, work)
    except Exception as error:
        status = "unfinished" if isinstance(error, subprocess.TimeoutExpired) else "failed"
        receipt.write_text(json.dumps(dict(status=status, reason=str(error))) + "\n")
        raise
    receipt.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary))


if __name__ == "__main__":
    main()
