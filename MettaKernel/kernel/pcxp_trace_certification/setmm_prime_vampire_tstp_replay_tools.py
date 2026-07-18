#!/usr/bin/env python3
"""Generate a Prime replay from Vampire's TSTP proof of public set.mm theorem ja."""

from __future__ import annotations

import argparse
import dataclasses
import subprocess
import sys
from pathlib import Path

import setmm_prime_e_tstp_replay_tools as tstp


def unique_direct_normalization(
    combined: tstp.AnnotatedClause,
    hypothesis_1: tstp.AnnotatedClause,
    hypothesis_2: tstp.AnnotatedClause,
    target: tstp.Clause,
) -> tuple[
    tuple[tstp.AnnotatedClause, dict[tstp.Term, tstp.Term], tstp.Literal, tstp.Literal],
    tuple[tstp.AnnotatedClause, dict[tstp.Term, tstp.Term], tstp.Literal, tstp.Literal],
]:
    answers = []
    for first in tstp.resolution_candidates(combined, hypothesis_1):
        for second in tstp.resolution_candidates(first[0], hypothesis_2):
            if tstp.canonical_clause(second[0].clause) == tstp.canonical_clause(target):
                answers.append((first, second))
    if len(answers) != 1:
        raise ValueError(f"expected one Horn normalization, found {len(answers)}")
    return answers[0]


def render_step(
    left_name: str,
    right_name: str,
    result_name: str,
    result: tstp.AnnotatedClause,
    substitution: dict[tstp.Term, tstp.Term],
    left_pivot: tstp.Literal,
    right_pivot: tstp.Literal,
) -> list[str]:
    normalized = tuple(
        sorted(
            (
                (variable, tstp.apply_term(term, substitution))
                for variable, term in substitution.items()
            ),
            key=lambda binding: binding[0].name,
        )
    )
    return [
        "!(assertEqual",
        "  (atp:resolution:check-step",
        f"    &{left_name} &{right_name}",
        f"    {tstp.metta_substitution(normalized)}",
        f"    {tstp.metta_literal(left_pivot)}",
        f"    {tstp.metta_literal(right_pivot)}",
        f"    &{result_name})",
        "  True)",
        "",
    ]


def build_replay(text: str) -> str:
    statements = tstp.parse_statements(text)
    rule_d1_stmt = tstp.find_source_cnf(
        statements, "rule_pm2_61d1", lambda clause: len(clause) == 3
    )
    rule_imim_stmt = tstp.find_source_cnf(
        statements, "rule_imim2i", lambda clause: len(clause) == 2
    )
    h1_stmt = tstp.find_source_cnf(
        statements,
        "hypothesis_1",
        lambda clause: len(clause) == 1 and clause[0].positive,
    )
    h2_stmt = tstp.find_source_cnf(
        statements,
        "hypothesis_2",
        lambda clause: len(clause) == 1 and clause[0].positive,
    )
    goal_stmt = tstp.find_source_cnf(
        statements,
        "target",
        lambda clause: len(clause) == 1 and not clause[0].positive,
    )

    combined_stmt = tstp.direct_child(statements, rule_d1_stmt.name, rule_imim_stmt.name)
    after_goal_stmt = tstp.direct_child(statements, combined_stmt.name, goal_stmt.name)
    after_h1_stmt = tstp.direct_child(statements, after_goal_stmt.name, h1_stmt.name)
    empty_stmt = tstp.direct_child(statements, after_h1_stmt.name, h2_stmt.name)
    if empty_stmt.clause != ():
        raise ValueError("Vampire proof does not end in the empty clause")

    rule_d1 = tstp.source_clause(
        tstp.rename_clause(rule_d1_stmt.clause or (), "vr0"), "rule_pm2_61d1"
    )
    rule_imim = tstp.source_clause(
        tstp.rename_clause(rule_imim_stmt.clause or (), "vr1"), "rule_imim2i"
    )
    h1 = tstp.source_clause(
        tstp.rename_clause(h1_stmt.clause or (), "vh1"), "hypothesis_1"
    )
    h2 = tstp.source_clause(
        tstp.rename_clause(h2_stmt.clause or (), "vh2"), "hypothesis_2"
    )
    goal_negative = tstp.source_clause(
        tstp.rename_clause(goal_stmt.clause or (), "vgoal"), "target"
    )

    combined, s0, lp0, rp0 = tstp.select_resolution(
        rule_d1, rule_imim, combined_stmt.clause or (), "Vampire resolution 1"
    )
    after_goal, s1, lp1, rp1 = tstp.select_resolution(
        combined, goal_negative, after_goal_stmt.clause or (), "Vampire resolution 2"
    )
    after_h1, s2, lp2, rp2 = tstp.select_resolution(
        after_goal, h1, after_h1_stmt.clause or (), "Vampire resolution 3"
    )
    empty, s3, lp3, rp3 = tstp.select_resolution(
        after_h1, h2, (), "Vampire resolution 4"
    )

    target_positive_clause = (tstp.Literal(True, goal_negative.clause[0].atom),)
    direct_first, direct_second = unique_direct_normalization(
        combined, h1, h2, target_positive_clause
    )
    direct_h1, sd1, lpd1, rpd1 = direct_first
    direct_target, sd2, lpd2, rpd2 = direct_second
    if direct_target.proof is None:
        raise ValueError("normalized Vampire refutation has no direct Horn proof")

    named = {
        "v-rule-d1": rule_d1.clause,
        "v-rule-imim2i": rule_imim.clause,
        "v-h1": h1.clause,
        "v-h2": h2.clause,
        "v-goal-negative": goal_negative.clause,
        "v-combined": combined.clause,
        "v-after-goal": after_goal.clause,
        "v-after-h1": after_h1.clause,
        "v-empty": empty.clause,
        "v-direct-h1": direct_h1.clause,
        "v-direct-target": direct_target.clause,
    }

    lines = [
        "; ============================================================================",
        "; setmm_prime_vampire_ja_resolution_replay_v0.metta",
        "; GENERATED from Vampire's TSTP proof by the independent adapter.",
        "; The exact four-step refutation is replayed first.  Its Horn fragment is",
        "; then normalized by two unit-resolution steps into a direct proof term,",
        "; which is accepted only by Prime's unchanged type checker.",
        "; ============================================================================",
        "",
        "!(import! &self lib_atp)",
        "",
    ]
    for name, clause in named.items():
        lines.append(f"!(bind! &{name} {tstp.metta_clause(clause)})")
    lines.append("")
    exact_steps = [
        ("v-rule-d1", "v-rule-imim2i", "v-combined", combined, s0, lp0, rp0),
        ("v-combined", "v-goal-negative", "v-after-goal", after_goal, s1, lp1, rp1),
        ("v-after-goal", "v-h1", "v-after-h1", after_h1, s2, lp2, rp2),
        ("v-after-h1", "v-h2", "v-empty", empty, s3, lp3, rp3),
    ]
    for left_name, right_name, result_name, result, substitution, left_pivot, right_pivot in exact_steps:
        lines.extend(
            render_step(
                left_name,
                right_name,
                result_name,
                result,
                substitution,
                left_pivot,
                right_pivot,
            )
        )

    lines.extend([
        "; Certificate-preserving Horn normalization of the same refutation.",
        *render_step(
            "v-combined",
            "v-h1",
            "v-direct-h1",
            direct_h1,
            sd1,
            lpd1,
            rpd1,
        ),
        *render_step(
            "v-direct-h1",
            "v-h2",
            "v-direct-target",
            direct_target,
            sd2,
            lpd2,
            rpd2,
        ),
        "; Negative: the empty clause cannot be replaced by a forged unit.",
        "!(assertEqual",
        "  (atp:resolution:check-step",
        f"    &v-after-h1 &v-h2 {tstp.metta_substitution(tuple(sorted(s3.items(), key=lambda item: item[0].name)))}",
        f"    {tstp.metta_literal(lp3)}",
        f"    {tstp.metta_literal(rp3)}",
        "    ((ATP.Pos (proved forged))))",
        "  False)",
        "",
    ])
    first_bindings = tuple(sorted(s0.items(), key=lambda item: item[0].name))
    shortened = tuple(first_bindings[:-1])
    lines.extend([
        "; Negative: dropping a unifier binding invalidates the first step.",
        "!(assertEqual",
        "  (atp:resolution:check-step",
        f"    &v-rule-d1 &v-rule-imim2i {tstp.metta_substitution(shortened)}",
        f"    {tstp.metta_literal(lp0)}",
        f"    {tstp.metta_literal(rp0)}",
        "    &v-combined)",
        "  False)",
        "",
        "; The normalized direct proof crosses the unchanged Prime checker.",
        "!(bind! &v-ja-kb (new-space))",
    ])

    source_rules = [("rule_pm2_61d1", rule_d1), ("rule_imim2i", rule_imim)]
    source_facts = [("hypothesis_1", h1), ("hypothesis_2", h2)]
    for constant in tstp.object_constants(
        clause.clause for _, clause in source_rules + source_facts
    ):
        lines.append(f"!(add-atom &v-ja-kb (: {constant} Type))")
    lines.extend([
        "!(add-atom &v-ja-kb (: imp (-> Type Type Type)))",
        "!(add-atom &v-ja-kb (: neg (-> Type Type)))",
    ])
    for label, annotated in source_facts:
        formula = tstp.unwrap_proved(
            next(entry.literal for entry in annotated.entries if entry.literal.positive)
        )
        lines.append(
            f"!(add-atom &v-ja-kb (: {label} {tstp.metta_term(formula, typed=True)}))"
        )
    for label, annotated in source_rules:
        positives = [entry.literal for entry in annotated.entries if entry.literal.positive]
        negatives = [entry.literal for entry in annotated.entries if not entry.literal.positive]
        if len(positives) != 1:
            raise ValueError(f"{label}: expected one positive literal")
        parts = [
            tstp.metta_term(tstp.unwrap_proved(literal), typed=True)
            for literal in negatives + positives
        ]
        lines.append(f"!(add-atom &v-ja-kb (: {label} (-> {' '.join(parts)})))")
    goal = tstp.unwrap_proved(goal_negative.clause[0])
    goal_text = tstp.metta_term(goal, typed=True)
    proof_text = tstp.metta_proof(direct_target.proof)
    lines.extend([
        "",
        "!(assertEqual",
        f"  (check-type &v-ja-kb {proof_text} {goal_text} 100000)",
        f"  (he-accept (exact {goal_text})))",
        "",
        "!(println! (SetMMPrimeVampireTSTPReplaySummary ja 9 9 0))",
        "",
    ])
    return "\n".join(lines)


def run_vampire(executable: Path, problem: Path, time_limit: int) -> str:
    completed = subprocess.run(
        [
            str(executable),
            "--mode",
            "vampire",
            "--random_polarities",
            "off",
            "--avatar",
            "off",
            "--proof",
            "tptp",
            "--output_axiom_names",
            "on",
            "--time_limit",
            str(time_limit),
            str(problem),
        ],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if "SZS status Theorem" not in completed.stdout:
        raise RuntimeError(
            f"Vampire did not prove {problem.name} (exit {completed.returncode})"
        )
    return completed.stdout


def self_test(proof_text: str) -> None:
    mutations = {
        "changed-resolvent": proof_text.replace(
            "~proved(imp(neg(f_ph_183),f_ch_183)) | ~proved(imp(f_ps_183,f_ch_183))",
            "~proved(imp(neg(f_ph_183),forged)) | ~proved(imp(f_ps_183,f_ch_183))",
            1,
        ),
        "changed-parent": proof_text.replace("[f572,f408]", "[f572,f579]", 1),
        "missing-empty-clause": proof_text.replace(
            "fof(f119481,plain,(\n  $false)",
            "fof(f119481,plain,(\n  proved(forged))",
            1,
        ),
    }
    for name, mutation in mutations.items():
        if mutation == proof_text:
            raise ValueError(f"self-test mutation {name} did not change the proof")
        try:
            build_replay(mutation)
        except (ValueError, RuntimeError):
            continue
        raise ValueError(f"self-test mutation survived: {name}")


def main() -> int:
    root = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--proof",
        type=Path,
        default=root / "tptp/ja_hilbert_full_vampire_refutation.tstp",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=root / "setmm_prime_vampire_ja_resolution_replay_v0.metta",
    )
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--live-vampire", type=Path)
    parser.add_argument("--problem", type=Path, default=root / "tptp/ja_hilbert_full.p")
    parser.add_argument("--time-limit", type=int, default=5)
    args = parser.parse_args()
    if not any((args.write, args.check, args.self_test, args.live_vampire)):
        parser.error("choose --write, --check, --self-test, or --live-vampire")

    proof_text = args.proof.read_text()
    generated = build_replay(proof_text)
    if args.write:
        args.output.write_text(generated)
        print(f"PASS: wrote {args.output.name}")
    if args.check:
        if not args.output.exists() or args.output.read_text() != generated:
            print(f"FAIL: {args.output.name} is not deterministic", file=sys.stderr)
            return 1
        print(f"PASS: {args.output.name} is deterministic")
    if args.self_test:
        self_test(proof_text)
        print("PASS: all 3 Vampire TSTP mutations are rejected")
    if args.live_vampire:
        live = build_replay(run_vampire(args.live_vampire, args.problem, args.time_limit))
        if live != generated:
            print("FAIL: live Vampire proof differs from frozen replay", file=sys.stderr)
            return 1
        print("PASS: live Vampire TSTP proof reproduces the frozen Prime replay")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
