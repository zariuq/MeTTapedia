#!/usr/bin/env python3
"""Build Prime and TPTP ATP fixtures directly from CC0 ``set.mm``.

The extractor deliberately consumes Metamath source, not a translated MeTTa
corpus or a premise-selection trace.  It reconstructs the implication/negation
fragment beginning at ``ax-mp`` and ending at ``ja``, including each
assertion's active essential hypotheses.  Two syntax constructors occupy
indices 0 and 1 in the historical experimental numbering, so the first
provability assertion, ``ax-mp``, has index 2.

Generated ATP problems distinguish three theory policies:

* ``core``: only ``ax-mp``, ``ax-1``, ``ax-2``, and ``ax-3``;
* ``full``: every earlier provability assertion in source order;
* ``reference``: only the provability labels named in set.mm's stored proof.

Only ``core`` and ``full`` are proof-search experiments.  ``reference`` is a
calibration case conditioned on proof support and must not be reported as
premise discovery.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Iterator, Sequence


HERE = Path(__file__).resolve().parent
DEFAULT_TARGETS = ("pm2.61nii", "pm2.61iii", "ja")
CORE_LABELS = ("ax-mp", "ax-1", "ax-2", "ax-3")
EXPECTED_ANCHORS = {
    2: "ax-mp",
    3: "ax-1",
    4: "ax-2",
    5: "ax-3",
    6: "mp2",
    181: "pm2.61nii",
    182: "pm2.61iii",
    183: "ja",
}


@dataclass(frozen=True)
class Formula:
    tag: str
    name: str | None = None
    left: "Formula | None" = None
    right: "Formula | None" = None


@dataclass(frozen=True)
class Assertion:
    index: int
    label: str
    kind: str
    premises: tuple[Formula, ...]
    conclusion: Formula
    proof_labels: tuple[str, ...]


class SourceError(ValueError):
    pass


def source_tokens(text: str) -> Iterator[str]:
    """Tokenize Metamath while removing ``$( ... $)`` comments."""

    for match in re.finditer(r"\$\([\s\S]*?\$\)|\S+", text):
        token = match.group(0)
        if not token.startswith("$("):
            yield token


def take_until(tokens: Sequence[str], pos: int, marker: str) -> tuple[list[str], int]:
    out: list[str] = []
    while pos < len(tokens) and tokens[pos] != marker:
        out.append(tokens[pos])
        pos += 1
    if pos >= len(tokens):
        raise SourceError(f"missing {marker!r}")
    return out, pos + 1


def parse_formula(tokens: Sequence[str]) -> Formula:
    """Parse the implication/negation formula grammar used by this tranche."""

    def go(pos: int) -> tuple[Formula, int]:
        if pos >= len(tokens):
            raise SourceError("unexpected end of formula")
        token = tokens[pos]
        if token == "-.":
            child, pos = go(pos + 1)
            return Formula("neg", left=child), pos
        if token == "(":
            left, pos = go(pos + 1)
            if pos >= len(tokens) or tokens[pos] != "->":
                found = tokens[pos] if pos < len(tokens) else "<end>"
                raise SourceError(f"expected '->', found {found!r}")
            right, pos = go(pos + 1)
            if pos >= len(tokens) or tokens[pos] != ")":
                found = tokens[pos] if pos < len(tokens) else "<end>"
                raise SourceError(f"expected ')', found {found!r}")
            return Formula("imp", left=left, right=right), pos + 1
        if token.startswith("$"):
            raise SourceError(f"unexpected Metamath marker {token!r}")
        return Formula("var", name=token), pos + 1

    result, end = go(0)
    if end != len(tokens):
        raise SourceError(f"trailing formula tokens: {tokens[end:]!r}")
    return result


def parse_provability(expression: Sequence[str]) -> Formula:
    if not expression or expression[0] != "|-":
        raise SourceError(f"expected provability expression, found {expression!r}")
    return parse_formula(expression[1:])


def extract_assertions(text: str) -> list[Assertion]:
    """Extract the exact ``ax-mp`` through ``ja`` provability sequence."""

    tokens = list(source_tokens(text))
    essentials: list[Formula] = []
    scope_marks: list[int] = []
    raw: list[tuple[str, str, tuple[Formula, ...], Formula, tuple[str, ...]]] = []
    started = False
    pos = 0

    while pos < len(tokens):
        token = tokens[pos]
        if token == "${":
            scope_marks.append(len(essentials))
            pos += 1
            continue
        if token == "$}":
            if not scope_marks:
                raise SourceError("unmatched $}")
            del essentials[scope_marks.pop():]
            pos += 1
            continue
        if token in ("$c", "$v", "$d"):
            _, pos = take_until(tokens, pos + 1, "$.")
            continue
        if token in ("$[",):
            _, pos = take_until(tokens, pos + 1, "$]")
            continue

        if pos + 1 >= len(tokens) or tokens[pos + 1] not in ("$f", "$e", "$a", "$p"):
            pos += 1
            continue

        label = token
        kind = tokens[pos + 1]
        expression, pos = take_until(tokens, pos + 2, "$." if kind != "$p" else "$=")

        if kind == "$f":
            continue
        if kind == "$e":
            if expression and expression[0] == "|-":
                essentials.append(parse_provability(expression))
            continue

        proof_labels: tuple[str, ...] = ()
        if kind == "$p":
            proof, pos = take_until(tokens, pos, "$.")
            if proof and proof[0] == "(":
                try:
                    close = proof.index(")")
                except ValueError as error:
                    raise SourceError(f"unclosed compressed-proof label list for {label}") from error
                proof_labels = tuple(proof[1:close])
            else:
                proof_labels = tuple(proof)

        if not expression or expression[0] != "|-":
            continue
        try:
            conclusion = parse_provability(expression)
        except SourceError:
            if started:
                raise
            continue

        if label == "ax-mp":
            started = True
        if not started:
            continue
        raw.append((label, kind, tuple(essentials), conclusion, proof_labels))
        if label == "ja":
            break

    assertions = [
        Assertion(index=position + 2, label=label, kind=kind,
                  premises=premises, conclusion=conclusion,
                  proof_labels=proof_labels)
        for position, (label, kind, premises, conclusion, proof_labels)
        in enumerate(raw)
    ]
    if len(assertions) != 182:
        # There are 182 assertions from index 2 through index 183 inclusive.
        raise SourceError(
            f"expected 182 provability assertions ax-mp..ja, found {len(assertions)}"
        )
    by_index = {assertion.index: assertion.label for assertion in assertions}
    bad = {
        index: (expected, by_index.get(index))
        for index, expected in EXPECTED_ANCHORS.items()
        if by_index.get(index) != expected
    }
    if bad:
        raise SourceError(f"set.mm implication-fragment anchor mismatch: {bad}")
    return assertions


def formula_vars(formula: Formula, out: list[str] | None = None) -> list[str]:
    if out is None:
        out = []
    if formula.tag == "var":
        assert formula.name is not None
        if formula.name not in out:
            out.append(formula.name)
    else:
        assert formula.left is not None
        formula_vars(formula.left, out)
        if formula.right is not None:
            formula_vars(formula.right, out)
    return out


def assertion_vars(assertion: Assertion) -> list[str]:
    result: list[str] = []
    for premise in assertion.premises:
        formula_vars(premise, result)
    formula_vars(assertion.conclusion, result)
    return result


def metta_formula(formula: Formula, substitution: dict[str, str]) -> str:
    if formula.tag == "var":
        assert formula.name is not None
        return substitution[formula.name]
    assert formula.left is not None
    if formula.tag == "neg":
        return f"(neg {metta_formula(formula.left, substitution)})"
    assert formula.tag == "imp" and formula.right is not None
    return (
        f"(impl {metta_formula(formula.left, substitution)} "
        f"{metta_formula(formula.right, substitution)})"
    )


def tptp_term(formula: Formula, substitution: dict[str, str]) -> str:
    if formula.tag == "var":
        assert formula.name is not None
        return substitution[formula.name]
    assert formula.left is not None
    if formula.tag == "neg":
        return f"neg({tptp_term(formula.left, substitution)})"
    assert formula.tag == "imp" and formula.right is not None
    return (
        f"imp({tptp_term(formula.left, substitution)},"
        f"{tptp_term(formula.right, substitution)})"
    )


def semantic_formula(formula: Formula, substitution: dict[str, str]) -> str:
    if formula.tag == "var":
        assert formula.name is not None
        return substitution[formula.name]
    assert formula.left is not None
    if formula.tag == "neg":
        return f"~ ({semantic_formula(formula.left, substitution)})"
    assert formula.tag == "imp" and formula.right is not None
    return (
        f"({semantic_formula(formula.left, substitution)} => "
        f"{semantic_formula(formula.right, substitution)})"
    )


def safe_name(label: str) -> str:
    return re.sub(r"[^A-Za-z0-9_]", "_", label).lower()


def upper_var(name: str) -> str:
    return "V_" + re.sub(r"[^A-Za-z0-9_]", "_", name).upper()


def metta_assertion_atoms(
    assertion: Assertion, proof_atom: str | None = None
) -> list[str]:
    variables = assertion_vars(assertion)
    substitution = {name: f"${name}" for name in variables}
    premises = [metta_formula(item, substitution) for item in assertion.premises]
    conclusion = metta_formula(assertion.conclusion, substitution)
    if premises:
        typ = f"(-> {' '.join(premises)} {conclusion})"
        admission = "chaining-rule"
    else:
        typ = conclusion
        admission = "type-scheme"
    proof = proof_atom if proof_atom is not None else assertion.label
    return [f"(: {proof} {typ})", f"({admission} {proof})"]


def nested_initialization(atoms: Sequence[str], final_expression: str) -> str:
    expression = final_expression
    for position, atom in reversed(list(enumerate(atoms))):
        expression = f"(let $init{position} (add-atom $kb {atom})\n  {expression})"
    return f"(let $kb (new-space)\n  {expression})"


def theory_assertions(assertions: Sequence[Assertion], target: Assertion,
                      policy: str) -> list[Assertion]:
    earlier = [item for item in assertions if item.index < target.index]
    by_label = {item.label: item for item in earlier}
    if policy == "full":
        return earlier
    if policy == "core":
        return [by_label[label] for label in CORE_LABELS]
    if policy == "reference":
        labels = [label for label in target.proof_labels if label in by_label]
        # Proof label lists also name syntax constructors such as wi and wn.
        unique = list(dict.fromkeys(labels))
        return [by_label[label] for label in unique]
    raise ValueError(f"unknown theory policy: {policy}")


def generate_metta(assertions: Sequence[Assertion], targets: Sequence[Assertion],
                   source_digest: str, source_revision: str,
                   depth: int, fuel: int, guided: bool) -> str:
    filename = ("setmm_prime_atp_guided_181_183_v0.metta" if guided else
                "setmm_prime_full_181_183_v0.metta")
    policy = (" (search-policy atp-guided-inhabitation)" if guided else "")
    policy_name = "atp-guided-inhabitation" if guided else "native"
    lines = [
        "; ============================================================================",
        f"; {filename}",
        ";",
        "; GENERATED directly from the CC0 set.mm implication/negation fragment.",
        f"; set.mm revision: {source_revision}",
        f"; set.mm SHA-256: {source_digest}",
        "; Theory policy: every earlier provability assertion in source order.",
        "; No premise-selection trace and no target proof labels are inputs.",
        f"; Search policy: {policy_name}.",
        "; This is bounded proof search.  Exhaustion is INCOMPLETE, never refutation.",
        "; ============================================================================",
        "",
    ]
    for target in targets:
        variables = assertion_vars(target)
        ground = {name: f"setmm{target.index}.{name}" for name in variables}
        atoms = ["(: impl (-> Type Type Type))", "(: neg (-> Type Type))"]
        atoms.extend(f"(: {name} Type)" for name in ground.values())
        for assertion in theory_assertions(assertions, target, "full"):
            atoms.extend(metta_assertion_atoms(assertion))
        for number, premise in enumerate(target.premises, 1):
            atoms.append(
                f"(: setmm{target.index}.h{number} {metta_formula(premise, ground)})"
            )
        goal = metta_formula(target.conclusion, ground)
        query = (
            f"(SetMMPrimeSearch {target.label} full-prior-theory "
            f"(search-inhabitants $kb {goal} {depth} {fuel} 1{policy}))"
        )
        lines.extend([
            f"; index {target.index}: {target.label}",
            f"!{nested_initialization(atoms, query)}",
            "",
        ])
    lines.append(
        f"!(SetMMPrimeSearchSummary full-{policy_name} {len(targets)} "
        f"{targets[0].index} {targets[-1].index})"
    )
    return "\n".join(lines) + "\n"


def tptp_rule(assertion: Assertion) -> str:
    variables = assertion_vars(assertion)
    substitution = {name: upper_var(name) for name in variables}
    conclusion = f"proved({tptp_term(assertion.conclusion, substitution)})"
    if assertion.premises:
        premises = " & ".join(
            f"proved({tptp_term(item, substitution)})"
            for item in assertion.premises
        )
        body = f"(({premises}) => {conclusion})"
    else:
        body = conclusion
    if variables:
        body = f"! [{', '.join(substitution.values())}] : ({body})"
    return f"fof(rule_{safe_name(assertion.label)}, axiom, {body})."


def metta_resolution_rule(assertion: Assertion) -> str:
    """Render one assertion as a native-variable Horn clause.

    The resolution producer deliberately uses ordinary MeTTa variables.  Its
    library standardizes parent clauses apart and calls the runtime's native
    occurs-checked ``unify``; explicit ``ATP.Var`` terms remain reserved for
    replaying external proof certificates.
    """

    prefix = f"v_{safe_name(assertion.label)}_"
    substitution = {
        name: f"${prefix}{safe_name(name)}"
        for name in assertion_vars(assertion)
    }
    literals = [
        f"(ATP.Pos (proved {metta_formula(assertion.conclusion, substitution)}))"
    ]
    literals.extend(
        f"(ATP.Neg (proved {metta_formula(premise, substitution)}))"
        for premise in assertion.premises
    )
    return (
        f"(ATP.NamedClause {assertion.label} "
        f"({' '.join(literals)}))"
    )


def generate_resolution_metta(
    assertions: Sequence[Assertion],
    target: Assertion,
    source_digest: str,
    source_revision: str,
    max_steps: int,
    max_generated: int,
) -> str:
    """Generate an honest full-prior native-resolution search fixture."""

    filename = f"setmm_prime_resolution_{safe_name(target.label)}_full_v0.metta"
    ground = {
        name: f"setmm{target.index}.{name}"
        for name in assertion_vars(target)
    }
    usable = [
        metta_resolution_rule(assertion)
        for assertion in theory_assertions(assertions, target, "full")
    ]
    usable.extend(
        f"(ATP.NamedClause setmm{target.index}.h{number} "
        f"((ATP.Pos (proved {metta_formula(premise, ground)}))))"
        for number, premise in enumerate(target.premises, 1)
    )
    support = (
        f"((ATP.NamedClause setmm{target.index}.negated-target "
        f"((ATP.Neg (proved {metta_formula(target.conclusion, ground)})))))"
    )
    usable_block = "(\n      " + "\n      ".join(usable) + ")"
    lines = [
        "; ============================================================================",
        f"; {filename}",
        ";",
        "; GENERATED directly from the pinned CC0 set.mm source.",
        f"; set.mm revision: {source_revision}",
        f"; set.mm SHA-256: {source_digest}",
        f"; target: {target.label} (index {target.index})",
        "; Theory: every earlier provability assertion plus active hypotheses.",
        "; No target proof, reference support, or selected support is an input.",
        "; Native binary resolution uses ordinary MeTTa match/unify,",
        "; a signed-literal Atomspace index, and set of support.",
        "; Bounds are coverage limits; failure within them is INCOMPLETE.",
        "; ============================================================================",
        "",
        "!(import! &self lib_atp)",
        "",
        f"!(bind! &setmm-resolution-{safe_name(target.label)}",
        "  (atp:resolution-search:prove-indexed",
        f"    {usable_block}",
        f"    {support}",
        f"    (ATP.GivenClauseBounds {max_steps} {max_generated})",
        "    (ATP.AgeWeight 5 1)))",
        "",
        f"!(println! (SetMMPrimeResolutionSearch {target.label}",
        f"  full-prior-theory &setmm-resolution-{safe_name(target.label)}))",
    ]
    return "\n".join(lines) + "\n"


def tptp_hilbert_problem(assertions: Sequence[Assertion], target: Assertion,
                         policy: str, source_digest: str,
                         source_revision: str) -> str:
    ground = {name: f"f_{safe_name(name)}_{target.index}"
              for name in assertion_vars(target)}
    selected = theory_assertions(assertions, target, policy)
    lines = [
        f"% set.mm revision: {source_revision}",
        f"% set.mm SHA-256: {source_digest}",
        f"% target: {target.label} (index {target.index})",
        f"% theory policy: {policy}",
    ]
    if policy == "reference":
        lines.append("% Calibration only: theory labels come from the stored proof.")
    else:
        lines.append("% No target proof labels are inputs.")
    lines.extend(tptp_rule(item) for item in selected)
    for number, premise in enumerate(target.premises, 1):
        lines.append(
            f"fof(hypothesis_{number}, axiom, "
            f"proved({tptp_term(premise, ground)}))."
        )
    lines.append(
        f"fof(target, conjecture, proved({tptp_term(target.conclusion, ground)}))."
    )
    return "\n".join(lines) + "\n"


def tptp_semantic_problem(target: Assertion, source_digest: str,
                          source_revision: str) -> str:
    ground = {name: f"p_{safe_name(name)}_{target.index}"
              for name in assertion_vars(target)}
    lines = [
        f"% set.mm revision: {source_revision}",
        f"% set.mm SHA-256: {source_digest}",
        f"% semantic entailment target: {target.label} (index {target.index})",
        "% This tests intrinsic propositional difficulty, not Hilbert proof search.",
    ]
    for number, premise in enumerate(target.premises, 1):
        lines.append(
            f"fof(hypothesis_{number}, axiom, {semantic_formula(premise, ground)})."
        )
    lines.append(
        f"fof(target, conjecture, {semantic_formula(target.conclusion, ground)})."
    )
    return "\n".join(lines) + "\n"


def write_if_changed(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if not path.exists() or path.read_text(encoding="utf-8") != content:
        path.write_text(content, encoding="utf-8")


def manifest(assertions: Sequence[Assertion], targets: Sequence[Assertion],
             source: Path, source_digest: str, source_revision: str) -> dict:
    return {
        "schema": "setmm-prime-atp-manifest-v0",
        "source": {
            "kind": "CC0 set.mm",
            "path_argument_basename": source.name,
            "revision": source_revision,
            "sha256": source_digest,
        },
        "fragment": {
            "first_index": assertions[0].index,
            "last_index": assertions[-1].index,
            "assertion_count": len(assertions),
            "anchors": {str(index): label for index, label in EXPECTED_ANCHORS.items()},
        },
        "targets": [
            {
                "index": target.index,
                "label": target.label,
                "premise_count": len(target.premises),
                "prior_assertion_count": target.index - 2,
                "reference_provability_labels": [
                    label for label in target.proof_labels
                    if label in {item.label for item in assertions}
                ],
            }
            for target in targets
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--setmm", type=Path, required=True)
    parser.add_argument("--source-revision", required=True)
    parser.add_argument("--output-dir", type=Path, default=HERE)
    parser.add_argument("--targets", nargs="+", default=list(DEFAULT_TARGETS))
    parser.add_argument("--depth", type=int, default=12)
    parser.add_argument("--fuel", type=int, default=250_000)
    parser.add_argument("--resolution-steps", type=int, default=1_000)
    parser.add_argument("--resolution-generated", type=int, default=5_000)
    args = parser.parse_args()

    source_bytes = args.setmm.read_bytes()
    source_digest = hashlib.sha256(source_bytes).hexdigest()
    assertions = extract_assertions(source_bytes.decode("utf-8"))
    by_label = {item.label: item for item in assertions}
    missing = [label for label in args.targets if label not in by_label]
    if missing:
        raise SystemExit(f"target labels absent from extracted fragment: {missing}")
    targets = [by_label[label] for label in args.targets]
    targets.sort(key=lambda item: item.index)

    output = args.output_dir
    write_if_changed(
        output / "setmm_prime_full_181_183_v0.metta",
        generate_metta(assertions, targets, source_digest,
                       args.source_revision, args.depth, args.fuel, False),
    )
    write_if_changed(
        output / "setmm_prime_atp_guided_181_183_v0.metta",
        generate_metta(assertions, targets, source_digest,
                       args.source_revision, args.depth, args.fuel, True),
    )
    tptp_dir = output / "tptp"
    for target in targets:
        stem = safe_name(target.label)
        write_if_changed(
            output / f"setmm_prime_resolution_{stem}_full_v0.metta",
            generate_resolution_metta(
                assertions, target, source_digest, args.source_revision,
                args.resolution_steps, args.resolution_generated,
            ),
        )
        write_if_changed(
            tptp_dir / f"{stem}_semantic.p",
            tptp_semantic_problem(target, source_digest, args.source_revision),
        )
        for policy in ("core", "full", "reference"):
            write_if_changed(
                tptp_dir / f"{stem}_hilbert_{policy}.p",
                tptp_hilbert_problem(assertions, target, policy,
                                     source_digest, args.source_revision),
            )
    write_if_changed(
        output / "setmm_prime_atp_manifest.json",
        json.dumps(manifest(assertions, targets, args.setmm, source_digest,
                            args.source_revision), indent=2, sort_keys=True) + "\n",
    )
    print(
        f"extracted {len(assertions)} CC0 set.mm assertions; generated "
        f"Prime and TPTP fixtures for {len(targets)} targets"
    )


if __name__ == "__main__":
    main()
