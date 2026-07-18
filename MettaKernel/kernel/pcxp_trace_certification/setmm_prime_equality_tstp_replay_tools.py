#!/usr/bin/env python3
"""Generate Prime replay for a tiny external-ATP equality proof.

The reader covers the ground first-order TSTP fragment used by the equality
transport conformance rung.  It checks E's rewriting proof and Vampire's
explicit superposition proof, derives the rewrite direction and position, and
emits a deterministic MeTTa certificate fixture.  This generator is not a
trusted checker; the generated substitution, KBO side condition, rewrite, and
final resolution step are replayed again by Prime's imported ATP library.
"""

from __future__ import annotations

import argparse
import dataclasses
import re
import subprocess
import sys
from pathlib import Path
from typing import Iterable


@dataclasses.dataclass(frozen=True)
class Term:
    name: str
    arguments: tuple["Term", ...] = ()


@dataclasses.dataclass(frozen=True)
class Formula:
    kind: str
    positive: bool = True
    atom: Term | None = None
    left: Term | None = None
    right: Term | None = None


@dataclasses.dataclass(frozen=True)
class Statement:
    name: str
    formula: Formula
    annotation: str
    rule: str | None
    parents: tuple[str, ...] = ()


@dataclasses.dataclass(frozen=True)
class EqualityProof:
    producer_rule: str
    equality: Formula
    target: Formula
    child: Formula
    fact: Formula
    direction: str
    path: tuple[int, ...]
    from_term: Term
    to_term: Term


TOKEN = re.compile(r"\s*(\$?[A-Za-z][A-Za-z0-9_]*|[(),=~])")
IDENT = re.compile(r"\b[A-Za-z][A-Za-z0-9_]*\b")


class TokenStream:
    def __init__(self, text: str) -> None:
        self.tokens: list[str] = []
        position = 0
        while position < len(text):
            match = TOKEN.match(text, position)
            if not match:
                raise ValueError(
                    f"unsupported ground-TSTP token near {text[position:position + 24]!r}"
                )
            self.tokens.append(match.group(1))
            position = match.end()
        self.index = 0

    def peek(self) -> str | None:
        return self.tokens[self.index] if self.index < len(self.tokens) else None

    def take(self, expected: str | None = None) -> str:
        token = self.peek()
        if token is None:
            raise ValueError("unexpected end of formula")
        if expected is not None and token != expected:
            raise ValueError(f"expected {expected!r}, got {token!r}")
        self.index += 1
        return token


def split_top_level(text: str, separator: str = ",") -> list[str]:
    fields: list[str] = []
    depth = 0
    quote: str | None = None
    start = 0
    for index, char in enumerate(text):
        if quote is not None:
            if char == quote and (index == 0 or text[index - 1] != "\\"):
                quote = None
            continue
        if char in "'\"":
            quote = char
        elif char in "([":
            depth += 1
        elif char in ")]":
            depth -= 1
        elif char == separator and depth == 0:
            fields.append(text[start:index].strip())
            start = index + 1
    fields.append(text[start:].strip())
    return fields


def strip_outer_parentheses(text: str) -> str:
    result = text.strip()
    while result.startswith("(") and result.endswith(")"):
        depth = 0
        encloses_all = True
        for index, char in enumerate(result):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth == 0 and index != len(result) - 1:
                    encloses_all = False
                    break
        if not encloses_all or depth != 0:
            break
        result = result[1:-1].strip()
    return result


def parse_term(tokens: TokenStream) -> Term:
    name = tokens.take()
    if name in {"(", ")", ",", "=", "~"}:
        raise ValueError(f"expected term symbol, got {name!r}")
    if name[0].isupper():
        raise ValueError("this conformance rung deliberately requires ground terms")
    arguments: list[Term] = []
    if tokens.peek() == "(":
        tokens.take("(")
        if tokens.peek() != ")":
            while True:
                arguments.append(parse_term(tokens))
                if tokens.peek() != ",":
                    break
                tokens.take(",")
        tokens.take(")")
    return Term(name, tuple(arguments))


def parse_formula(text: str) -> Formula:
    body = strip_outer_parentheses(text)
    if body == "$false":
        return Formula("false")
    tokens = TokenStream(body)
    positive = tokens.peek() != "~"
    if not positive:
        tokens.take("~")
    left = parse_term(tokens)
    if tokens.peek() == "=":
        if not positive:
            raise ValueError("negative equality is outside this first rung")
        tokens.take("=")
        right = parse_term(tokens)
        if tokens.peek() is not None:
            raise ValueError("trailing tokens after equality")
        return Formula("equality", left=left, right=right)
    if tokens.peek() is not None:
        raise ValueError(f"trailing tokens after literal: {tokens.tokens[tokens.index:]}")
    return Formula("literal", positive=positive, atom=left)


def proof_lines(text: str) -> list[str]:
    inside = False
    pending: list[str] = []
    depth = 0
    result: list[str] = []
    for raw in text.splitlines():
        line = raw.strip()
        if "SZS output start" in line and (
            "CNFRefutation" in line or "Proof" in line
        ):
            inside = True
            continue
        if inside and "SZS output end" in line:
            break
        if not inside:
            continue
        if not pending and not (line.startswith("fof(") or line.startswith("cnf(")):
            continue
        pending.append(line)
        depth += line.count("(") - line.count(")")
        if depth == 0 and line.endswith("."):
            result.append(" ".join(pending))
            pending = []
    if pending:
        raise ValueError("unterminated TSTP statement")
    if not result:
        raise ValueError("no TSTP proof block found")
    return result


def parse_statements(text: str) -> dict[str, Statement]:
    provisional: list[Statement] = []
    for line in proof_lines(text):
        _kind, rest = line.split("(", 1)
        if not rest.endswith(")."):
            raise ValueError(f"malformed TSTP statement: {line}")
        fields = split_top_level(rest[:-2])
        if len(fields) < 3:
            raise ValueError(f"missing TSTP fields: {line}")
        name, _role, formula_text = fields[:3]
        annotation = ",".join(fields[3:])
        rule_match = re.search(r"inference\(\s*([A-Za-z0-9_]+)\s*,", annotation)
        provisional.append(
            Statement(
                name,
                parse_formula(formula_text),
                annotation,
                rule_match.group(1) if rule_match else None,
            )
        )
    names = {statement.name for statement in provisional}
    result: dict[str, Statement] = {}
    for statement in provisional:
        parents: list[str] = []
        for token in IDENT.findall(statement.annotation):
            if token in names and token != statement.name and token not in parents:
                parents.append(token)
        result[statement.name] = dataclasses.replace(
            statement, parents=tuple(parents)
        )
    return result


def term_differences(
    left: Term, right: Term, path: tuple[int, ...] = ()
) -> list[tuple[tuple[int, ...], Term, Term]]:
    if left == right:
        return []
    if left.name == right.name and len(left.arguments) == len(right.arguments):
        differences: list[tuple[tuple[int, ...], Term, Term]] = []
        for index, (left_arg, right_arg) in enumerate(
            zip(left.arguments, right.arguments), 1
        ):
            differences.extend(
                term_differences(left_arg, right_arg, path + (index,))
            )
        return differences
    return [(path, left, right)]


def require_unique(items: Iterable[Statement], description: str) -> Statement:
    values = list(items)
    if len(values) != 1:
        raise ValueError(f"expected one {description}, found {len(values)}")
    return values[0]


def validate_proof(text: str, expected_rule: str) -> EqualityProof:
    statements = parse_statements(text)
    rewrite = require_unique(
        (
            statement
            for statement in statements.values()
            if statement.rule == expected_rule
        ),
        f"{expected_rule} inference",
    )
    if rewrite.formula.kind != "literal" or rewrite.formula.positive:
        raise ValueError("equality inference must derive a negative literal")
    parent_statements = [statements[parent] for parent in rewrite.parents]
    equality = require_unique(
        (parent for parent in parent_statements if parent.formula.kind == "equality"),
        "equality parent",
    )
    target = require_unique(
        (
            parent
            for parent in parent_statements
            if parent.formula.kind == "literal" and not parent.formula.positive
        ),
        "negative target parent",
    )
    assert equality.formula.left is not None and equality.formula.right is not None
    assert target.formula.atom is not None and rewrite.formula.atom is not None
    differences = term_differences(target.formula.atom, rewrite.formula.atom)
    if len(differences) != 1:
        raise ValueError("equality inference must perform exactly one term replacement")
    path, from_term, to_term = differences[0]
    if not path:
        raise ValueError("rewriting an entire predicate atom is not superposition")
    if (
        from_term == equality.formula.left
        and to_term == equality.formula.right
    ):
        direction = "ATP.LeftToRight"
    elif (
        from_term == equality.formula.right
        and to_term == equality.formula.left
    ):
        direction = "ATP.RightToLeft"
    else:
        raise ValueError("derived child is not a parent-equality replacement")

    final = require_unique(
        (
            statement
            for statement in statements.values()
            if statement.formula.kind == "false"
        ),
        "empty-clause conclusion",
    )
    final_parents = [statements[parent] for parent in final.parents]
    if rewrite.name not in final.parents:
        raise ValueError("empty clause does not depend on the equality child")
    fact = require_unique(
        (
            parent
            for parent in final_parents
            if parent.formula.kind == "literal" and parent.formula.positive
        ),
        "positive resolution parent",
    )
    if fact.formula.atom != rewrite.formula.atom:
        raise ValueError("final resolution parents are not complementary")
    if not any(
        statement.formula.kind == "literal"
        and statement.formula.positive
        and statement.formula.atom == target.formula.atom
        for statement in statements.values()
    ):
        raise ValueError("positive conjecture is absent from proof ancestry")
    return EqualityProof(
        expected_rule,
        equality.formula,
        target.formula,
        rewrite.formula,
        fact.formula,
        direction,
        path,
        from_term,
        to_term,
    )


def metta_term(term: Term) -> str:
    if not term.arguments:
        return term.name
    return f"({term.name} {' '.join(metta_term(arg) for arg in term.arguments)})"


def metta_literal(formula: Formula) -> str:
    if formula.kind != "literal" or formula.atom is None:
        raise ValueError("expected predicate literal")
    sign = "ATP.Pos" if formula.positive else "ATP.Neg"
    return f"({sign} {metta_term(formula.atom)})"


def metta_equality(formula: Formula) -> str:
    if formula.kind != "equality" or formula.left is None or formula.right is None:
        raise ValueError("expected equality")
    return f"(ATP.Pos (ATP.Eq {metta_term(formula.left)} {metta_term(formula.right)}))"


def precedence_symbols(model: EqualityProof) -> list[str]:
    symbols = [model.from_term.name, model.to_term.name]
    if model.target.atom is not None:
        symbols.append(model.target.atom.name)
    symbols.append("ATP.Eq")
    result: list[str] = []
    for symbol in symbols:
        if symbol not in result:
            result.append(symbol)
    return result


def build_replay(e_text: str, vampire_text: str) -> str:
    e_model = validate_proof(e_text, "rw")
    vampire_model = validate_proof(vampire_text, "superposition")
    comparable_e = dataclasses.replace(e_model, producer_rule="shared")
    comparable_v = dataclasses.replace(vampire_model, producer_rule="shared")
    if comparable_e != comparable_v:
        raise ValueError("E and Vampire equality derivations disagree structurally")
    model = vampire_model
    assert model.equality.left is not None and model.equality.right is not None
    assert model.target.atom is not None and model.child.atom is not None
    source_clause = f"({metta_equality(model.equality)})"
    target_literal = metta_literal(model.target)
    target_clause = f"({target_literal})"
    child_literal = metta_literal(model.child)
    child_clause = f"({child_literal})"
    fact_literal = metta_literal(model.fact)
    position = " ".join(str(index) for index in model.path)
    precedence = " ".join(precedence_symbols(model))
    opposite = (
        "ATP.RightToLeft"
        if model.direction == "ATP.LeftToRight"
        else "ATP.LeftToRight"
    )
    wrong_index = model.path[0] + 1
    wrong_precedence = " ".join(
        [model.to_term.name, model.from_term.name]
        + precedence_symbols(model)[2:]
    )
    left = metta_term(model.equality.left)
    right = metta_term(model.equality.right)
    predicate = model.target.atom.name
    from_text = metta_term(model.from_term)
    to_text = metta_term(model.to_term)

    lines = [
        "; Generated from actual E and Vampire TSTP equality proofs.",
        "; E normalizes the step as rw; Vampire exposes it as superposition.",
        "; Both derive the same child, direction, position, and final refutation.",
        "!(import! &self lib_atp)",
        "",
        f"!(bind! &external-equality-kbo (ATP.KBO 1 1 () ({precedence})))",
        f"!(bind! &external-equality {source_clause})",
        f"!(bind! &external-target {target_clause})",
        f"!(bind! &external-child {child_clause})",
        "",
        "!(assertEqual",
        "  (atp:kbo:config-valid &external-equality-kbo)",
        "  True)",
        "!(assertEqual",
        f"  (atp:kbo:greater &external-equality-kbo {from_text} {to_text})",
        "  True)",
        "!(assertEqual",
        "  (atp:superposition:check-unit-step",
        "    &external-equality &external-target (ATP.Subst ())",
        f"    {metta_equality(model.equality)} {model.direction}",
        f"    {target_literal} (ATP.Position ({position}))",
        "    &external-equality-kbo &external-child)",
        "  True)",
        "!(assertEqual",
        "  (atp:resolution:check-step",
        f"    &external-child ({fact_literal}) (ATP.Subst ())",
        f"    {child_literal} {fact_literal} ())",
        "  True)",
        "",
        "; Reversing the certified equality direction violates KBO.",
        "!(assertEqual",
        "  (atp:superposition:check-unit-step",
        "    &external-equality &external-target (ATP.Subst ())",
        f"    {metta_equality(model.equality)} {opposite}",
        f"    {target_literal} (ATP.Position ({position}))",
        "    &external-equality-kbo &external-child)",
        "  False)",
        "; A changed child is not the supplied-position replacement.",
        "!(assertEqual",
        "  (atp:superposition:check-unit-step",
        "    &external-equality &external-target (ATP.Subst ())",
        f"    {metta_equality(model.equality)} {model.direction}",
        f"    {target_literal} (ATP.Position ({position}))",
        "    &external-equality-kbo ((ATP.Neg (forged))))",
        "  False)",
        "; A changed position is rejected.",
        "!(assertEqual",
        "  (atp:superposition:check-unit-step",
        "    &external-equality &external-target (ATP.Subst ())",
        f"    {metta_equality(model.equality)} {model.direction}",
        f"    {target_literal} (ATP.Position ({wrong_index}))",
        "    &external-equality-kbo &external-child)",
        "  False)",
        "; A reversed precedence cannot justify the observed orientation.",
        "!(assertEqual",
        "  (atp:superposition:check-unit-step",
        "    &external-equality &external-target (ATP.Subst ())",
        f"    {metta_equality(model.equality)} {model.direction}",
        f"    {target_literal} (ATP.Position ({position}))",
        f"    (ATP.KBO 1 1 () ({wrong_precedence})) &external-child)",
        "  False)",
        "; Cyclic substitution evidence fails before replay.",
        "!(assertEqual",
        "  (atp:superposition:check-unit-step",
        "    &external-equality &external-target",
        "    (ATP.Subst ((ATP.Bind x (ATP.Var y)) (ATP.Bind y (ATP.Var x))))",
        f"    {metta_equality(model.equality)} {model.direction}",
        f"    {target_literal} (ATP.Position ({position}))",
        "    &external-equality-kbo &external-child)",
        "  False)",
        "; An original variable target position is forbidden.",
        "!(assertEqual",
        "  (atp:superposition:check-unit-step",
        f"    &external-equality ((ATP.Neg ({predicate} (ATP.Var x))))",
        f"    (ATP.Subst ((ATP.Bind x {from_text})))",
        f"    {metta_equality(model.equality)} {model.direction}",
        f"    (ATP.Neg ({predicate} (ATP.Var x))) (ATP.Position ({position}))",
        "    &external-equality-kbo &external-child)",
        "  False)",
        "",
        "; Reconstruct an ordinary proof term for Prime's unchanged checker.",
        "!(bind! &external-equality-kb (new-space))",
        "!(add-atom &external-equality-kb (: Obj Type))",
        f"!(add-atom &external-equality-kb (: {left} Obj))",
        f"!(add-atom &external-equality-kb (: {right} Obj))",
        "!(add-atom &external-equality-kb (: EqT (-> Obj Obj Type)))",
        "!(add-atom &external-equality-kb (: Pred (-> Obj Type)))",
        f"!(add-atom &external-equality-kb (: eq-proof (EqT {left} {right})))",
        f"!(add-atom &external-equality-kb (: fact-proof (Pred {left})))",
        "!(add-atom &external-equality-kb",
        "  (: equality-substitution",
        "    (-> (EqT $left $right) (Pred $left) (Pred $right))))",
        "!(assertEqual",
        "  (check-type &external-equality-kb",
        "    (equality-substitution eq-proof fact-proof)",
        f"    (Pred {right}) 100000)",
        f"  (he-accept (exact (Pred {right}))))",
        "",
        "!(println!",
        "  (SetMMPrimeExternalEqualityReplaySummary",
        "    equality_transport 2 11 11 0))",
        "",
    ]
    return "\n".join(lines)


def run_e(executable: Path, problem: Path, cpu_limit: int) -> str:
    completed = subprocess.run(
        [
            str(executable),
            "--auto",
            f"--cpu-limit={cpu_limit}",
            "--tstp-format",
            "--proof-object",
            str(problem),
        ],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if "% SZS status Theorem" not in completed.stdout:
        raise RuntimeError(f"E did not prove {problem.name} (exit {completed.returncode})")
    return completed.stdout


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
            "--function_definition_elimination",
            "none",
            "--function_definition_rewriting",
            "off",
            "--forward_demodulation",
            "off",
            "--backward_demodulation",
            "off",
            "--forward_subsumption_demodulation",
            "off",
            "--backward_subsumption_demodulation",
            "off",
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


def require_rejected(text: str, expected_rule: str, old: str, new: str) -> None:
    mutation = text.replace(old, new, 1)
    if mutation == text:
        raise ValueError(f"self-test mutation did not match {old!r}")
    try:
        validate_proof(mutation, expected_rule)
    except ValueError:
        return
    raise ValueError(f"self-test mutation survived: {old!r} -> {new!r}")


def self_test(e_text: str, vampire_text: str) -> None:
    require_rejected(e_text, "rw", "inference(rw", "inference(resolution")
    require_rejected(e_text, "rw", "[c_0_5, c_0_6]", "[c_0_5, c_0_7]")
    require_rejected(e_text, "rw", "(~p(a)), inference(rw", "(~p(c)), inference(rw")
    require_rejected(
        vampire_text,
        "superposition",
        "inference(superposition",
        "inference(resolution",
    )
    require_rejected(vampire_text, "superposition", "[f8,f6]", "[f8,f7]")
    require_rejected(
        vampire_text,
        "superposition",
        "  ~p(a)),\n  inference(superposition",
        "  ~p(c)),\n  inference(superposition",
    )


def main() -> int:
    root = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--e-proof",
        type=Path,
        default=root / "tptp/equality_transport_v0_e_refutation.tstp",
    )
    parser.add_argument(
        "--vampire-proof",
        type=Path,
        default=root
        / "tptp/equality_transport_v0_vampire_superposition_refutation.tstp",
    )
    parser.add_argument(
        "--problem", type=Path, default=root / "tptp/equality_transport_v0.p"
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=root / "setmm_prime_external_equality_replay_v0.metta",
    )
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--live-e", type=Path)
    parser.add_argument("--live-vampire", type=Path)
    parser.add_argument("--limit", type=int, default=5)
    args = parser.parse_args()
    if not any(
        [args.write, args.check, args.self_test, args.live_e, args.live_vampire]
    ):
        parser.error("choose --write, --check, --self-test, or a live ATP")

    e_text = args.e_proof.read_text()
    vampire_text = args.vampire_proof.read_text()
    generated = build_replay(e_text, vampire_text)
    if args.write:
        args.output.write_text(generated)
        print(f"PASS: wrote {args.output.name}")
    if args.check:
        if not args.output.exists() or args.output.read_text() != generated:
            print(
                f"FAIL: {args.output.name} is not the deterministic replay",
                file=sys.stderr,
            )
            return 1
        print(f"PASS: {args.output.name} is deterministic")
    if args.self_test:
        self_test(e_text, vampire_text)
        print("PASS: six equality-TSTP extractor mutations rejected")
    live_e_text = (
        run_e(args.live_e, args.problem, args.limit) if args.live_e else e_text
    )
    live_vampire_text = (
        run_vampire(args.live_vampire, args.problem, args.limit)
        if args.live_vampire
        else vampire_text
    )
    if args.live_e or args.live_vampire:
        if build_replay(live_e_text, live_vampire_text) != generated:
            print("FAIL: live ATP proof does not reproduce replay", file=sys.stderr)
            return 1
        print("PASS: live E and Vampire equality proofs reproduce Prime replay")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
