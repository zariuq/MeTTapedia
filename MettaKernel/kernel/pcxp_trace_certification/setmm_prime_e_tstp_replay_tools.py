#!/usr/bin/env python3
"""Generate a Prime replay from E's TSTP proof of the public set.mm theorem ja.

The parser intentionally covers only the first-order CNF fragment used by this
fixture.  It identifies E's actual proof parents, independently recomputes each
binary resolvent with an occurs-checking unifier, and reconstructs the direct
Horn proof term.  Neither the parser nor its unifier is trusted: the generated
MeTTa fixture applies every explicit substitution again and sends the rebuilt
proof term through Prime's ordinary type checker.
"""

from __future__ import annotations

import argparse
import dataclasses
import itertools
import re
import subprocess
import sys
from pathlib import Path
from typing import Iterable, Iterator, Mapping, Sequence


@dataclasses.dataclass(frozen=True)
class Term:
    name: str
    args: tuple["Term", ...] = ()
    variable: bool = False


@dataclasses.dataclass(frozen=True)
class Literal:
    positive: bool
    atom: Term


Clause = tuple[Literal, ...]


@dataclasses.dataclass(frozen=True)
class Statement:
    order: int
    kind: str
    name: str
    role: str
    formula: str
    annotation: str
    clause: Clause | None
    parents: tuple[str, ...] = ()
    source_label: str | None = None


@dataclasses.dataclass(frozen=True)
class ProofExpr:
    name: str
    args: tuple["ProofExpr", ...] = ()
    hole: bool = False


@dataclasses.dataclass(frozen=True)
class AnnotatedLiteral:
    literal: Literal
    hole: str | None = None


@dataclasses.dataclass(frozen=True)
class AnnotatedClause:
    entries: tuple[AnnotatedLiteral, ...]
    proof: ProofExpr | None

    @property
    def clause(self) -> Clause:
        return tuple(entry.literal for entry in self.entries)


@dataclasses.dataclass(frozen=True)
class ResolutionStep:
    left: str
    right: str
    result: str
    left_clause: AnnotatedClause
    right_clause: AnnotatedClause
    result_clause: AnnotatedClause
    substitution: tuple[tuple[Term, Term], ...]
    left_pivot: Literal
    right_pivot: Literal


TOKEN = re.compile(r"\s*(\$?[A-Za-z][A-Za-z0-9_]*|[(),|~])")
IDENT = re.compile(r"\b(?:[A-Za-z][A-Za-z0-9_]*|c_0_[0-9]+)\b")


class TokenStream:
    def __init__(self, text: str) -> None:
        self.tokens: list[str] = []
        position = 0
        while position < len(text):
            match = TOKEN.match(text, position)
            if not match:
                raise ValueError(f"unsupported TPTP token near {text[position:position + 32]!r}")
            self.tokens.append(match.group(1))
            position = match.end()
        self.index = 0

    def peek(self) -> str | None:
        return self.tokens[self.index] if self.index < len(self.tokens) else None

    def take(self, expected: str | None = None) -> str:
        token = self.peek()
        if token is None:
            raise ValueError("unexpected end of TPTP formula")
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
        if quote:
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
    if name in {"(", ")", ",", "|", "~"}:
        raise ValueError(f"expected term symbol, got {name!r}")
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
    return Term(name, tuple(arguments), bool(name and name[0].isupper()))


def parse_clause(formula: str) -> Clause:
    body = strip_outer_parentheses(formula)
    if body == "$false":
        return ()
    tokens = TokenStream(body)
    literals: list[Literal] = []
    while True:
        positive = tokens.peek() != "~"
        if not positive:
            tokens.take("~")
        literals.append(Literal(positive, parse_term(tokens)))
        if tokens.peek() != "|":
            break
        tokens.take("|")
    if tokens.peek() is not None:
        raise ValueError(f"trailing tokens in CNF formula: {tokens.tokens[tokens.index:]}")
    return tuple(literals)


def parse_clausal_formula(formula: str) -> Clause | None:
    body = strip_outer_parentheses(formula)
    if body.startswith("!"):
        colon = body.find(":")
        if colon < 0:
            return None
        body = strip_outer_parentheses(body[colon + 1 :])
    if "=>" in body or "&" in body or "<=>" in body:
        return None
    try:
        return parse_clause(body)
    except ValueError:
        return None


def proof_lines(text: str) -> list[str]:
    inside = False
    result: list[str] = []
    pending: list[str] = []
    depth = 0
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
    if not result:
        raise ValueError("no CNFRefutation proof block found")
    if pending:
        raise ValueError("unterminated statement in proof block")
    return result


def parse_statements(text: str) -> list[Statement]:
    provisional: list[Statement] = []
    for order, line in enumerate(proof_lines(text)):
        kind, rest = line.split("(", 1)
        if not rest.endswith(")."):
            raise ValueError(f"TSTP statement is not a single complete line: {line}")
        fields = split_top_level(rest[:-2])
        if len(fields) < 3:
            raise ValueError(f"malformed TSTP statement: {line}")
        name, role, formula = fields[:3]
        annotation = ",".join(fields[3:])
        source_match = re.search(r"file\([^,]+,\s*([A-Za-z][A-Za-z0-9_]*)\s*\)", annotation)
        provisional.append(
            Statement(
                order,
                kind,
                name,
                role,
                formula,
                annotation,
                parse_clausal_formula(formula),
                source_label=source_match.group(1) if source_match else None,
            )
        )
    names = {statement.name for statement in provisional}
    result: list[Statement] = []
    for statement in provisional:
        parents: list[str] = []
        for token in IDENT.findall(statement.annotation):
            if token in names and token != statement.name and token not in parents:
                parents.append(token)
        result.append(dataclasses.replace(statement, parents=tuple(parents)))
    return result


def ancestry(statements: Mapping[str, Statement], name: str, memo: dict[str, frozenset[str]]) -> frozenset[str]:
    if name in memo:
        return memo[name]
    statement = statements[name]
    if not statement.parents:
        answer = frozenset({statement.source_label or name})
    else:
        answer = frozenset().union(*(ancestry(statements, parent, memo) for parent in statement.parents))
    memo[name] = answer
    return answer


def rename_term(term: Term, prefix: str, names: dict[str, Term]) -> Term:
    if term.variable:
        if term.name not in names:
            names[term.name] = Term(f"{prefix}_v{len(names)}", variable=True)
        return names[term.name]
    return Term(term.name, tuple(rename_term(arg, prefix, names) for arg in term.args))


def rename_clause(clause: Clause, prefix: str) -> Clause:
    names: dict[str, Term] = {}
    return tuple(Literal(literal.positive, rename_term(literal.atom, prefix, names)) for literal in clause)


def walk(term: Term, substitution: Mapping[Term, Term]) -> Term:
    seen: set[Term] = set()
    current = term
    while current.variable and current in substitution:
        if current in seen:
            raise ValueError("cyclic substitution produced by unifier")
        seen.add(current)
        current = substitution[current]
    return current


def occurs(variable: Term, term: Term, substitution: Mapping[Term, Term]) -> bool:
    term = walk(term, substitution)
    return term == variable or any(occurs(variable, arg, substitution) for arg in term.args)


def unify(left: Term, right: Term) -> dict[Term, Term] | None:
    substitution: dict[Term, Term] = {}
    pending = [(left, right)]
    while pending:
        lhs, rhs = pending.pop()
        lhs = walk(lhs, substitution)
        rhs = walk(rhs, substitution)
        if lhs == rhs:
            continue
        if lhs.variable:
            if occurs(lhs, rhs, substitution):
                return None
            substitution[lhs] = rhs
            continue
        if rhs.variable:
            if occurs(rhs, lhs, substitution):
                return None
            substitution[rhs] = lhs
            continue
        if lhs.name != rhs.name or len(lhs.args) != len(rhs.args):
            return None
        pending.extend(zip(lhs.args, rhs.args))
    return {key: apply_term(value, substitution) for key, value in substitution.items()}


def apply_term(term: Term, substitution: Mapping[Term, Term]) -> Term:
    root = walk(term, substitution)
    if root.variable:
        return root
    return Term(root.name, tuple(apply_term(arg, substitution) for arg in root.args))


def apply_literal(literal: Literal, substitution: Mapping[Term, Term]) -> Literal:
    return Literal(literal.positive, apply_term(literal.atom, substitution))


def replace_hole(proof: ProofExpr, hole: str, replacement: ProofExpr) -> ProofExpr:
    if proof.hole:
        return replacement if proof.name == hole else proof
    return ProofExpr(proof.name, tuple(replace_hole(arg, hole, replacement) for arg in proof.args))


def source_clause(clause: Clause, source_name: str) -> AnnotatedClause:
    entries: list[AnnotatedLiteral] = []
    holes: list[str] = []
    positives = 0
    for index, literal in enumerate(clause):
        if literal.positive:
            positives += 1
            entries.append(AnnotatedLiteral(literal))
        else:
            hole = f"{source_name}_h{index}"
            holes.append(hole)
            entries.append(AnnotatedLiteral(literal, hole))
    if positives > 1:
        raise ValueError(f"{source_name}: source clause is not Horn")
    proof = None
    if positives == 1:
        proof = ProofExpr(source_name, tuple(ProofExpr(hole, hole=True) for hole in holes))
    return AnnotatedClause(tuple(entries), proof)


def resolution_candidates(left: AnnotatedClause, right: AnnotatedClause) -> Iterator[tuple[AnnotatedClause, dict[Term, Term], Literal, Literal]]:
    for left_index, left_entry in enumerate(left.entries):
        for right_index, right_entry in enumerate(right.entries):
            if left_entry.literal.positive == right_entry.literal.positive:
                continue
            substitution = unify(left_entry.literal.atom, right_entry.literal.atom)
            if substitution is None:
                continue
            left_entries = [
                AnnotatedLiteral(apply_literal(entry.literal, substitution), entry.hole)
                for index, entry in enumerate(left.entries)
                if index != left_index
            ]
            right_entries = [
                AnnotatedLiteral(apply_literal(entry.literal, substitution), entry.hole)
                for index, entry in enumerate(right.entries)
                if index != right_index
            ]
            if left_entry.literal.positive:
                provider, consumer, consumer_entry = left, right, right_entry
            else:
                provider, consumer, consumer_entry = right, left, left_entry
            proof = consumer.proof
            if proof is not None:
                if provider.proof is None or consumer_entry.hole is None:
                    raise ValueError("Horn proof annotation is inconsistent with the pivot")
                proof = replace_hole(proof, consumer_entry.hole, provider.proof)
            yield (
                AnnotatedClause(tuple(left_entries + right_entries), proof),
                substitution,
                left_entry.literal,
                right_entry.literal,
            )


def canonical_term(term: Term, variables: dict[str, str]) -> str:
    if term.variable:
        if term.name not in variables:
            variables[term.name] = f"V{len(variables)}"
        return variables[term.name]
    if not term.args:
        return term.name
    return f"{term.name}({','.join(canonical_term(arg, variables) for arg in term.args)})"


def canonical_clause(clause: Clause) -> str:
    if not clause:
        return "$false"
    variants: list[str] = []
    for permutation in itertools.permutations(clause):
        variables: dict[str, str] = {}
        variants.append(
            "|".join(
                ("+" if literal.positive else "-") + canonical_term(literal.atom, variables)
                for literal in permutation
            )
        )
    return min(variants)


def select_resolution(left: AnnotatedClause, right: AnnotatedClause, expected: Clause, label: str) -> tuple[AnnotatedClause, dict[Term, Term], Literal, Literal]:
    matches = [
        candidate
        for candidate in resolution_candidates(left, right)
        if canonical_clause(candidate[0].clause) == canonical_clause(expected)
    ]
    if len(matches) != 1:
        raise ValueError(f"{label}: expected one matching resolvent, found {len(matches)}")
    return matches[0]


def find_source_cnf(statements: Sequence[Statement], source: str, predicate) -> Statement:
    by_name = {statement.name: statement for statement in statements}
    memo: dict[str, frozenset[str]] = {}
    candidates = [
        statement
        for statement in statements
        if statement.clause is not None
        and ancestry(by_name, statement.name, memo) == frozenset({source})
        and predicate(statement.clause)
    ]
    if not candidates:
        raise ValueError(f"no CNF descendant found for {source}")
    active = [
        candidate
        for candidate in candidates
        if any(
            candidate.name in statement.parents
            and any(
                inference in statement.annotation
                for inference in ("inference(spm", "inference(resolution", "inference(forward_subsumption_resolution")
            )
            for statement in statements
        )
    ]
    return min(active or candidates, key=lambda statement: statement.order)


def direct_child(statements: Sequence[Statement], left: str, right: str) -> Statement:
    candidates = [
        statement
        for statement in statements
        if statement.clause is not None
        and left in statement.parents
        and right in statement.parents
    ]
    if len(candidates) != 1:
        raise ValueError(f"expected one TSTP child of {left}, {right}; found {len(candidates)}")
    return candidates[0]


def metta_term(term: Term, typed: bool = False) -> str:
    if term.variable:
        return f"${term.name}" if typed else f"(ATP.Var {term.name})"
    if not term.args:
        return term.name
    return f"({term.name} {' '.join(metta_term(arg, typed) for arg in term.args)})"


def metta_literal(literal: Literal) -> str:
    sign = "ATP.Pos" if literal.positive else "ATP.Neg"
    return f"({sign} {metta_term(literal.atom)})"


def metta_clause(clause: Clause) -> str:
    return "(" + " ".join(metta_literal(literal) for literal in clause) + ")"


def metta_substitution(substitution: Sequence[tuple[Term, Term]]) -> str:
    if not substitution:
        return "(ATP.Subst ())"
    bindings = " ".join(
        f"(ATP.Bind {variable.name} {metta_term(term)})" for variable, term in substitution
    )
    return f"(ATP.Subst ({bindings}))"


def metta_proof(proof: ProofExpr) -> str:
    if proof.hole:
        raise ValueError(f"unfilled proof hole: {proof.name}")
    if not proof.args:
        return proof.name
    return f"({proof.name} {' '.join(metta_proof(arg) for arg in proof.args)})"


def unwrap_proved(literal: Literal) -> Term:
    if literal.atom.name != "proved" or len(literal.atom.args) != 1:
        raise ValueError("Hilbert clause literal is not proved(term)")
    return literal.atom.args[0]


def object_constants(clauses: Iterable[Clause]) -> list[str]:
    constants: set[str] = set()

    def visit(term: Term) -> None:
        if term.variable:
            return
        if not term.args and term.name not in {"proved", "imp", "neg"}:
            constants.add(term.name)
        for argument in term.args:
            visit(argument)

    for clause in clauses:
        for literal in clause:
            visit(literal.atom)
    return sorted(constants)


def build_replay(text: str) -> str:
    statements = parse_statements(text)
    by_name = {statement.name: statement for statement in statements}

    c8_stmt = find_source_cnf(statements, "rule_pm2_61d1", lambda clause: len(clause) == 3)
    c9_stmt = find_source_cnf(statements, "hypothesis_1", lambda clause: len(clause) == 1 and clause[0].positive)
    c10_stmt = find_source_cnf(statements, "rule_imim2i", lambda clause: len(clause) == 2)
    c11_stmt = find_source_cnf(statements, "hypothesis_2", lambda clause: len(clause) == 1 and clause[0].positive)
    cneg_stmt = find_source_cnf(statements, "target", lambda clause: len(clause) == 1 and not clause[0].positive)

    c13_stmt = direct_child(statements, c8_stmt.name, c9_stmt.name)
    c14_stmt = direct_child(statements, c10_stmt.name, c11_stmt.name)
    final_candidates = [statement for statement in statements if statement.clause == ()]
    if len(final_candidates) != 1:
        raise ValueError(f"expected one empty clause, found {len(final_candidates)}")
    final_stmt = final_candidates[0]
    for parent in (c13_stmt.name, c14_stmt.name, cneg_stmt.name):
        if parent not in final_stmt.annotation:
            raise ValueError(f"final TSTP inference does not cite {parent}")

    c8 = source_clause(rename_clause(c8_stmt.clause or (), "r0"), "rule_pm2_61d1")
    c9 = source_clause(rename_clause(c9_stmt.clause or (), "h1"), "hypothesis_1")
    c10 = source_clause(rename_clause(c10_stmt.clause or (), "r1"), "rule_imim2i")
    c11 = source_clause(rename_clause(c11_stmt.clause or (), "h2"), "hypothesis_2")
    cneg = source_clause(rename_clause(cneg_stmt.clause or (), "goal"), "target")

    c13, s13, lp13, rp13 = select_resolution(c8, c9, c13_stmt.clause or (), "E step c13")
    c14, s14, lp14, rp14 = select_resolution(c10, c11, c14_stmt.clause or (), "E step c14")

    target_atom = cneg.clause[0].atom
    positive_target = (Literal(True, target_atom),)
    c15pos, s15, lp15, rp15 = select_resolution(c13, c14, positive_target, "E nested step")
    empty, s16, lp16, rp16 = select_resolution(c15pos, cneg, (), "E final step")
    if empty.proof is not None:
        raise ValueError("empty clause unexpectedly carries a direct proof annotation")
    if c15pos.proof is None:
        raise ValueError("positive target has no reconstructed Horn proof")

    steps_data = [
        ("c13", "c8", "c9", c8, c9, c13, s13, lp13, rp13),
        ("c14", "c10", "c11", c10, c11, c14, s14, lp14, rp14),
        ("c15-positive", "c13", "c14", c13, c14, c15pos, s15, lp15, rp15),
        ("empty", "c15-positive", "c15-negative", c15pos, cneg, empty, s16, lp16, rp16),
    ]

    lines = [
        "; ============================================================================",
        "; setmm_prime_e_ja_resolution_replay_v0.metta",
        "; GENERATED by setmm_prime_e_tstp_replay_tools.py from E's TSTP proof.",
        "; The source problem is the public CC0 set.mm full-prior-theory encoding.",
        "; E is an external producer; explicit resolution substitutions and the final",
        "; Curry--Howard proof term are replayed by Prime without trusting E or Python.",
        "; ============================================================================",
        "",
        "!(import! &self lib_atp)",
        "",
    ]
    named_clauses = {
        "c8": c8.clause,
        "c9": c9.clause,
        "c10": c10.clause,
        "c11": c11.clause,
        "c13": c13.clause,
        "c14": c14.clause,
        "c15-positive": c15pos.clause,
        "c15-negative": cneg.clause,
        "empty": empty.clause,
    }
    for name, clause in named_clauses.items():
        lines.append(f"!(bind! &{name} {metta_clause(clause)})")
    lines.append("")

    for result_name, left_name, right_name, left, right, result, substitution, left_pivot, right_pivot in steps_data:
        normalized_substitution = tuple(sorted(
            ((variable, apply_term(term, substitution)) for variable, term in substitution.items()),
            key=lambda binding: binding[0].name,
        ))
        lines.extend([
            "!(assertEqual",
            "  (atp:resolution:check-step",
            f"    &{left_name} &{right_name}",
            f"    {metta_substitution(normalized_substitution)}",
            f"    {metta_literal(left_pivot)}",
            f"    {metta_literal(right_pivot)}",
            f"    &{result_name})",
            "  True)",
            "",
        ])

    lines.extend([
        "; A changed final resolvent is rejected.",
        "!(assertEqual",
        "  (atp:resolution:check-step",
        "    &c15-positive &c15-negative (ATP.Subst ())",
        f"    {metta_literal(lp16)}",
        f"    {metta_literal(rp16)}",
        "    ((ATP.Pos (proved forged))))",
        "  False)",
        "",
        "; A required substitution binding cannot be omitted.",
    ])
    s13_bindings = tuple(sorted(s13.items(), key=lambda binding: binding[0].name))
    if len(s13_bindings) < 2:
        raise ValueError("the first E step no longer exercises a multi-binding substitution")
    shortened = tuple((variable, apply_term(term, s13)) for variable, term in s13_bindings[:-1])
    lines.extend([
        "!(assertEqual",
        "  (atp:resolution:check-step",
        f"    &c8 &c9 {metta_substitution(shortened)}",
        f"    {metta_literal(lp13)}",
        f"    {metta_literal(rp13)}",
        "    &c13)",
        "  False)",
        "",
    ])

    source_rules = [("rule_pm2_61d1", c8), ("rule_imim2i", c10)]
    source_facts = [("hypothesis_1", c9), ("hypothesis_2", c11)]
    goal = unwrap_proved(cneg.clause[0])
    lines.extend([
        "; Reconstruct the direct proof term carried by the Horn resolution DAG and",
        "; send it through the unchanged Prime type checker.",
        "!(bind! &e-ja-kb (new-space))",
    ])
    for constant in object_constants(clause.clause for _, clause in source_rules + source_facts):
        lines.append(f"!(add-atom &e-ja-kb (: {constant} Type))")
    lines.extend([
        "!(add-atom &e-ja-kb (: imp (-> Type Type Type)))",
        "!(add-atom &e-ja-kb (: neg (-> Type Type)))",
    ])
    for label, annotated in source_facts:
        formula = unwrap_proved(next(entry.literal for entry in annotated.entries if entry.literal.positive))
        lines.append(f"!(add-atom &e-ja-kb (: {label} {metta_term(formula, typed=True)}))")
    for label, annotated in source_rules:
        positives = [entry.literal for entry in annotated.entries if entry.literal.positive]
        negatives = [entry.literal for entry in annotated.entries if not entry.literal.positive]
        if len(positives) != 1:
            raise ValueError(f"{label}: expected exactly one positive literal")
        parts = [metta_term(unwrap_proved(literal), typed=True) for literal in negatives]
        parts.append(metta_term(unwrap_proved(positives[0]), typed=True))
        lines.append(f"!(add-atom &e-ja-kb (: {label} (-> {' '.join(parts)})))")
    goal_text = metta_term(goal, typed=True)
    proof_text = metta_proof(c15pos.proof)
    lines.extend([
        "",
        "!(assertEqual",
        f"  (check-type &e-ja-kb {proof_text} {goal_text} 100000)",
        f"  (he-accept (exact {goal_text})))",
        "",
        "!(println! (SetMMPrimeETSTPReplaySummary ja 7 7 0))",
        "",
    ])
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


def self_test(proof_text: str) -> None:
    mutations = {
        "changed-resolvent": proof_text.replace(
            "proved(imp(X1,f_ch_183))|~proved(imp(X1,imp(f_ph_183,f_ch_183)))",
            "proved(imp(X1,forged))|~proved(imp(X1,imp(f_ph_183,f_ch_183)))",
            1,
        ),
        "changed-parent": proof_text.replace(
            "[c_0_13, c_0_14]", "[c_0_13, c_0_11]", 1
        ),
        "missing-empty-clause": proof_text.replace(
            "cnf(c_0_16, plain, ($false)",
            "cnf(c_0_16, plain, (proved(forged))",
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
    parser.add_argument("--proof", type=Path, default=root / "tptp/ja_hilbert_full_e_refutation.tstp")
    parser.add_argument("--output", type=Path, default=root / "setmm_prime_e_ja_resolution_replay_v0.metta")
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--live-e", type=Path)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--problem", type=Path, default=root / "tptp/ja_hilbert_full.p")
    parser.add_argument("--cpu-limit", type=int, default=5)
    args = parser.parse_args()
    if not args.write and not args.check and args.live_e is None and not args.self_test:
        parser.error("choose --write, --check, --live-e, or --self-test")

    proof_text = args.proof.read_text()
    generated = build_replay(proof_text)
    if args.write:
        args.output.write_text(generated)
        print(f"PASS: wrote {args.output.name}")
    if args.check:
        if not args.output.exists() or args.output.read_text() != generated:
            print(f"FAIL: {args.output.name} is not the deterministic replay", file=sys.stderr)
            return 1
        print(f"PASS: {args.output.name} is deterministic")
    if args.live_e is not None:
        live_generated = build_replay(run_e(args.live_e, args.problem, args.cpu_limit))
        if live_generated != generated:
            print("FAIL: live E proof does not reproduce the frozen replay", file=sys.stderr)
            return 1
        print("PASS: live E TSTP proof reproduces the frozen Prime replay")
    if args.self_test:
        self_test(proof_text)
        print("PASS: all 3 TSTP replay mutations are rejected")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
