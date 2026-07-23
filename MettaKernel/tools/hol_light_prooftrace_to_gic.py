#!/usr/bin/env python3
"""Lower an official HOL Light ProofTrace closure to generic MIK GIC data.

The ProofTrace JSONL and this adapter are untrusted source transport.  The
emitted MeTTa artifact is accepted only when the generated LanguageDef
presentation and generic inference checker validate its complete proof DAG.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence


class TraceError(ValueError):
    pass


@dataclass(frozen=True)
class TyVar:
    name: str


@dataclass(frozen=True)
class TyApp:
    name: str
    arguments: tuple[HolType, ...]


HolType = TyVar | TyApp


@dataclass(frozen=True)
class Var:
    name: str
    type: HolType


@dataclass(frozen=True)
class Const:
    name: str
    type: HolType


@dataclass(frozen=True)
class Comb:
    function: HolTerm
    argument: HolTerm


@dataclass(frozen=True)
class Abs:
    variable: HolTerm
    body: HolTerm


HolTerm = Var | Const | Comb | Abs


@dataclass(frozen=True)
class Theorem:
    hypotheses: tuple[HolTerm, ...]
    conclusion: HolTerm


@dataclass(frozen=True)
class Pattern:
    head: str
    arguments: tuple[Pattern, ...] = ()


@dataclass(frozen=True)
class Fact:
    rule_id: str
    node_id: str
    relation: str
    arguments: tuple[Pattern, ...]


@dataclass(frozen=True)
class DagNode:
    node_id: str
    rule_id: str
    arguments: tuple[Pattern, ...]
    children: tuple[str, ...]


class Cursor:
    def __init__(self, source: str):
        self.source = source
        self.position = 0

    def starts(self, prefix: str) -> bool:
        return self.source.startswith(prefix, self.position)

    def expect(self, value: str) -> None:
        if not self.starts(value):
            actual = self.source[self.position : self.position + max(12, len(value))]
            raise TraceError(
                f"expected {value!r} at offset {self.position}, found {actual!r}"
            )
        self.position += len(value)

    def read_until(self, delimiter: str) -> str:
        end = self.source.find(delimiter, self.position)
        if end < 0:
            raise TraceError(
                f"missing {delimiter!r} after offset {self.position} in {self.source!r}"
            )
        value = self.source[self.position : end]
        self.position = end + len(delimiter)
        return value

    def done(self) -> bool:
        return self.position == len(self.source)

    def peek(self) -> str:
        return self.source[self.position : self.position + 1]


def parse_type_at(cursor: Cursor) -> HolType:
    if cursor.starts("v["):
        cursor.expect("v[")
        return TyVar(cursor.read_until("]"))
    if cursor.starts("c["):
        cursor.expect("c[")
        name = cursor.read_until("]")
        cursor.expect("[")
        arguments: list[HolType] = []
        while cursor.peek() == "[":
            cursor.expect("[")
            arguments.append(parse_type_at(cursor))
            cursor.expect("]")
        cursor.expect("]")
        return TyApp(name, tuple(arguments))
    raise TraceError(f"invalid HOL type at offset {cursor.position}: {cursor.source!r}")


def parse_type(source: str) -> HolType:
    cursor = Cursor(source)
    result = parse_type_at(cursor)
    if not cursor.done():
        raise TraceError(f"trailing HOL type input at offset {cursor.position}: {source!r}")
    return result


def parse_term_at(cursor: Cursor) -> HolTerm:
    if cursor.starts("v("):
        cursor.expect("v(")
        name = cursor.read_until(")")
        cursor.expect("(")
        type_ = parse_type_at(cursor)
        cursor.expect(")")
        return Var(name, type_)
    if cursor.starts("c("):
        cursor.expect("c(")
        name = cursor.read_until(")")
        cursor.expect("(")
        type_ = parse_type_at(cursor)
        cursor.expect(")")
        return Const(name, type_)
    if cursor.starts("C("):
        cursor.expect("C(")
        function = parse_term_at(cursor)
        cursor.expect(")(")
        argument = parse_term_at(cursor)
        cursor.expect(")")
        return Comb(function, argument)
    if cursor.starts("A("):
        cursor.expect("A(")
        variable = parse_term_at(cursor)
        cursor.expect(")(")
        body = parse_term_at(cursor)
        cursor.expect(")")
        return Abs(variable, body)
    raise TraceError(f"invalid HOL term at offset {cursor.position}: {cursor.source!r}")


def parse_term(source: str) -> HolTerm:
    cursor = Cursor(source)
    result = parse_term_at(cursor)
    if not cursor.done():
        raise TraceError(f"trailing HOL term input at offset {cursor.position}: {source!r}")
    return result


BOOL = TyApp("bool", ())


def function_type(domain: HolType, codomain: HolType) -> HolType:
    return TyApp("fun", (domain, codomain))


def type_of(term: HolTerm) -> HolType:
    if isinstance(term, (Var, Const)):
        return term.type
    if isinstance(term, Comb):
        function_ty = type_of(term.function)
        if not (
            isinstance(function_ty, TyApp)
            and function_ty.name == "fun"
            and len(function_ty.arguments) == 2
        ):
            raise TraceError(f"application has non-function operator: {term!r}")
        domain, codomain = function_ty.arguments
        if type_of(term.argument) != domain:
            raise TraceError(f"application domain mismatch: {term!r}")
        return codomain
    if isinstance(term, Abs):
        if not isinstance(term.variable, Var):
            raise TraceError(f"abstraction binder is not a variable: {term!r}")
        return function_type(term.variable.type, type_of(term.body))
    raise AssertionError(term)


def dest_equality(term: HolTerm) -> tuple[HolType, HolTerm, HolTerm]:
    if not (
        isinstance(term, Comb)
        and isinstance(term.function, Comb)
        and isinstance(term.function.function, Const)
        and term.function.function.name == "="
    ):
        raise TraceError(f"expected HOL equality, found {term!r}")
    left = term.function.argument
    right = term.argument
    equality_type = term.function.function.type
    expected = function_type(type_of(left), function_type(type_of(left), BOOL))
    if equality_type != expected or type_of(right) != type_of(left):
        raise TraceError(f"malformed typed HOL equality: {term!r}")
    return type_of(left), left, right


def alpha_key(term: HolTerm, binders: tuple[Var, ...] = ()) -> tuple:
    if isinstance(term, Var):
        for index, binder in enumerate(reversed(binders)):
            if term == binder:
                return ("bound", index, term.type)
        return ("free", term.name, term.type)
    if isinstance(term, Const):
        return ("const", term.name, term.type)
    if isinstance(term, Comb):
        return ("comb", alpha_key(term.function, binders), alpha_key(term.argument, binders))
    if isinstance(term, Abs):
        if not isinstance(term.variable, Var):
            raise TraceError(f"abstraction binder is not a variable: {term!r}")
        return ("abs", term.variable.type, alpha_key(term.body, binders + (term.variable,)))
    raise AssertionError(term)


def alpha_equal(left: HolTerm, right: HolTerm) -> bool:
    return alpha_key(left) == alpha_key(right)


def remove_alpha(term: HolTerm, hypotheses: Sequence[HolTerm]) -> tuple[HolTerm, ...]:
    result = list(hypotheses)
    for index, hypothesis in enumerate(result):
        if alpha_equal(term, hypothesis):
            del result[index]
            break
    return tuple(result)


def papp(head: str, *arguments: Pattern) -> Pattern:
    return Pattern(head, tuple(arguments))


def name_pattern(value: str) -> Pattern:
    suffix = ".".join(str(byte) for byte in value.encode("utf-8"))
    return papp(f"$hol.name.{suffix}")


def type_data(type_: HolType) -> object:
    if isinstance(type_, TyVar):
        return ["v", type_.name]
    if isinstance(type_, TyApp):
        return ["c", type_.name, [type_data(argument) for argument in type_.arguments]]
    raise AssertionError(type_)


def term_data(term: HolTerm) -> object:
    if isinstance(term, Var):
        return ["v", term.name, type_data(term.type)]
    if isinstance(term, Const):
        return ["c", term.name, type_data(term.type)]
    if isinstance(term, Comb):
        return ["C", term_data(term.function), term_data(term.argument)]
    if isinstance(term, Abs):
        return ["A", term_data(term.variable), term_data(term.body)]
    raise AssertionError(term)


def content_head(kind: str, value: object) -> str:
    payload = json.dumps(
        value, ensure_ascii=False, separators=(",", ":")
    ).encode("utf-8")
    return f"$hol.{kind}.{hashlib.sha256(payload).hexdigest()}"


def type_pattern(type_: HolType) -> Pattern:
    if type_ == BOOL:
        return papp("$hol.type.bool")
    return papp(content_head("type", type_data(type_)))


def term_pattern(term: HolTerm) -> Pattern:
    try:
        type_, left, right = dest_equality(term)
        return equality_pattern(type_, left, right)
    except TraceError:
        pass
    return papp(content_head("term", term_data(term)))


def type_list_pattern(arguments: Sequence[Pattern]) -> Pattern:
    result = papp("TyNil")
    for argument in reversed(arguments):
        result = papp("TyCons", argument, result)
    return result


def type_app_pattern(name: str, arguments: Sequence[Pattern] = ()) -> Pattern:
    return papp("TyApp", name_pattern(name), type_list_pattern(arguments))


def function_type_pattern(domain: Pattern, codomain: Pattern) -> Pattern:
    return type_app_pattern("fun", (domain, codomain))


def equality_pattern(type_: HolType, left: HolTerm, right: HolTerm) -> Pattern:
    encoded_type = type_pattern(type_)
    equality_type = function_type_pattern(
        encoded_type, function_type_pattern(encoded_type, type_pattern(BOOL))
    )
    equality = papp("TmConst", name_pattern("="), equality_type)
    return papp("TmApp", papp("TmApp", equality, term_pattern(left)), term_pattern(right))


def hypotheses_pattern(hypotheses: Sequence[HolTerm]) -> Pattern:
    result = papp("HypsNil")
    for hypothesis in reversed(hypotheses):
        result = papp("HypsCons", term_pattern(hypothesis), result)
    return result


def theorem_pattern(theorem: Theorem) -> Pattern:
    return papp(
        "Seq", hypotheses_pattern(theorem.hypotheses), term_pattern(theorem.conclusion)
    )


def theorem_judgment(theorem: Theorem) -> Pattern:
    return papp("$hol.thm", theorem_pattern(theorem))


def term_map_pattern(pairs: Sequence[tuple[HolTerm, HolTerm]]) -> Pattern:
    result = papp("TermMapNil")
    for redex, residue in reversed(pairs):
        result = papp("TermMapCons", term_pattern(redex), term_pattern(residue), result)
    return result


def type_map_pattern(pairs: Sequence[tuple[HolType, HolType]]) -> Pattern:
    result = papp("TypeMapNil")
    for redex, residue in reversed(pairs):
        result = papp("TypeMapCons", type_pattern(redex), type_pattern(residue), result)
    return result


def substitution_pattern(
    term_pairs: Sequence[tuple[HolTerm, HolTerm]] = (),
    type_pairs: Sequence[tuple[HolType, HolType]] = (),
) -> Pattern:
    return papp("Subst", type_map_pattern(type_pairs), term_map_pattern(term_pairs))


def render_list(values: Iterable[str], nil: str, cons: str) -> str:
    result = nil
    for value in reversed(tuple(values)):
        result = f"({cons} {value} {result})"
    return result


def render_pattern(pattern: Pattern) -> str:
    arguments = render_list((render_pattern(value) for value in pattern.arguments), "LNil", "LCons")
    return f"(PApp {json.dumps(pattern.head, ensure_ascii=False)} {arguments})"


def render_fact_rule(rule_id: str, relation: str, arity: int) -> str:
    names = tuple(f"a{index}" for index in range(arity))
    formals = render_list(
        (f"(Formal {json.dumps(name)} 0)" for name in names), "LNil", "LCons"
    )
    arguments = render_list(
        (f"(FVar {json.dumps(name)})" for name in names), "LNil", "LCons"
    )
    conclusion = f"(PApp {json.dumps(f'$hol.rel.{relation}')} {arguments})"
    return f"(GRule {json.dumps(rule_id)} {formals} LNil {conclusion})"


def render_node(node: DagNode) -> str:
    arguments = render_list((render_pattern(value) for value in node.arguments), "LNil", "LCons")
    children = render_list((json.dumps(value) for value in node.children), "DrNil", "DrCons")
    return (
        f"(GDNode {json.dumps(node.node_id)} "
        f"(GRuleInst {json.dumps(node.rule_id)} {arguments}) {children})"
    )


def collect_name_heads(pattern: Pattern, result: set[str]) -> None:
    if pattern.head.startswith(("$hol.name.", "$hol.term.", "$hol.type.")):
        result.add(pattern.head)
    for argument in pattern.arguments:
        collect_name_heads(argument, result)


def read_json_lines(path: Path) -> list[dict]:
    rows: list[dict] = []
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        try:
            value = json.loads(line)
        except json.JSONDecodeError as error:
            raise TraceError(f"{path.name}:{line_number}: invalid JSON: {error}") from error
        if not isinstance(value, dict):
            raise TraceError(f"{path.name}:{line_number}: expected a JSON object")
        rows.append(value)
    return rows


def read_theorems(path: Path) -> dict[int, Theorem]:
    result: dict[int, Theorem] = {}
    for row in read_json_lines(path):
        identifier = row.get("id")
        theorem = row.get("th")
        if not isinstance(identifier, int) or not isinstance(theorem, dict):
            raise TraceError(f"{path.name}: malformed theorem row: {row!r}")
        hypotheses = theorem.get("hy")
        conclusion = theorem.get("cc")
        if not isinstance(hypotheses, list) or not all(isinstance(x, str) for x in hypotheses):
            raise TraceError(f"{path.name}: malformed hypothesis list for id {identifier}")
        if not isinstance(conclusion, str):
            raise TraceError(f"{path.name}: malformed conclusion for id {identifier}")
        if identifier in result:
            raise TraceError(f"{path.name}: duplicate theorem id {identifier}")
        result[identifier] = Theorem(
            tuple(parse_term(value) for value in hypotheses), parse_term(conclusion)
        )
    return result


def read_formals(path: Path, system: str) -> dict[str, tuple[str, ...]]:
    prefix = f"; MIK-HOL-FORMALS {system} "
    result: dict[str, tuple[str, ...]] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.startswith(prefix):
            continue
        body = line[len(prefix) :]
        rule_id, separator, names = body.partition(" ")
        if not separator or not rule_id:
            raise TraceError(f"malformed generated formal manifest line: {line!r}")
        if rule_id in result:
            raise TraceError(f"duplicate generated formal manifest for {rule_id}")
        result[rule_id] = tuple(name for name in names.split(",") if name)
    if not result:
        raise TraceError(f"no generated {system} formal manifest in {path.name}")
    return result


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class Lowerer:
    def __init__(
        self,
        proofs: Sequence[dict],
        theorems: dict[int, Theorem],
        formals: dict[str, tuple[str, ...]],
        artifact_id: str,
    ):
        self.proofs = proofs
        self.theorems = theorems
        self.formals = formals
        self.artifact_id = artifact_id
        self.facts: list[Fact] = []
        self.nodes: list[DagNode] = []
        self.seen: set[int] = set()

    def source_node_id(self, identifier: int) -> str:
        return f"s{identifier}"

    def fact(self, identifier: int, relation: str, *arguments: Pattern) -> str:
        slot = sum(1 for fact in self.facts if fact.node_id.startswith(f"f{identifier}_"))
        node_id = f"f{identifier}_{slot}"
        rule_id = f"$hl.source.{self.artifact_id}.{relation}"
        self.facts.append(Fact(rule_id, node_id, relation, tuple(arguments)))
        self.nodes.append(DagNode(node_id, rule_id, tuple(arguments), ()))
        return node_id

    def theorem(self, identifier: int) -> Theorem:
        try:
            return self.theorems[identifier]
        except KeyError as error:
            raise TraceError(f"proof references absent theorem id {identifier}") from error

    def child(self, current: int, identifier: object) -> tuple[Theorem, str]:
        if not isinstance(identifier, int):
            raise TraceError(f"proof {current}: child id is not an integer: {identifier!r}")
        if identifier not in self.seen:
            raise TraceError(f"proof {current}: child {identifier} is absent or not earlier")
        return self.theorem(identifier), self.source_node_id(identifier)

    def arguments(self, rule_id: str, environment: dict[str, Pattern]) -> tuple[Pattern, ...]:
        try:
            formal_names = self.formals[rule_id]
        except KeyError as error:
            raise TraceError(f"generated presentation lacks rule {rule_id}") from error
        missing = [name for name in formal_names if name not in environment]
        if missing:
            raise TraceError(f"{rule_id}: adapter did not bind generated formals {missing}")
        return tuple(environment[name] for name in formal_names)

    def add_source_node(
        self,
        identifier: int,
        rule_id: str,
        environment: dict[str, Pattern],
        theorem_children: Sequence[str],
        fact_children: Sequence[str],
    ) -> None:
        self.nodes.append(
            DagNode(
                self.source_node_id(identifier),
                rule_id,
                self.arguments(rule_id, environment),
                tuple(theorem_children) + tuple(fact_children),
            )
        )
        self.seen.add(identifier)

    def lower_row(self, row: dict) -> None:
        identifier = row.get("id")
        proof = row.get("pr")
        if not isinstance(identifier, int) or not isinstance(proof, list) or not proof:
            raise TraceError(f"malformed proof row: {row!r}")
        if identifier in self.seen:
            raise TraceError(f"duplicate proof id {identifier}")
        if identifier not in self.theorems:
            raise TraceError(f"proof id {identifier} has no theorem row")
        operation = proof[0]
        if not isinstance(operation, str):
            raise TraceError(f"proof {identifier}: operation is not a string")
        output = self.theorem(identifier)

        if operation == "REFL":
            if len(proof) != 2 or not isinstance(proof[1], str):
                raise TraceError(f"proof {identifier}: malformed REFL")
            term = parse_term(proof[1])
            type_, left, right = dest_equality(output.conclusion)
            if output.hypotheses or left != term or right != term:
                raise TraceError(f"proof {identifier}: REFL theorem disagrees with payload")
            fact = self.fact(identifier, "termHasType", term_pattern(term), type_pattern(type_))
            self.add_source_node(
                identifier,
                "HL_REFL",
                {"P": term_pattern(term), "T": type_pattern(type_)},
                (),
                (fact,),
            )
            return

        if operation == "TRANS":
            if len(proof) != 3:
                raise TraceError(f"proof {identifier}: malformed TRANS")
            left_thm, left_id = self.child(identifier, proof[1])
            right_thm, right_id = self.child(identifier, proof[2])
            t1, p, q = dest_equality(left_thm.conclusion)
            t2, q2, r = dest_equality(right_thm.conclusion)
            out_t, out_p, out_r = dest_equality(output.conclusion)
            if out_t != t1 or out_p != p or out_r != r or not alpha_equal(q, q2):
                raise TraceError(f"proof {identifier}: TRANS theorem/premises disagree")
            alpha = self.fact(identifier, "alphaEq", term_pattern(q), term_pattern(q2))
            union = self.fact(
                identifier,
                "hypUnion",
                hypotheses_pattern(left_thm.hypotheses),
                hypotheses_pattern(right_thm.hypotheses),
                hypotheses_pattern(output.hypotheses),
            )
            environment = {
                "H1": hypotheses_pattern(left_thm.hypotheses),
                "T": type_pattern(t1),
                "P": term_pattern(p),
                "Q": term_pattern(q),
                "H2": hypotheses_pattern(right_thm.hypotheses),
                "T2": type_pattern(t2),
                "Q2": term_pattern(q2),
                "R": term_pattern(r),
                "HO": hypotheses_pattern(output.hypotheses),
            }
            self.add_source_node(identifier, "HL_TRANS", environment, (left_id, right_id), (alpha, union))
            return

        if operation == "MK_COMB":
            if len(proof) != 3:
                raise TraceError(f"proof {identifier}: malformed MK_COMB")
            function_thm, function_id = self.child(identifier, proof[1])
            argument_thm, argument_id = self.child(identifier, proof[2])
            tf, f, g = dest_equality(function_thm.conclusion)
            tx, x, y = dest_equality(argument_thm.conclusion)
            to, fx, gy = dest_equality(output.conclusion)
            if fx != Comb(f, x) or gy != Comb(g, y):
                raise TraceError(f"proof {identifier}: MK_COMB result is not source application")
            side = (
                self.fact(identifier, "appResult", term_pattern(f), term_pattern(x), term_pattern(fx)),
                self.fact(identifier, "appResult", term_pattern(g), term_pattern(y), term_pattern(gy)),
                self.fact(
                    identifier,
                    "hypUnion",
                    hypotheses_pattern(function_thm.hypotheses),
                    hypotheses_pattern(argument_thm.hypotheses),
                    hypotheses_pattern(output.hypotheses),
                ),
                self.fact(identifier, "termHasType", term_pattern(fx), type_pattern(to)),
            )
            environment = {
                "H1": hypotheses_pattern(function_thm.hypotheses),
                "TF": type_pattern(tf),
                "F": term_pattern(f),
                "G": term_pattern(g),
                "H2": hypotheses_pattern(argument_thm.hypotheses),
                "TX": type_pattern(tx),
                "X": term_pattern(x),
                "Y": term_pattern(y),
                "FX": term_pattern(fx),
                "GY": term_pattern(gy),
                "HO": hypotheses_pattern(output.hypotheses),
                "TO": type_pattern(to),
            }
            self.add_source_node(
                identifier, "HL_MK_COMB", environment, (function_id, argument_id), side
            )
            return

        if operation == "ABS":
            if len(proof) != 3 or not isinstance(proof[2], str):
                raise TraceError(f"proof {identifier}: malformed ABS")
            equality_thm, equality_id = self.child(identifier, proof[1])
            variable = parse_term(proof[2])
            if not isinstance(variable, Var):
                raise TraceError(f"proof {identifier}: ABS binder is not a variable")
            ti, p, q = dest_equality(equality_thm.conclusion)
            to, vp, vq = dest_equality(output.conclusion)
            if vp != Abs(variable, p) or vq != Abs(variable, q):
                raise TraceError(f"proof {identifier}: ABS theorem disagrees with payload")
            side = (
                self.fact(identifier, "absResult", term_pattern(variable), term_pattern(p), term_pattern(vp)),
                self.fact(identifier, "absResult", term_pattern(variable), term_pattern(q), term_pattern(vq)),
                self.fact(identifier, "notFreeIn", term_pattern(variable), hypotheses_pattern(equality_thm.hypotheses)),
                self.fact(identifier, "termHasType", term_pattern(vp), type_pattern(to)),
            )
            environment = {
                "V": term_pattern(variable),
                "H1": hypotheses_pattern(equality_thm.hypotheses),
                "TI": type_pattern(ti),
                "P": term_pattern(p),
                "Q": term_pattern(q),
                "VP": term_pattern(vp),
                "VQ": term_pattern(vq),
                "TO": type_pattern(to),
            }
            self.add_source_node(identifier, "HL_ABS", environment, (equality_id,), side)
            return

        if operation == "BETA":
            if len(proof) != 2 or not isinstance(proof[1], str):
                raise TraceError(f"proof {identifier}: malformed BETA")
            redex = parse_term(proof[1])
            type_, left, right = dest_equality(output.conclusion)
            if output.hypotheses or left != redex:
                raise TraceError(f"proof {identifier}: BETA theorem disagrees with payload")
            side = (
                self.fact(identifier, "betaResult", term_pattern(redex), term_pattern(right)),
                self.fact(identifier, "termHasType", term_pattern(right), type_pattern(type_)),
            )
            self.add_source_node(
                identifier,
                "HL_BETA",
                {"P": term_pattern(redex), "Q": term_pattern(right), "T": type_pattern(type_)},
                (),
                side,
            )
            return

        if operation == "ASSUME":
            if len(proof) != 2 or not isinstance(proof[1], str):
                raise TraceError(f"proof {identifier}: malformed ASSUME")
            proposition = parse_term(proof[1])
            if output != Theorem((proposition,), proposition):
                raise TraceError(f"proof {identifier}: ASSUME theorem disagrees with payload")
            fact = self.fact(identifier, "isBool", term_pattern(proposition))
            self.add_source_node(
                identifier, "HL_ASSUME", {"P": term_pattern(proposition)}, (), (fact,)
            )
            return

        if operation == "EQ_MP":
            if len(proof) != 3:
                raise TraceError(f"proof {identifier}: malformed EQ_MP")
            equality_thm, equality_id = self.child(identifier, proof[1])
            premise_thm, premise_id = self.child(identifier, proof[2])
            type_, p, q = dest_equality(equality_thm.conclusion)
            q2 = premise_thm.conclusion
            if type_ != BOOL or output.conclusion != q or not alpha_equal(p, q2):
                raise TraceError(f"proof {identifier}: EQ_MP theorem/premises disagree")
            side = (
                self.fact(identifier, "alphaEq", term_pattern(p), term_pattern(q2)),
                self.fact(
                    identifier,
                    "hypUnion",
                    hypotheses_pattern(equality_thm.hypotheses),
                    hypotheses_pattern(premise_thm.hypotheses),
                    hypotheses_pattern(output.hypotheses),
                ),
            )
            environment = {
                "H1": hypotheses_pattern(equality_thm.hypotheses),
                "P": term_pattern(p),
                "Q": term_pattern(q),
                "H2": hypotheses_pattern(premise_thm.hypotheses),
                "Q2": term_pattern(q2),
                "HO": hypotheses_pattern(output.hypotheses),
            }
            self.add_source_node(identifier, "HL_EQ_MP", environment, (equality_id, premise_id), side)
            return

        if operation == "DEDUCT_ANTISYM_RULE":
            if len(proof) != 3:
                raise TraceError(f"proof {identifier}: malformed DEDUCT_ANTISYM_RULE")
            left_thm, left_id = self.child(identifier, proof[1])
            right_thm, right_id = self.child(identifier, proof[2])
            p = left_thm.conclusion
            q = right_thm.conclusion
            type_, out_p, out_q = dest_equality(output.conclusion)
            if out_p != p or out_q != q or type_of(p) != type_ or type_of(q) != type_:
                raise TraceError(f"proof {identifier}: DEDUCT_ANTISYM theorem disagrees")
            hr1 = remove_alpha(q, left_thm.hypotheses)
            hr2 = remove_alpha(p, right_thm.hypotheses)
            side = (
                self.fact(
                    identifier,
                    "hypRemove",
                    term_pattern(q),
                    hypotheses_pattern(left_thm.hypotheses),
                    hypotheses_pattern(hr1),
                ),
                self.fact(
                    identifier,
                    "hypRemove",
                    term_pattern(p),
                    hypotheses_pattern(right_thm.hypotheses),
                    hypotheses_pattern(hr2),
                ),
                self.fact(
                    identifier,
                    "hypUnion",
                    hypotheses_pattern(hr1),
                    hypotheses_pattern(hr2),
                    hypotheses_pattern(output.hypotheses),
                ),
                self.fact(identifier, "termHasType", term_pattern(p), type_pattern(type_)),
                self.fact(identifier, "termHasType", term_pattern(q), type_pattern(type_)),
            )
            environment = {
                "H1": hypotheses_pattern(left_thm.hypotheses),
                "P": term_pattern(p),
                "H2": hypotheses_pattern(right_thm.hypotheses),
                "Q": term_pattern(q),
                "HR1": hypotheses_pattern(hr1),
                "HR2": hypotheses_pattern(hr2),
                "HO": hypotheses_pattern(output.hypotheses),
                "T": type_pattern(type_),
            }
            self.add_source_node(
                identifier, "HL_DEDUCT_ANTISYM", environment, (left_id, right_id), side
            )
            return

        if operation in ("INST", "INST_TYPE"):
            if len(proof) != 3 or not isinstance(proof[2], list):
                raise TraceError(f"proof {identifier}: malformed {operation}")
            input_thm, input_id = self.child(identifier, proof[1])
            if operation == "INST":
                pairs: list[tuple[HolTerm, HolTerm]] = []
                for pair in proof[2]:
                    if not (
                        isinstance(pair, list)
                        and len(pair) == 2
                        and all(isinstance(value, str) for value in pair)
                    ):
                        raise TraceError(f"proof {identifier}: malformed INST pair {pair!r}")
                    pairs.append((parse_term(pair[0]), parse_term(pair[1])))
                substitution = substitution_pattern(term_pairs=pairs)
                rule_id = "HL_INST"
            else:
                type_pairs: list[tuple[HolType, HolType]] = []
                for pair in proof[2]:
                    if not (
                        isinstance(pair, list)
                        and len(pair) == 2
                        and all(isinstance(value, str) for value in pair)
                    ):
                        raise TraceError(f"proof {identifier}: malformed INST_TYPE pair {pair!r}")
                    type_pairs.append((parse_type(pair[0]), parse_type(pair[1])))
                substitution = substitution_pattern(type_pairs=type_pairs)
                rule_id = "HL_INST_TYPE"
            fact = self.fact(
                identifier,
                "substResult",
                substitution,
                theorem_pattern(input_thm),
                theorem_pattern(output),
            )
            environment = {
                "S": substitution,
                "Input": theorem_pattern(input_thm),
                "Output": theorem_pattern(output),
            }
            self.add_source_node(identifier, rule_id, environment, (input_id,), (fact,))
            return

        if operation == "AXIOM":
            if len(proof) != 2 or not isinstance(proof[1], str):
                raise TraceError(f"proof {identifier}: malformed AXIOM")
            proposition = parse_term(proof[1])
            if output != Theorem((), proposition):
                raise TraceError(f"proof {identifier}: AXIOM theorem disagrees with payload")
            output_pattern = theorem_pattern(output)
            fact = self.fact(identifier, "axiomAllowed", output_pattern)
            self.add_source_node(
                identifier, "HL_AXIOM", {"Output": output_pattern}, (), (fact,)
            )
            return

        if operation == "DEFINITION":
            if len(proof) != 3 or not all(isinstance(value, str) for value in proof[1:]):
                raise TraceError(f"proof {identifier}: malformed DEFINITION")
            payload = parse_term(proof[1])
            name = proof[2]
            type_, left, right = dest_equality(output.conclusion)
            if (
                output.hypotheses
                or payload != output.conclusion
                or not isinstance(left, Const)
                or left.name != name
                or left.type != type_
            ):
                raise TraceError(f"proof {identifier}: DEFINITION theorem disagrees with payload")
            fact = self.fact(
                identifier,
                "definitionAllowed",
                name_pattern(name),
                type_pattern(type_),
                term_pattern(right),
            )
            const_fact = self.fact(
                identifier,
                "constResult",
                name_pattern(name),
                type_pattern(type_),
                term_pattern(left),
            )
            environment = {
                "N": name_pattern(name),
                "T": type_pattern(type_),
                "P": term_pattern(right),
                "C": term_pattern(left),
            }
            self.add_source_node(
                identifier, "HL_DEFINITION", environment, (), (fact, const_fact)
            )
            return

        if operation == "TYPE_DEFINITION":
            raise TraceError(
                f"proof {identifier}: ProofTrace omits TYPE_DEFINITION's new type; "
                "extend the source export before lowering this rule"
            )

        raise TraceError(f"proof {identifier}: unsupported ProofTrace operation {operation}")

    def lower(self) -> None:
        proof_ids: set[int] = set()
        for row in self.proofs:
            identifier = row.get("id")
            if not isinstance(identifier, int):
                raise TraceError(f"malformed proof id: {row!r}")
            proof_ids.add(identifier)
            self.lower_row(row)
        if proof_ids != set(self.theorems):
            missing_proofs = sorted(set(self.theorems) - proof_ids)
            missing_theorems = sorted(proof_ids - set(self.theorems))
            raise TraceError(
                f"proof/theorem id mismatch: missing proofs={missing_proofs}, "
                f"missing theorems={missing_theorems}"
            )


def render_artifact(
    lowerer: Lowerer,
    root_id: int,
    root_name: str,
    root_goal: Pattern,
    hashes: dict[str, str],
) -> str:
    name_heads: set[str] = set()
    collect_name_heads(root_goal, name_heads)
    for fact in lowerer.facts:
        for argument in fact.arguments:
            collect_name_heads(argument, name_heads)
    for node in lowerer.nodes:
        for argument in node.arguments:
            collect_name_heads(argument, name_heads)
    fixed_name_heads = {name_pattern(value).head for value in ("=", "==>", "bool", "fun")}
    fixed_name_heads.add("$hol.type.bool")
    vocabulary = render_list(
        (f"(CDecl {json.dumps(head)} 0)" for head in sorted(name_heads - fixed_name_heads)),
        "LNil",
        "LCons",
    )
    fact_rule_shapes: dict[tuple[str, str], int] = {}
    for fact in lowerer.facts:
        key = (fact.rule_id, fact.relation)
        previous = fact_rule_shapes.setdefault(key, len(fact.arguments))
        if previous != len(fact.arguments):
            raise TraceError(f"relation {fact.relation} used at inconsistent arities")
    fact_rules = render_list(
        (
            render_fact_rule(rule_id, relation, arity)
            for (rule_id, relation), arity in sorted(fact_rule_shapes.items())
        ),
        "LNil",
        "LCons",
    )
    root_node = lowerer.source_node_id(root_id)
    if not lowerer.nodes or lowerer.nodes[-1].node_id != root_node:
        raise TraceError("named root is not the final chronological DAG node")
    terminal_node = lowerer.nodes[-1]
    prefix_nodes = lowerer.nodes[:-1]
    node_chunks = [prefix_nodes[index : index + 48] for index in range(0, len(prefix_nodes), 48)]
    chunk_definitions = [
        f"(= (hl-source-prefix-{index}) "
        + render_list((render_node(node) for node in chunk), "DnNil", "DnCons")
        + ")"
        for index, chunk in enumerate(node_chunks)
    ]
    chunks = "DcNil"
    for index in reversed(range(len(node_chunks))):
        chunks = f"(DcCons (hl-source-prefix-{index}) {chunks})"
    wrong_child = lowerer.source_node_id(next(iter(lowerer.seen - {root_id})))
    lines = [
        "; Generated from an official HOL Light ProofTrace closure.",
        "; The source JSONL and adapter remain untrusted until source correspondence is proved.",
        "; Side-relation rules are explicit source-oracle schemas, not proved HOL algorithms.",
        *(f"; SHA256 {name} {digest}" for name, digest in hashes.items()),
        "!(import! &self hol_source_presentations_generated_v0)",
        "",
        f"(= (hl-source-vocabulary) {vocabulary})",
        f"(= (hl-source-fact-rules) {fact_rules})",
        "(= (hl-source-presentation) (hl-source-presentation-with (hl-source-vocabulary) (hl-source-fact-rules)))",
        f"(= (hl-source-goal) {render_pattern(root_goal)})",
        *chunk_definitions,
        f"(= (hl-source-prefix-chunks) {chunks})",
        f"(= (hl-source-root-node) {render_node(terminal_node)})",
        "",
        "(= (hl-dr-drop-last $children)",
        "   (case $children",
        "     ((DrNil DrNil)",
        "      ((DrCons $value DrNil) DrNil)",
        "      ((DrCons $value $rest) (DrCons $value (hl-dr-drop-last $rest))))))",
        "(= (hl-dr-swap-first-two $children)",
        "   (case $children",
        "     (((DrCons $a (DrCons $b $rest)) (DrCons $b (DrCons $a $rest)))",
        "      ($other $other))))",
        "(= (hl-dr-snoc DrNil $value) (DrCons $value DrNil))",
        "(= (hl-dr-snoc (DrCons $head $tail) $value)",
        "   (DrCons $head (hl-dr-snoc $tail $value)))",
        f"(= (hl-dr-wrong-first (DrCons $head $tail)) (DrCons {json.dumps(wrong_child)} $tail))",
        "(= (hl-dr-wrong-first DrNil) DrNil)",
        "",
    ]

    def root_mutation(name: str, transform: str) -> list[str]:
        return [
            f"(= ({name})",
            "   (case (hl-source-root-node)",
            f"     (((GDNode $id $instance $children) (GDNode $id $instance ({transform})))",
            "      ($_ InvalidRoot))))",
        ]

    lines.extend(root_mutation("hl-source-missing", "hl-dr-drop-last $children"))
    lines.extend(root_mutation("hl-source-reordered", "hl-dr-swap-first-two $children"))
    lines.extend(
        root_mutation(
            "hl-source-extra",
            f"hl-dr-snoc $children {json.dumps(wrong_child)}",
        )
    )
    lines.extend(root_mutation("hl-source-wrong", "hl-dr-wrong-first $children"))
    lines.extend(
        [
            "",
            "(= (hl-source-terminal-checks)",
            "   (case (gic-build-index (hl-source-presentation))",
            "     (((GICIndexOK $space)",
            "        (case (gic-index-check-dag-chunks $space (hl-source-prefix-chunks))",
            "          ((DagOK",
            "             (if (gic-index-check-dag-terminal $space (hl-source-goal) (hl-source-root-node))",
            "               (if (gic-index-check-dag-terminal $space (hl-source-goal) (hl-source-missing))",
            "                 False",
            "                 (if (gic-index-check-dag-terminal $space (hl-source-goal) (hl-source-reordered))",
            "                   False",
            "                   (if (gic-index-check-dag-terminal $space (hl-source-goal) (hl-source-extra))",
            "                     False",
            "                     (if (gic-index-check-dag-terminal $space (hl-source-goal) (hl-source-wrong))",
            "                       False True))))",
            "               False))",
            "           ($_ False))))",
            "      ($_ False))))",
            "!(assertEqual (gic-presentation-valid (hl-source-presentation)) True)",
            "!(assertEqual (hl-source-terminal-checks) True)",
            f"!(HOLLightSourceGICSummary {json.dumps(root_name)} {len(lowerer.seen)} {len(lowerer.facts)} 6 6 0)",
            "",
        ]
    )
    return "\n".join(lines)


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--proofs", type=Path, required=True)
    parser.add_argument("--theorems", type=Path, required=True)
    parser.add_argument("--names", type=Path, required=True)
    parser.add_argument("--presentation", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    return parser.parse_args()


def main() -> int:
    arguments = parse_arguments()
    name_rows = read_json_lines(arguments.names)
    if len(name_rows) != 1:
        raise TraceError(f"{arguments.names.name}: expected exactly one named root")
    root_id = name_rows[0].get("id")
    root_name = name_rows[0].get("nm")
    if not isinstance(root_id, int) or not isinstance(root_name, str):
        raise TraceError(f"{arguments.names.name}: malformed named root")

    proofs = read_json_lines(arguments.proofs)
    theorems = read_theorems(arguments.theorems)
    formals = read_formals(arguments.presentation, "HL")
    hashes = {
        arguments.proofs.name: file_sha256(arguments.proofs),
        arguments.theorems.name: file_sha256(arguments.theorems),
        arguments.names.name: file_sha256(arguments.names),
        arguments.presentation.name: file_sha256(arguments.presentation),
    }
    artifact_id = hashlib.sha256("".join(hashes.values()).encode("ascii")).hexdigest()[:16]
    lowerer = Lowerer(proofs, theorems, formals, artifact_id)
    lowerer.lower()
    if root_id not in lowerer.seen:
        raise TraceError(f"named root {root_id} is absent from the proof closure")
    output = render_artifact(
        lowerer,
        root_id,
        root_name,
        theorem_judgment(theorems[root_id]),
        hashes,
    )
    arguments.output.write_text(output, encoding="utf-8")
    print(
        f"HOL_LIGHT_PROOFTRACE_TO_GIC_OK root={root_id} "
        f"nodes={len(lowerer.seen)} facts={len(lowerer.facts)} bytes={len(output.encode('utf-8'))}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
