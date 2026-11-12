#!/usr/bin/env python3
"""Generate VibeITP rule shapes and audit their source coverage.

Run from the Lean project root:
    python3 scripts/generate_vibe_itp_rule_shapes.py --write
    python3 scripts/generate_vibe_itp_rule_shapes.py --check --self-test

The parser accepts the deliberately small schema language used by Rules.lean;
an unsupported declaration, expression, alias or package expression is an
error. It is not a Lean parser. Compiling the generated Lean and the soundness
assembly remains necessary. The JSON records source references, and reports
unrecorded completeness witnesses and presentation controls as missing.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
PRESENTATION = Path("Mettapedia/Languages/VibeITP/Presentation")
SPEC = Path("Mettapedia/Languages/VibeITP/Spec")
RULES = PRESENTATION / "Rules.lean"
SYNTAX = PRESENTATION / "Syntax.lean"
BASIC = SPEC / "Basic.lean"
THEORY = PRESENTATION / "Theory.lean"
SHAPES = PRESENTATION / "RuleShapes.lean"
MANIFEST = PRESENTATION / "rule-coverage.json"
GENERATOR = Path("scripts/generate_vibe_itp_rule_shapes.py")
SOUND_SOURCES = tuple(PRESENTATION / name for name in (
    "SoundArith.lean", "SoundTerms.lean", "SoundTheorems.lean", "SoundDefinitions.lean"))
EXPECTED_NAMED = 112
EXPECTED_BUILTINS = 11
RENAMES = {"id": "idv", "h": "hh", "args": "argv", "x": "xx"}
HELPER_LEMMAS = {"ms_rInstOther"}


class SourceError(ValueError):
    """The source no longer fits the checked generation profile."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SourceError(message)


def mask_comments(source: str) -> str:
    """Retain offsets, newlines and strings; handle nested Lean comments."""
    output, i, depth, quoted = [], 0, 0, False
    while i < len(source):
        pair, char = source[i:i + 2], source[i]
        if depth:
            if pair in ("/-", "-/"):
                depth += 1 if pair == "/-" else -1
                output.append("  ")
                i += 2
            else:
                output.append("\n" if char == "\n" else " ")
                i += 1
        elif quoted:
            output.append(char)
            i += 1
            if char == "\\":
                require(i < len(source), "unterminated string escape")
                output.append(source[i])
                i += 1
            elif char == '"':
                quoted = False
        elif pair == "/-":
            depth = 1
            output.append("  ")
            i += 2
        elif pair == "--":
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            output.append(" " * (end - i))
            i = end
        else:
            quoted = char == '"'
            output.append(char)
            i += 1
    require(depth == 0 and not quoted, "unterminated comment or string")
    return "".join(output)


def norm(source: str) -> str:
    return re.sub(r"\s+", " ", source).strip()


def split_top(source: str, separator: str = ",") -> list[str]:
    """Split at depth zero, rejecting mismatched delimiters and strings."""
    stack, parts, start, i, quoted = [], [], 0, 0, False
    matching = {")": "(", "]": "[", "}": "{"}
    while i < len(source):
        char = source[i]
        if quoted:
            if char == "\\":
                i += 2
                continue
            quoted = char != '"'
        elif char == '"':
            quoted = True
        elif char in "([{":
            stack.append(char)
        elif char in ")]}":
            require(bool(stack) and stack.pop() == matching[char], "mismatched delimiters")
        elif not stack and source.startswith(separator, i):
            parts.append(source[start:i].strip())
            i += len(separator)
            start = i
            continue
        i += 1
    require(not stack and not quoted, "unterminated group or string")
    parts.append(source[start:].strip())
    return parts


def take_group(source: str, start: int) -> tuple[str, int]:
    require(start < len(source) and source[start] in "([{", "expected delimited group")
    stack, i, quoted = [], start, False
    matching = {")": "(", "]": "[", "}": "{"}
    while i < len(source):
        char = source[i]
        if quoted:
            if char == "\\":
                i += 2
                continue
            quoted = char != '"'
        elif char == '"':
            quoted = True
        elif char in "([{":
            stack.append(char)
        elif char in ")]}":
            require(bool(stack) and stack.pop() == matching[char], "mismatched delimiters")
            if not stack:
                return source[start + 1:i], i + 1
        i += 1
    raise SourceError("unterminated group")


@dataclass(frozen=True)
class Declaration:
    name: str
    header: str
    body: str
    line: int
    namespace: str


def declarations(source: str, kind: str = "def") -> dict[str, Declaration]:
    code = mask_comments(source)
    attributes = r"(?:@\[[^\]\n]+\]\s*)*"
    starts = list(re.finditer(
        r"^" + attributes + r"(?:private\s+)?(?:def|abbrev|theorem|instance|structure|inductive|class|"
        r"opaque|axiom|mutual|end|namespace|section|variable|set_option|open|import)\b",
        code, re.MULTILINE))
    output = {}
    scopes = []
    for index, start in enumerate(starts):
        chunk = code[start.start():starts[index + 1].start() if index + 1 < len(starts) else len(code)]
        scope = re.match(r"(namespace|section|mutual|end)\b(?:\s+([^\s]+))?", chunk)
        if scope:
            if scope[1] == "end":
                require(bool(scopes), "unmatched end in declaration source")
                scopes.pop()
            else:
                scopes.append((scope[1], scope[2] if scope[1] == "namespace" else ""))
            continue
        match = re.match(attributes + r"(?:private\s+)?" + kind + r"\s+([\w.']+)(?![\w.'])", chunk)
        if not match:
            continue
        pieces = split_top(chunk, ":=")
        # Definitions by equations have no :=. They are relevant only to the
        # separately checked Builtin tables, not to direct rule generation.
        if len(pieces) == 1:
            header, body = chunk.strip(), ""
        else:
            header, body = pieces[0], ":=".join(pieces[1:])
        name = match[1]
        require(name not in output, f"duplicate declaration: {name}")
        namespace = ".".join(value for kind, value in scopes if kind == "namespace")
        output[name] = Declaration(name, header, body,
                                  code.count("\n", 0, start.start()) + 1, namespace)
    return output


# Parentheses group applications; they do not add an AST node. A token's
# string/identifier distinction is retained by its leading quote.
TOKEN = re.compile(r'\s*("(?:[^"\\]|\\.)*"|[\w\'.]+|[(),])', re.UNICODE)
Expr = str | tuple["Expr", ...]


def tokens(source: str) -> list[str]:
    output, i = [], 0
    while i < len(source):
        if not source[i:].strip():
            break
        match = TOKEN.match(source, i)
        require(match is not None, f"unsupported pattern syntax near {source[i:i + 32]!r}")
        output.append(match[1])
        i = match.end()
    return output


def expression(source: str) -> Expr:
    stream, i = tokens(source), 0

    def application() -> Expr:
        nonlocal i
        terms = []
        while i < len(stream) and stream[i] not in (")", ","):
            token = stream[i]
            i += 1
            if token == "(":
                term = application()
                require(i < len(stream) and stream[i] == ")", "unterminated pattern application")
                i += 1
            else:
                term = token
            terms.append(term)
        require(bool(terms), "empty pattern application")
        return terms[0] if len(terms) == 1 else tuple(terms)

    result = application()
    require(i == len(stream), f"unconsumed pattern tokens: {stream[i:]}")
    return result


def render(expr: Expr) -> str:
    if isinstance(expr, str):
        return expr
    return " ".join(render(term) if isinstance(term, str) else "(" + render(term) + ")"
                    for term in expr)


def parameters(header: str) -> list[str]:
    result = []
    for match in re.finditer(r"\(([^():]+)\s*:\s*[^():]+\)", header):
        result.extend(match[1].split())
    return result


@dataclass(frozen=True)
class Rule:
    name: str
    id: str
    variables: tuple[str, ...]
    premises: tuple[Expr, ...]
    conclusion: Expr
    line: int


@dataclass(frozen=True)
class Builtin:
    name: str
    slot: int
    arity: int


@dataclass
class Inventory:
    rules: dict[str, Rule]
    order: list[str]
    groups: dict[str, list[str]]
    builtins: list[Builtin]
    aliases: dict[str, Expr]
    arities: dict[str, int]


def parse_inventory(rules_source: str, syntax_source: str, basic_source: str) -> Inventory:
    defs = declarations(rules_source)
    syntax_defs = declarations(syntax_source)
    arities = {name: len(parameters(d.header))
               for name, d in syntax_defs.items()
               if re.search(r"\s:\s*Pattern\s*$", d.header)}
    builtin_constructors = re.search(r"^inductive Builtin where\s*(.*?)^deriving\b",
                                     mask_comments(basic_source), re.M | re.S)
    require(builtin_constructors is not None, "missing Builtin constructors")
    for name in re.findall(r"^\s*\|\s+(\w+)\s*$", builtin_constructors[1], re.M):
        arities["." + name] = 0
    aliases = {}
    for name, d in defs.items():
        if re.search(r"\s:\s*Pattern\s*$", d.header):
            arities[name] = len(parameters(d.header))
            if not parameters(d.header) and name != "mv":
                aliases[name] = expression(d.body)
    require(set(aliases) == {"fvarSym", "byteList8", "patImpl", "patEq"},
            f"unexpected rule-schema aliases: {sorted(aliases)}")

    def expand(expr: Expr, seen: tuple[str, ...] = ()) -> Expr:
        if isinstance(expr, str) and expr in ("fvarSym", "byteList8"):
            require(expr not in seen, f"cyclic schema alias: {expr}")
            return expand(aliases[expr], seen + (expr,))
        if isinstance(expr, tuple):
            return tuple(expand(term, seen) for term in expr)
        return expr

    def validate(expr: Expr, variables: set[str]) -> set[str]:
        if isinstance(expr, str):
            require(expr in arities and arities[expr] == 0, f"unknown/nonconstant schema atom: {expr}")
            return set()
        require(isinstance(expr[0], str), "computed pattern head is unsupported")
        head = expr[0]
        if head == "mv":
            require(len(expr) == 2 and isinstance(expr[1], str) and expr[1].startswith('"'),
                    "mv requires one quoted name")
            variable = json.loads(expr[1])
            require(variable in variables, f"undeclared schema metavariable: {variable}")
            return {variable}
        require(head in arities and len(expr) - 1 == arities[head],
                f"unknown/wrong-arity schema application: {head}/{len(expr) - 1}")
        used = set()
        for argument in expr[1:]:
            used.update(validate(argument, variables))
        return used

    rules = {}
    for name, d in defs.items():
        if name == "mkRule":
            require(norm(d.header) ==
                    "def mkRule (id : String) (vars : List String) (premises : List Pattern) (conclusion : Pattern) : FORule" and
                    norm(d.body) == "⟨id, vars, premises, conclusion⟩", "unsupported mkRule definition")
            continue
        if not re.fullmatch(r"def\s+" + re.escape(name) + r"\s*:\s*FORule", norm(d.header)):
            require(not re.search(r"\bFORule\s*$", d.header) or "List FORule" in d.header,
                    f"unsupported parameterized rule declaration: {name}")
            continue
        require(re.fullmatch(r"r\w+", name) is not None, f"unexpected direct rule name: {name}")
        match = re.match(r'\s*mkRule\s+("(?:[^"\\]|\\.)*")\s*', d.body)
        require(match is not None, f"{name}: expected direct mkRule")
        rule_id, remaining = json.loads(match[1]), d.body[match.end():].lstrip()
        require(rule_id.startswith("vibe-"), f"{name}: unexpected rule ID: {rule_id}")
        variable_text, end = take_group(remaining, 0)
        require(remaining[0] == "[", f"{name}: variable vector must be a list")
        variable_parts = split_top(variable_text) if variable_text.strip() else []
        require(all(re.fullmatch(r'"[A-Za-z][A-Za-z0-9]*"', v) for v in variable_parts),
                f"{name}: unsupported variable names")
        variables = tuple(json.loads(v) for v in variable_parts)
        require(len(set(variables)) == len(variables), f"{name}: duplicate variables")
        require(len(set(RENAMES.get(v, v) for v in variables)) == len(variables),
                f"{name}: generated variable names collide")
        remaining = remaining[end:].lstrip()
        premise_text, end = take_group(remaining, 0)
        require(remaining[0] == "[", f"{name}: premises must be a list")
        premises = tuple(expand(expression(p)) for p in split_top(premise_text)) if premise_text.strip() else ()
        conclusion = expand(expression(remaining[end:].strip()))
        used = set()
        for expr in (*premises, conclusion):
            used.update(validate(expr, set(variables)))
        require(used == set(variables), f"{name}: unused variables: {sorted(set(variables) - used)}")
        rules[name] = Rule(name, rule_id, variables, premises, conclusion, d.line)
    require(len(rules) == EXPECTED_NAMED,
            f"named rule count changed: {len(rules)}; expected {EXPECTED_NAMED}")
    duplicates = [rid for rid, count in Counter(r.id for r in rules.values()).items() if count != 1]
    require(not duplicates, f"duplicate rule IDs: {duplicates}")

    basic_defs = declarations(basic_source)
    require("Builtin.all" in basic_defs, "missing Builtin.all")
    all_body = basic_defs["Builtin.all"].body.strip()
    all_text, end = take_group(all_body, 0)
    require(all_body[0] == "[" and not all_body[end:].strip(), "unsupported Builtin.all")
    builtin_names = [item.removeprefix(".") for item in split_top(all_text)]
    require(all(re.fullmatch(r"\.[A-Za-z]\w*", item) for item in split_top(all_text)),
            "unsupported Builtin.all element")
    basic_code = mask_comments(basic_source)
    constructors = re.search(r"^inductive Builtin where\s*(.*?)^deriving\b", basic_code, re.M | re.S)
    require(constructors is not None, "missing Builtin constructors")
    constructor_names = re.findall(r"^\s*\|\s+(\w+)\s*$", constructors[1], re.M)
    require(builtin_names == constructor_names and len(set(builtin_names)) == EXPECTED_BUILTINS,
            "Builtin.all must enumerate every constructor once in declaration order")

    def builtin_table(name: str) -> dict[str, int]:
        require(name in basic_defs, f"missing {name}")
        header = basic_defs[name].header
        entries = re.findall(r"\|\s*\.(\w+)\s*=>\s*(\d+)\s*(?=\||$)", header)
        table = dict((n, int(v)) for n, v in entries)
        require(len(entries) == len(builtin_names) and set(table) == set(builtin_names),
                f"unsupported/incomplete/repeated {name}")
        return table

    slots, builtin_arities = builtin_table("Builtin.slot"), builtin_table("Builtin.arity")
    require([slots[name] for name in builtin_names] == list(range(2, 13)),
            "builtin slot profile changed")
    builtins = [Builtin(name, slots[name], builtin_arities[name]) for name in builtin_names]
    require(norm(defs["builtinRules"].body) ==
            'Builtin.all.map fun b => mkRule ("vibe-builtin-" ++ toString b.slot) [] [] (jSymDecl (patBuiltinSym b))',
            "unsupported builtinRules expression")

    lists = {name: d for name, d in defs.items()
             if re.fullmatch(r"def\s+" + re.escape(name) + r"\s*:\s*List FORule", norm(d.header))}
    groups = {}

    def flatten(name: str, seen: tuple[str, ...] = ()) -> list[str]:
        require(name in lists, f"unknown rule-list reference: {name}")
        require(name not in seen, f"cyclic rule-list reference: {name}")
        if name in groups:
            return groups[name]
        if name == "builtinRules":
            result = ["builtin:" + b.name for b in builtins]
        else:
            body = lists[name].body.strip()
            if body.startswith("["):
                content, end = take_group(body, 0)
                require(not body[end:].strip(), f"{name}: unsupported list suffix")
                result = split_top(content) if content.strip() else []
                require(all(item in rules for item in result), f"{name}: unknown direct rule")
            else:
                refs = split_top(body, "++")
                require(all(re.fullmatch(r"\w+", ref) for ref in refs), f"{name}: unsupported package expression")
                result = [rule for ref in refs for rule in flatten(ref, seen + (name,))]
        groups[name] = result
        return result

    require("kernelRules" in lists, "missing kernelRules")
    order = flatten("kernelRules")
    expected = set(rules) | {"builtin:" + b.name for b in builtins}
    require(set(order) == expected, f"kernel coverage mismatch: missing {sorted(expected - set(order))}; "
            f"extra {sorted(set(order) - expected)}")
    require(all(n == 1 for n in Counter(order).values()), "kernelRules repeats a rule")
    for name in lists:
        flatten(name)
    return Inventory(rules, order, groups, builtins, aliases, arities)


def instantiate(expr: Expr) -> Expr:
    if isinstance(expr, str):
        return expr
    if expr[0] == "mv":
        return RENAMES.get(json.loads(expr[1]), json.loads(expr[1]))
    return tuple(instantiate(term) for term in expr)


def parenthesized(expr: Expr) -> str:
    return "(" + render(expr) + ")"


def semantic_matches(inventory: Inventory, sources: dict[Path, str]) -> tuple[dict, list]:
    lemmas, helpers = {}, []
    for path in SOUND_SOURCES:
        for name, d in declarations(sources[path], "theorem").items():
            if not name.startswith("ms_"):
                continue
            require(name not in lemmas, f"duplicate semantic lemma: {name}")
            if name in HELPER_LEMMAS:
                helpers.append({"declaration": name, "source": str(path), "line": d.line,
                                "role": "helper, not a fixed kernel rule"})
                continue
            require(name.removeprefix("ms_") in inventory.rules,
                    f"semantic lemma has no fixed named rule: {name}")
            rule = inventory.rules[name.removeprefix("ms_")]
            signature_parts = split_top(d.header, ":")
            require(len(signature_parts) >= 2, f"{name}: unsupported theorem header")
            signature = [signature_parts[0], ":".join(signature_parts[1:])]
            type_text = signature[1].strip()
            expected_variables = [RENAMES.get(v, v) for v in rule.variables]
            if expected_variables:
                quantifier = re.match(r"∀\s+([^:,]+)\s*:\s*Pattern\s*,\s*", type_text)
                require(quantifier is not None and quantifier[1].split() == expected_variables,
                        f"{name}: variable vector differs from {rule.name}")
                type_text = type_text[quantifier.end():]
            clauses = split_top(type_text, "→")
            meaning_patterns = []
            for clause in clauses:
                match = re.fullmatch(r"Meaning\s+T\s+(.+)", clause, re.S)
                require(match is not None, f"{name}: unsupported semantic clause")
                meaning_patterns.append(expression(match[1]))
            expected = [instantiate(p) for p in (*rule.premises, rule.conclusion)]
            require(meaning_patterns == expected,
                    f"{name}: semantic premises/conclusion differ from {rule.name}")
            lemmas[name] = {"declaration": name, "source": str(path), "line": d.line,
                            "header_sha256": sha256(norm(d.header)), "schema_match": "exact",
                            "explicit_parameters": norm(signature[0]).removeprefix("theorem " + name).strip()}
    expected_names = {"ms_" + name for name in inventory.rules}
    require(set(lemmas) == expected_names,
            f"semantic lemma coverage differs: missing {sorted(expected_names - set(lemmas))}; "
            f"extra {sorted(set(lemmas) - expected_names)}")
    require({h["declaration"] for h in helpers} == HELPER_LEMMAS, "semantic helper census changed")
    return lemmas, helpers


def sha256(source: str) -> str:
    return hashlib.sha256(source.encode("utf-8")).hexdigest()


def generate_shapes(inventory: Inventory) -> str:
    output = ['''import Mettapedia.Languages.VibeITP.Presentation.Instances

/-!
# Vibe-ITP presentation: rule instance shapes

Generated by `scripts/generate_vibe_itp_rule_shapes.py` from `Rules`.
Each named rule has its exact instance shape, a conditional soundness transfer,
and an introduction lemma in any containing rule list. Built-in declaration
rules are covered uniformly by the final three lemmas.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Languages.VibeITP.Spec
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
''']
    helpers = ('cP1 cPO cPI cN0 cNPos cU0 cUS cFalse cTrue cNil cCons cKConst cKFvar cSym cAnn '
               'cBVar cLit cApp jPSucc jPAdd jPAddC jNAdd jNLt jNLe jPMul jNMul jNDivMod jNMod64 '
               'jPBits jNWord jNMonus jNMax jBOr jLen jNth jBytes jSymDecl jWf jWfArgs jKindFv jDepth '
               'jHasFv jAnnArgs jShift jShiftArgs jSubst jSubstArgs jSubstTop jInst jInstArgs '
               'jNatLit jArities jHintsIn jOcc jOccArgs jEtas jDescBVars jDefStmt jThm '
               'closedApp1 closedApp2 patAnnClosed patImpl patEq').split()
    simpset = ('FORule.instPremises, FORule.instConclusion, FORule.bindings, mkRule, mv, '
               'ab_apply, ab_fvar_hit, ab_fvar_miss, fvarSym, byteList8, ' + ', '.join(helpers))

    def pick(count: int, name: str) -> str:
        if count == 0:
            return ""
        if count == 1:
            return f"    rcases {name} with rfl\n    assumption"
        return f"    rcases {name} with " + " | ".join(["rfl"] * count) + " <;> assumption"

    for name in inventory.order:
        if name.startswith("builtin:"):
            continue
        rule = inventory.rules[name]
        variables = [RENAMES.get(v, v) for v in rule.variables]
        binders, applied = " ".join(variables), " ".join(variables)
        arguments = "[" + ", ".join(variables) + "]"
        premises = [instantiate(p) for p in rule.premises]
        conclusion = instantiate(rule.conclusion)
        premise_list = "[" + ", ".join(render(p) for p in premises) + "]"
        conclusion_text = parenthesized(conclusion)
        binder = "(" + binders + " : Pattern) " if variables else ""
        output.append(f'''theorem inst_{name} {binder}:
    {name}.instPremises {arguments} = {premise_list} ∧
      {name}.instConclusion {arguments} = {conclusion_text} := by
  constructor <;> simp [{name}, {simpset}]
''')
        hypotheses = " → ".join("P " + parenthesized(p) for p in (*premises, conclusion))
        quantifier = "∀ " + binders + " : Pattern, " if variables else ""
        premise_arguments = " ".join(["(hprem _ (by simp))"] * len(premises))
        output.append(f'''theorem sound_{name} {{P : Pattern → Prop}}
    (h : {quantifier}{hypotheses}) :
    ∀ args : List Pattern, args.length = {name}.vars.length →
      (∀ x ∈ {name}.instPremises args, P x) → P ({name}.instConclusion args) := by
  intro args hlen hprem
  match args, hlen with
  | {arguments}, _ =>
    rw [(inst_{name} {applied}).1] at hprem
    rw [(inst_{name} {applied}).2]
    exact h {applied} {premise_arguments}
''')
        data_hypotheses = " ".join(f"(hd_{v} : IsData {v})" for v in variables)
        premise_hypotheses = " ".join(f"(h{k} : FODerivable R {parenthesized(p)})"
                                      for k, p in enumerate(premises))
        implicit = "{" + binders + " : Pattern}" if variables else ""
        output.append(f'''theorem intro_{name} {{R : List FORule}} (hr : {name} ∈ R) {implicit}
    {data_hypotheses} {premise_hypotheses} :
    FODerivable R {conclusion_text} := by
  apply FODerivable.intro hr {arguments} rfl
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
{pick(len(variables), "ha")}
  · exact (inst_{name} {applied}).2
  · rw [(inst_{name} {applied}).1]
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
{pick(len(premises), "hx")}
''')
    output.append('''theorem inst_builtin (b : Builtin) :
    (mkRule ("vibe-builtin-" ++ toString b.slot) [] []
      (jSymDecl (patBuiltinSym b))).instPremises [] = [] ∧
    (mkRule ("vibe-builtin-" ++ toString b.slot) [] []
      (jSymDecl (patBuiltinSym b))).instConclusion [] = jSymDecl (patBuiltinSym b) := by
  constructor <;> simp [FORule.instPremises, FORule.instConclusion,
    FORule.bindings, mkRule, jSymDecl, ab_apply]

theorem sound_builtin {P : Pattern → Prop} (b : Builtin)
    (h : P (jSymDecl (patBuiltinSym b))) :
    ∀ args : List Pattern, args.length =
      (mkRule ("vibe-builtin-" ++ toString b.slot) [] []
        (jSymDecl (patBuiltinSym b))).vars.length →
      (∀ x ∈ (mkRule ("vibe-builtin-" ++ toString b.slot) [] []
        (jSymDecl (patBuiltinSym b))).instPremises args, P x) →
      P ((mkRule ("vibe-builtin-" ++ toString b.slot) [] []
        (jSymDecl (patBuiltinSym b))).instConclusion args) := by
  intro args hlen _
  have ha : args = [] := List.length_eq_zero_iff.mp hlen
  subst args
  rw [(inst_builtin b).2]
  exact h

theorem intro_builtin {R : List FORule} (b : Builtin)
    (hr : mkRule ("vibe-builtin-" ++ toString b.slot) [] []
      (jSymDecl (patBuiltinSym b)) ∈ R) : FODerivable R (jSymDecl (patBuiltinSym b)) := by
  apply FODerivable.intro hr [] rfl
  · simp
  · exact (inst_builtin b).2
  · rw [(inst_builtin b).1]
    simp
''')
    output.append("end Mettapedia.Languages.VibeITP.Presentation\n")
    return "\n".join(output)


def reference_sites(sources: dict[Path, str], names: set[str]) -> dict[str, list[dict]]:
    """Find direct references in declaration bodies, excluding comments/strings."""
    result = {name: [] for name in names}
    for path, source in sorted(sources.items()):
        for kind in ("theorem", "def"):
            for declaration in declarations(source, kind).values():
                code = re.sub(r'"(?:[^"\\]|\\.)*"', '""', declaration.body)
                for name in names.intersection(re.findall(r"\b[A-Za-z_]\w*\b", code)):
                    result[name].append(source_reference(path, declaration))
    return result


def declaration_sites(sources: dict[Path, str], names: set[str]) -> dict[str, list[dict]]:
    result = {name: [] for name in names}
    for path, source in sorted(sources.items()):
        for name, declaration in declarations(source, "theorem").items():
            if name in names:
                result[name].append(source_reference(path, declaration, header=True))
    return result


def source_reference(path: Path, declaration: Declaration, header: bool = False) -> dict:
    reference = {"declaration": declaration.name, "namespace": declaration.namespace,
                 "source": str(path), "line": declaration.line}
    if not declaration.header.startswith("private "):
        reference["qualified_declaration"] = declaration.namespace + "." + declaration.name
    if header:
        reference.update(header=norm(declaration.header),
                         header_sha256=sha256(norm(declaration.header)))
    return reference


# These mappings describe the judgment or inference tested by each public
# control. A judgment case qualifies its relation, not every production path
# used by a recursive witness. Positional arity qualification is kept separate
# from semantic acceptance and refusal cases.
KERNEL_CONTROLS = PRESENTATION / "KernelControls.lean"
VALIDATION = PRESENTATION / "Validation.lean"
CONTROL_NAMESPACE = "Mettapedia.Languages.VibeITP.Presentation.KernelControls"
ADMISSION_NAMESPACE = "Mettapedia.Languages.VibeITP.Presentation.AdmissionControls"

# name: (outcome, named rules/families, judgment conclusions, proof/article route)
KERNEL_CONTROL_CASES = {
    "modus_ponens_accepts": ("accepted_article", ("rMp",), (), ("mpArticle",)),
    "harmless_duplicate_premise_accepts": ("accepted_article", ("rMp",), (), ("rMp",)),
    "modus_ponens_wrong_goal_rejects": ("rejected_article", ("rMp",), (), ("mpArticle",)),
    "modus_ponens_wrong_premise_rejects": ("rejected_article", ("rMp",), (), ("rMp",)),
    "modus_ponens_reversed_premises_rejects": ("rejected_article", ("rMp",), (), ("rMp",)),
    "modus_ponens_wrong_argument_count_rejects": ("rejected_article", ("rMp",), (), ("rMp",)),
    "application_arity_no_formation": ("nonderivability", (), ("jWf",), ("meaning_of_foDerivable",)),
    "application_arity_rejects": ("rejected_article", (), ("jWf",), ("application_arity_no_formation",)),
    "shift_under_binder_accepts": ("accepted_article", (), ("jShift",), ("complete_shift",)),
    "shift_wrong_binder_result_no_derivation": ("nonderivability", (), ("jShift",), ("shift_of_foDerivable",)),
    "shift_prunes_closed_accepts": ("accepted_article", (), ("jShift",), ("complete_shift",)),
    "shift_word_overflow_no_derivation": ("nonderivability", (), ("jShift",), ("shift_refusal",)),
    "shift_binder_offset_overflow_no_derivation": ("nonderivability", (), ("jShiftArgs",), ("shiftList_refusal_iff",)),
    "substitution_last_argument_accepts": ("accepted_article", (), ("jSubstTop",), ("complete_substTop",)),
    "substitution_first_argument_accepts": ("accepted_article", (), ("jSubstTop",), ("complete_substTop",)),
    "substitution_forward_order_no_derivation": ("nonderivability", (), ("jSubstTop",), ("substTop_of_foDerivable",)),
    "substitution_under_binder_accepts": ("accepted_article", (), ("jSubstTop",), ("complete_substTop",)),
    "substitution_capturing_result_no_derivation": ("nonderivability", (), ("jSubstTop",), ("substTop_of_foDerivable",)),
    "substitution_shift_overflow_no_derivation": ("nonderivability", (), ("jSubst",), ("substGo_refusal",)),
    "zero_argument_substitution_prunes_accepts": ("accepted_article", (), ("jSubstTop",), ("complete_substTop_shape",)),
    "instantiation_under_binder_operation_accepts": ("accepted_article", (), ("jInst",), ("complete_inst",)),
    "instantiation_under_binder_theorem_accepts": ("accepted_article", ("rInst",), (), ("complete_instantiateStatement",)),
    "instantiation_capturing_result_no_derivation": ("nonderivability", (), ("jInst",), ("instGo_of_foDerivable",)),
    "instantiation_other_lower_head_accepts": ("accepted_article", (), ("jInst",), ("complete_inst",)),
    "instantiation_other_higher_head_accepts": ("accepted_article", (), ("jInst",), ("complete_inst",)),
    "instantiation_prunes_no_fvar_accepts": ("accepted_article", (), ("jInst",), ("complete_inst",)),
    "instantiation_shift_overflow_no_derivation": ("nonderivability", (), ("jInst",), ("instGo_refusal_iff",)),
    "instantiation_binder_offset_overflow_no_derivation": ("nonderivability", (), ("jInst",), ("instGo_refusal_iff",)),
    "instantiation_value_exceeds_arity_refused": ("computation", ("rInst",), (), ("instantiateStatement",)),
    "instantiation_value_exceeds_arity_no_guard_derivation": ("nonderivability", (), ("jNLe",), ("meaning_of_foDerivable",)),
    "instantiation_value_exceeds_arity_guard_rejects": ("rejected_article", (), ("jNLe",), ("instantiation_value_exceeds_arity_no_guard_derivation",)),
    "instantiation_constant_refused": ("computation", ("rInst",), (), ("instantiateStatement",)),
    "definition_conditions_accept": ("accepted_article", (), ("jDefStmt",), ("complete_defStmt",)),
    "surplus_valid_definition_hints_accept": ("accepted_article", (), ("jDefStmt",), ("complete_defStmt",)),
    "missing_definition_hint_no_derivation": ("nonderivability", (), ("jDefStmt",), ("no_defStmt_of_refused",)),
    "out_of_range_definition_hint_no_derivation": ("nonderivability", (), ("jDefStmt",), ("no_defStmt_of_refused",)),
    "wrong_definition_parameter_hint_no_derivation": ("nonderivability", (), ("jDefStmt",), ("no_defStmt_of_refused",)),
    "open_definition_body_no_derivation": ("nonderivability", (), ("jDefStmt",), ("no_defStmt_of_refused",)),
    "definition_equation_leaf_accepts": ("accepted_article", ("definitionRule",), (), ("definitionRuleId",)),
    "number_literal_boundary_encoding": ("computation", ("rNatlitSmall", "rNatlitLarge"), (), ("natLiteral",)),
    "literal_is_nat_accepts": ("accepted_article", ("rLitIsnat",), (), ("complete_litIsNat",)),
    "literal_less_than_accepts": ("accepted_article", ("rLitLt",), (), ("complete_litLt",)),
    "literal_addition_wraps": ("computation", ("rLitAdd",), (), ("litAddStatement",)),
    "literal_addition_wraparound_accepts": ("accepted_article", ("rLitAdd",), (), ("complete_litAdd",)),
    "literal_multiplication_wraps": ("computation", ("rLitMul",), (), ("litMulStatement",)),
    "literal_multiplication_wraparound_accepts": ("accepted_article", ("rLitMul",), (), ("complete_litMul",)),
    "literal_nonzero_division_accepts": ("accepted_article", ("rLitDiv",), (), ("complete_litDiv",)),
    "division_zero_no_operation_derivation": ("nonderivability", (), ("jNDivMod",), ("meaning_of_foDerivable",)),
    "division_zero_rejects": ("rejected_article", (), ("jNDivMod",), ("division_zero_no_operation_derivation",)),
    "literal_byte_length_accepts": ("accepted_article", ("rLitLength",), (), ("complete_litLength",)),
    "literal_byte_in_range_accepts": ("accepted_article", ("rLitGet",), (), ("complete_litGet",)),
    "byte_index_bounds_no_operation_derivation": ("nonderivability", (), ("jNth",), ("meaning_of_foDerivable",)),
    "byte_index_bounds_rejects": ("rejected_article", (), ("jNth",), ("byte_index_bounds_no_operation_derivation",)),
    "byte_index_at_length_rejects": ("rejected_article", (), ("jNth",), ("byte_index_bounds_rejects",)),
}

ADMISSION_CONTROL_CASES = {
    "symbol_leaf_accepts": ("accepted_article", ("symbolRule",), (), ("symbolRuleId",)),
    "axiom_leaf_accepts": ("accepted_article", ("axiomRule",), (), ("axiomRuleId",)),
    "definition_leaf_accepts": ("accepted_article", ("definitionRule",), (), ("definitionRuleId",)),
    "harmless_duplicate_axiom_accepts": ("accepted_article", ("axiomRule",), (), ("axiomRuleId",)),
    "wrong_symbol_goal_rejects": ("rejected_article", ("symbolRule",), (), ("symbolRuleId",)),
    "wrong_axiom_goal_rejects": ("rejected_article", ("axiomRule",), (), ("axiomRuleId",)),
    "extra_leaf_child_rejects": ("rejected_article", ("axiomRule",), (), ("axiomRuleId",)),
    "extra_leaf_argument_rejects": ("rejected_article", ("axiomRule",), (), ("axiomRuleId",)),
    "duplicate_rule_id_rejects": ("rejected_package", ("axiomRule",), (), ("axiomRule",)),
    "wrong_constructor_arity_rejects": ("rejected_package", (), (), ("mkRule",)),
}

QUALIFICATION_CASES = {
    "fixed_rule_argument_count_rejects": ("fixed", "kernelRules"),
    "fixed_rule_argument_count_controls": ("fixed", "kernelRules"),
    "admitted_rule_argument_count_rejects": ("admitted", "theoryRules"),
    "admitted_rule_argument_count_controls": ("admitted", "theoryRules"),
    "symbol_rule_argument_count_rejects": ("symbolRule", "symbolRule"),
    "axiom_rule_argument_count_rejects": ("axiomRule", "axiomRules"),
    "definition_rule_argument_count_rejects": ("definitionRule", "theoryDefinitionRules"),
}
CONTROL_SUPPORT = {
    CONTROL_NAMESPACE: {"controlTheory_hosted", "variationTheory_hosted", "wrong_argument_arity_rejects",
                        "tooManyArguments_length", "tooManyArguments_valid", "parameter_isFvarOf", "atomA_isFvarOf"},
    ADMISSION_NAMESPACE: {"controlTheory_hosted"},
}


def checked_control_cases(inventory: Inventory, sources: dict[Path, str]) -> tuple[list, list]:
    declarations_by_path = {p: {**declarations(s, "def"), **declarations(s, "theorem")}
                            for p, s in sources.items() if p.suffix == ".lean"}
    names = {}
    for path, ds in declarations_by_path.items():
        for name, declaration in ds.items():
            names.setdefault(name, []).append(source_reference(path, declaration))
    intro_targets = {"intro_" + r: [r] for r in inventory.rules}
    intro_targets.update({"intro_builtin": ["builtin:" + b.name for b in inventory.builtins],
                          "builtinRules": ["builtin:" + b.name for b in inventory.builtins],
                          **{"intro_" + family: [family] for family in
                             ("symbolRule", "axiomRule", "definitionRule")}})

    def construction_dependencies(route: tuple[str, ...]) -> tuple[list[str], list[dict]]:
        todo, visited, dependencies, references = list(route), set(), set(), []
        while todo:
            name = todo.pop()
            if name in visited:
                continue
            visited.add(name)
            require(name in names and len(names[name]) == 1,
                    f"ambiguous or missing construction route: {name}")
            reference = names[name][0]
            declaration = declarations_by_path[Path(reference["source"])][name]
            references.append(reference)
            body = re.sub(r'"(?:[^"\\]|\\.)*"', '""', declaration.body)
            words = set(re.findall(r"\b[A-Za-z_]\w*\b", body))
            for word in words:
                dependencies.update(intro_targets.get(word, []))
                if word in inventory.rules:
                    dependencies.add(word)
                if word.startswith("complete_") and word in names:
                    todo.append(word)
        return sorted(dependencies), sorted(references, key=lambda r: (r["source"], r["line"]))
    targets = set(inventory.order) | {"symbolRule", "axiomRule", "definitionRule"}
    conclusions = {name: (r.conclusion[0] if isinstance(r.conclusion, tuple) else r.conclusion)
                   for name, r in inventory.rules.items()}
    cases = []
    for path, namespace, mapping in ((KERNEL_CONTROLS, CONTROL_NAMESPACE, KERNEL_CONTROL_CASES),
                                      (VALIDATION, ADMISSION_NAMESPACE, ADMISSION_CONTROL_CASES)):
        require(path in sources, f"missing control source: {path}")
        public = {name: d for name, d in declarations(sources[path], "theorem").items()
                  if d.namespace == namespace and not d.header.startswith("private ")}
        known = set(mapping) | CONTROL_SUPPORT[namespace]
        if namespace == CONTROL_NAMESPACE:
            known |= set(QUALIFICATION_CASES)
        require(set(public) == known,
                f"control inventory changed in {namespace}: unclassified {sorted(set(public) - known)}; "
                f"missing {sorted(known - set(public))}")
        for name, (outcome, direct_targets, judgments, route) in mapping.items():
            declaration = public[name]
            code = re.sub(r'"(?:[^"\\]|\\.)*"', '""', declaration.header + "\n" + declaration.body)
            require(set(direct_targets) <= targets, f"{name}: unknown mapped rule/family")
            require(all(j in inventory.arities and j.startswith("j") for j in judgments),
                    f"{name}: unknown mapped judgment")
            require(all(re.search(r"\b" + re.escape(j) + r"\b", declaration.header) for j in judgments),
                    f"{name}: mapped judgment does not occur in its statement")
            require(all(re.search(r"\b" + re.escape(r) + r"\b", code) and r in names for r in route),
                    f"{name}: missing declared proof/article route")
            checked_outcome(declaration, outcome)
            matched = set(direct_targets) | {r for r, j in conclusions.items() if j in judgments}
            dependencies, construction_routes = construction_dependencies(route)
            cases.append({**source_reference(path, declaration, header=True), "outcome": outcome,
                          "rule_targets": sorted(matched), "direct_targets": list(direct_targets),
                          "judgment_targets": list(judgments), "mapping_scope": "judgment_or_inference",
                          "route_references": [ref for r in route for ref in names[r]],
                          "constructive_helper_rule_dependencies": dependencies,
                          "constructive_helper_routes": construction_routes,
                          "dependency_scope_note": "These are source dependencies of general constructive helpers, not claims that a concrete article exercises every production branch."})
    qualification = []
    kernel_declarations = declarations(sources[KERNEL_CONTROLS], "theorem")
    for name, (scope, membership) in QUALIFICATION_CASES.items():
        declaration = kernel_declarations[name]
        checked_outcome(declaration, "rejected_article")
        require(re.search(r"\b" + membership + r"\b", declaration.header + "\n" + declaration.body) is not None,
                f"{name}: qualification membership changed")
        qualification.append({**source_reference(KERNEL_CONTROLS, declaration, header=True),
                              "outcome": "rejected_article", "scope": scope,
                              "membership": membership, "mapping_scope": "positional_argument_count",
                              "semantic_positive_case": False})
    return cases, qualification


def checked_outcome(declaration: Declaration, outcome: str) -> None:
    statement = norm(declaration.header)
    if outcome in ("accepted_article", "rejected_article"):
        expected = "true" if outcome == "accepted_article" else "false"
        require(re.search(r"\bcheckRaw\b", statement) is not None and statement.endswith("= " + expected),
                f"{declaration.name}: expected actual checkRaw outcome {expected}")
    elif outcome == "nonderivability":
        require("¬ FODerivable" in statement, f"{declaration.name}: expected nonderivability statement")
    elif outcome == "rejected_package":
        require(".isValid = false" in statement, f"{declaration.name}: expected package rejection")
    else:
        require(outcome == "computation", f"unknown control outcome: {outcome}")


def required_theorem_references(sources: dict[Path, str], path: Path, names: tuple[str, ...]) -> list[dict]:
    require(path in sources, f"missing endpoint source: {path}")
    ds = declarations(sources[path], "theorem")
    require(all(name in ds for name in names), f"missing endpoint in {path}: {sorted(set(names) - set(ds))}")
    return [source_reference(path, ds[name], header=True) for name in names]


RELATED_SPEC_CONTROLS = {
    "rMp": {"positive": ["modus_ponens_proves_challenge"],
            "negative": ["modus_ponens_premise_mismatch"]},
    "rInst": {"positive": ["instantiation_plugs_argument", "instantiation_under_binder"],
              "negative": ["value_too_deep_for_arity", "constant_cannot_be_instantiated"]},
    "rWfApp": {"positive": [], "negative": ["arity_mismatch"]},
    "rWfBvar": {"positive": [], "negative": ["largest_word_index_unbuildable"]},
    "rLitAdd": {"positive": ["literal_addition_wraps"], "negative": []},
    "rLitLt": {"positive": [], "negative": ["literal_order_requires_less"]},
    "rLitDiv": {"positive": [], "negative": ["division_by_zero_refused"]},
    "rLitGet": {"positive": ["byte_index_in_range"], "negative": ["byte_index_bounded"]},
    "rDefstmt": {"positive": ["definition_equation_satisfies"],
                 "negative": ["open_definition_body_refused", "definition_hint_mismatch"]},
    "symbolRule": {"positive": [], "negative": ["missing_symbol"]},
    "axiomRule": {"positive": ["axiom_satisfies_challenge"], "negative": ["open_axiom_refused"]},
    "definitionRule": {"positive": ["definition_equation_satisfies"],
                       "negative": ["open_definition_body_refused", "definition_hint_mismatch"]},
}


def generate_manifest(inventory: Inventory, sources: dict[Path, str], shapes: str) -> str:
    lemmas, helpers = semantic_matches(inventory, sources)
    soundness_sources = {p: s for p, s in sources.items()
                         if "Soundness" in p.name or p.name == "SoundAdmissions.lean"}
    completeness_sources = {p: s for p, s in sources.items()
                            if "Completeness" in p.name or p.name.startswith("Complete")}
    for source in soundness_sources.values():
        for declaration in declarations(source, "theorem").values():
            body = re.sub(r'"(?:[^"\\]|\\.)*"', '""', declaration.body)
            for transfer in set(re.findall(r"\bsound_r\w+\b", body)):
                rule_name = transfer.removeprefix("sound_")
                require(rule_name in inventory.rules, f"unknown dispatch rule: {rule_name}")
                require(re.search(r"\bms_" + re.escape(rule_name) + r"\b", body) is not None,
                        f"{declaration.name}: {transfer} is not paired with ms_{rule_name}")
    transfers = reference_sites(soundness_sources, {"sound_" + name for name in inventory.rules})
    constructors = reference_sites(completeness_sources, {"intro_" + name for name in inventory.rules} |
                                  {"intro_builtin", "builtinRules", "intro_symbolRule", "intro_axiomRule", "intro_definitionRule"})
    control_cases, qualification_cases = checked_control_cases(inventory, sources)
    admission_semantics = declaration_sites(soundness_sources,
        {"ms_builtin", "ms_builtinRules", "ms_symbolRule", "ms_axiomRule", "ms_definitionRule"})
    admission_introductions = declaration_sites(soundness_sources,
        {"intro_symbolRule", "intro_axiomRule", "intro_definitionRule"})
    admission_dispatch = reference_sites(soundness_sources,
        {"ms_builtinRules", "ms_symbolRule", "ms_axiomRule", "ms_definitionRule"})
    control_declarations = declarations(sources[SPEC / "Controls.lean"], "theorem")
    for related in RELATED_SPEC_CONTROLS.values():
        require(all(name in control_declarations for polarity in related.values() for name in polarity),
                "related specification control is missing")

    def related_controls(name: str) -> dict:
        related = RELATED_SPEC_CONTROLS.get(name, {"positive": [], "negative": []})
        return {polarity: [{"source": str(SPEC / "Controls.lean"), "declaration": declaration,
                            "line": control_declarations[declaration].line} for declaration in names]
                for polarity, names in related.items()}

    def evidence(sites: list[dict], absent: str) -> dict:
        return {"status": "source_references" if sites else absent, "references": sites}

    def presentation_controls(name: str) -> dict:
        focused = [case for case in control_cases if name in case["rule_targets"]]
        indirect = [case for case in control_cases if name in case["constructive_helper_rule_dependencies"]]
        scope = "fixed" if name in inventory.order else "admitted"
        qualification = [case for case in qualification_cases if case["scope"] in (scope, name)]
        status = "focused_judgment_or_inference" if focused else "qualification_only" if qualification else "missing"
        compact = ("declaration", "namespace", "qualified_declaration", "source", "line", "outcome", "mapping_scope")
        return {"status": status,
                "scope_note": "Judgment cases do not claim every production branch was exercised. Positional argument-count rejection supplies no semantic positive case.",
                "qualification_rejections": [{k: c[k] for k in compact} for c in qualification],
                "focused_cases": [{k: c[k] for k in compact} for c in focused],
                "indirect_constructive_helper_dependencies": [{k: c[k] for k in compact} for c in indirect],
                "positive_article_examples": [c["qualified_declaration"] for c in focused if c["outcome"] == "accepted_article"],
                "negative_article_examples": [c["qualified_declaration"] for c in focused if c["outcome"] == "rejected_article"],
                "nonderivability_examples": [c["qualified_declaration"] for c in focused if c["outcome"] == "nonderivability"],
                "package_rejection_examples": [c["qualified_declaration"] for c in focused if c["outcome"] == "rejected_package"],
                "computation_examples": [c["qualified_declaration"] for c in focused if c["outcome"] == "computation"]}

    fixed = []
    builtin_map = {b.name: b for b in inventory.builtins}
    for position, name in enumerate(inventory.order):
        if name.startswith("builtin:"):
            builtin = builtin_map[name.removeprefix("builtin:")]
            fixed.append({"position": position, "id": "vibe-builtin-" + str(builtin.slot),
                "kind": "builtin_declaration", "declaration": "builtinRules", "builtin": builtin.name,
                "slot": builtin.slot, "arity": builtin.arity, "variables": [], "premises": [],
                "conclusion": "jSymDecl (patBuiltinSym ." + builtin.name + ")",
                "source": str(RULES),
                "generated": {"instance": "inst_builtin", "transfer": "sound_builtin", "introduction": "intro_builtin"},
                "semantic": evidence(admission_semantics["ms_builtin"],
                                     "missing_builtin_meaning"),
                "soundness_dispatch": evidence(admission_dispatch["ms_builtinRules"],
                                              "missing_builtin_dispatch"),
                "completeness": evidence(constructors["intro_builtin"] + constructors["builtinRules"],
                                         "missing_encoded_witness"),
                "presentation_controls": presentation_controls(name),
                "related_specification_controls": related_controls(name)})
            continue
        rule = inventory.rules[name]
        fixed.append({"position": position, "id": rule.id, "kind": "named", "declaration": name,
            "source": str(RULES), "line": rule.line, "variables": list(rule.variables),
            "premises": [render(p) for p in rule.premises], "conclusion": render(rule.conclusion),
            "generated": {"instance": "inst_" + name, "transfer": "sound_" + name, "introduction": "intro_" + name},
            "semantic": lemmas["ms_" + name],
            "soundness_dispatch": evidence(transfers["sound_" + name], "missing_dispatch"),
            "completeness": evidence(constructors["intro_" + name], "missing_encoded_witness"),
            "presentation_controls": presentation_controls(name),
            "related_specification_controls": related_controls(name)})

    theory_defs = declarations(sources[THEORY])
    admitted = []
    for name, membership in (("symbolRule", "List.range allocated"),
                             ("axiomRule", "T.axioms"), ("definitionRule", "T.definitions")):
        require(name in theory_defs, f"missing admitted family: {name}")
        d = theory_defs[name]
        admitted.append({"declaration": name, "source": str(THEORY), "line": d.line,
            "admission_membership": membership, "header_sha256": sha256(norm(d.header)),
            "semantic": evidence(admission_semantics["ms_" + name], "missing_admission_meaning"),
            "soundness_dispatch": evidence(admission_dispatch["ms_" + name], "missing_admission_dispatch"),
            "introduction": evidence(admission_introductions["intro_" + name], "missing_admission_introduction"),
            "completeness": evidence(constructors["intro_" + name], "missing_encoded_witness"),
            "presentation_controls": presentation_controls(name),
            "related_specification_controls": related_controls(name)})
    manifest = {
        "schema_version": 2,
        "scope": "VibeITP static kernel: 123 fixed rules and three admitted families",
        "evidence_scope": "Exact named-rule semantic signatures are checked against schemas. Maintained controls are checked for source existence, namespace, stated checkRaw/validation/nonderivability outcome, judgment and proof/article route. Constructor and dispatch references remain source evidence; compile Lean and audit dependencies separately. Judgment controls do not claim every production branch is exercised. Uniform positional argument-count rejection is qualification coverage, not semantic positive coverage. Related specification controls do not qualify SemanticService articles or prove nonderivability.",
        "generation": {"write": "python3 scripts/generate_vibe_itp_rule_shapes.py --write",
                       "check": "python3 scripts/generate_vibe_itp_rule_shapes.py --check --self-test",
                       "shapes": str(SHAPES), "shapes_sha256": sha256(shapes)},
        "source_sha256": {str(path): sha256(source) for path, source in sorted(sources.items())},
        "counts": {"fixed": len(fixed), "named": len(inventory.rules), "builtin": len(inventory.builtins),
                   "admitted_families": len(admitted), "semantic_named_exact_matches": len(lemmas),
                   "semantic_helpers": len(helpers), "generated_theorems": 3 * len(inventory.rules) + 3,
                   "fixed_missing_dispatch": sum(r["soundness_dispatch"]["status"].startswith("missing") for r in fixed),
                   "fixed_missing_encoded_witness": sum(r["completeness"]["status"].startswith("missing") for r in fixed),
                   "fixed_missing_presentation_controls": sum(r["presentation_controls"]["status"] == "missing" for r in fixed),
                   "fixed_missing_qualification_rejection": sum(not r["presentation_controls"]["qualification_rejections"] for r in fixed),
                   "fixed_qualification_only_controls": sum(r["presentation_controls"]["status"] == "qualification_only" for r in fixed),
                   "fixed_without_focused_positive_article": sum(not r["presentation_controls"]["positive_article_examples"] for r in fixed),
                   "fixed_without_focused_negative_article_or_nonderivability": sum(not (r["presentation_controls"]["negative_article_examples"] or r["presentation_controls"]["nonderivability_examples"]) for r in fixed),
                   "admitted_missing_encoded_witness": sum(r["completeness"]["status"].startswith("missing") for r in admitted),
                   "admitted_missing_qualification_rejection": sum(not r["presentation_controls"]["qualification_rejections"] for r in admitted),
                   "focused_control_cases": len(control_cases), "qualification_control_theorems": len(qualification_cases)},
        "package_groups": inventory.groups,
        "fixed_rules": fixed,
        "admitted_families": admitted,
        "semantic_helpers": helpers,
        "focused_control_cases": control_cases,
        "qualification_control_theorems": qualification_cases,
        "static_correspondence_endpoints": required_theorem_references(sources,
            PRESENTATION / "CompleteCorrespondence.lean",
            ("complete_derives", "derives_iff_foDerivable", "derives_iff_checkRaw", "complete_article")),
        "package_validation": required_theorem_references(sources, VALIDATION,
            ("kernelRules_foPackage", "theoryRules_foPackage", "kernelDefinitionWith_theoryRules_valid",
             "kernelValidated_presents", "kernelFixedValidated_presents", "kernelValidated_lookup")),
        "operation_correspondence": [
            {"operation": "shift", "source": str(PRESENTATION / "CompleteShift.lean"),
             "success_and_refusal": required_theorem_references(sources, PRESENTATION / "CompleteShift.lean",
                ("shift_iff_foDerivable", "shift_shape_iff_foDerivable", "shiftList_iff_foDerivable",
                 "shift_refusal_iff", "shiftList_refusal_iff"))},
            {"operation": "substitution", "source": str(PRESENTATION / "CompleteSubstitution.lean"),
             "success_and_refusal": required_theorem_references(sources, PRESENTATION / "CompleteSubstitution.lean",
                ("substGo_shape_iff_foDerivable", "substList_shape_iff_foDerivable",
                 "substGoArgs_shape_iff_foDerivable", "substTop_shape_iff_foDerivable",
                 "substGo_shape_refusal_iff", "substList_shape_refusal_iff",
                 "substGoArgs_shape_refusal_iff", "substTop_shape_refusal_iff",
                 "substGo_iff_foDerivable", "substList_iff_foDerivable",
                 "substGoArgs_iff_foDerivable", "substTop_iff_foDerivable",
                 "substGo_refusal_iff", "substList_refusal_iff",
                 "substGoArgs_refusal_iff", "substTop_refusal_iff"))},
            {"operation": "instantiation", "source": str(PRESENTATION / "CompleteInstantiation.lean"),
             "success_and_refusal": required_theorem_references(sources, PRESENTATION / "CompleteInstantiation.lean",
                ("instGo_iff_foDerivable", "instList_iff_foDerivable", "instArgs_iff_foDerivable",
                 "instGo_refusal_iff", "instList_refusal_iff", "instArgs_refusal_iff"))}],
        "operation_profile_preservation": required_theorem_references(sources, PRESENTATION / "OperationsWf.lean",
            ("shift_wellFormed", "shiftList_wellFormed", "subst_wellFormed", "substList_wellFormed",
             "substBVars_wellFormed", "inst_wellFormed", "instList_wellFormed",
             "shift_termShape", "shiftList_termShape", "subst_termShape", "substList_termShape",
             "substBVars_termShape", "inst_termShape", "instList_termShape")),
        "derived_profile": required_theorem_references(sources, PRESENTATION / "DerivedTermShape.lean",
            ("instantiateStatement_termShape", "derives_termShape")),
    }
    return json.dumps(manifest, indent=2, ensure_ascii=False) + "\n"


def load_sources(root: Path) -> dict[Path, str]:
    required = {GENERATOR, RULES, SYNTAX, BASIC, THEORY, SPEC / "Controls.lean", *SOUND_SOURCES}
    optional = {path.relative_to(root) for path in (root / PRESENTATION).glob("*.lean")
                if path.relative_to(root) != SHAPES}
    optional |= {path.relative_to(root) for path in (root / SPEC).glob("*.lean")}
    return {path: (root / path).read_text(encoding="utf-8") for path in sorted(required | optional)}


def self_test(sources: dict[Path, str]) -> None:
    """Mutation controls exercise omissions a permissive generator could hide."""
    def inventory(rules: str, basic: str | None = None) -> Inventory:
        return parse_inventory(rules, sources[SYNTAX], basic or sources[BASIC])

    def refuses(label: str, action) -> None:
        try:
            action()
        except SourceError:
            return
        raise SourceError("negative generator control accepted: " + label)

    original = sources[RULES]
    baseline = inventory(original)
    variation = original.replace('mkRule "vibe-psucc-1" [] []',
                                 'mkRule /- harmless /- nested -/ comment -/ "vibe-psucc-1"\n    [ ] [ ]', 1)
    varied = inventory(variation)
    require(generate_shapes(baseline) == generate_shapes(varied), "valid whitespace/comment variation changed shapes")
    require(generate_shapes(baseline) == generate_shapes(inventory(original)), "generation is nondeterministic")
    refuses("omitted kernel rule", lambda: inventory(original.replace('[rMp, rInst,', '[rInst,', 1)))
    refuses("repeated kernel rule", lambda: inventory(original.replace('[rMp, rInst,', '[rMp, rMp, rInst,', 1)))
    refuses("duplicate rule ID", lambda: inventory(original.replace('"vibe-psucc-o"', '"vibe-psucc-1"', 1)))
    refuses("undeclared metavariable", lambda: inventory(original.replace('(mv "p")', '(mv "unlisted")', 1)))
    refuses("wrong constructor arity", lambda: inventory(original.replace('(cPO cP1)', '(cPO cP1 cP1)', 1)))
    refuses("unsupported trailing syntax", lambda: inventory(original.replace('(jPSucc cP1 (cPO cP1))',
        '(jPSucc cP1 (cPO cP1)) where hidden := 1', 1)))
    refuses("missing builtin", lambda: inventory(original, sources[BASIC].replace('.isSafeCode, .executedTo]', '.isSafeCode]', 1)))
    broken = dict(sources)
    broken[SOUND_SOURCES[0]] = broken[SOUND_SOURCES[0]].replace('Meaning T (jPSucc cP1 (cPO cP1))',
        'Meaning T (jPSucc cP1 (cPI cP1))', 1)
    refuses("named semantic conclusion differs", lambda: semantic_matches(baseline, broken))
    apostrophes = declarations("namespace Example\n"
        "theorem profile : 0 = 0 := rfl\n"
        "theorem profile' : 1 = 1 := rfl\nend Example\n", "theorem")
    require(set(apostrophes) == {"profile", "profile'"}, "apostrophe declaration name was truncated")
    control_original = sources[KERNEL_CONTROLS]
    control_variation = dict(sources)
    control_variation[KERNEL_CONTROLS] = control_original.replace("theorem shift_under_binder_accepts :",
        "theorem /- valid /- nested -/ comment -/ shift_under_binder_accepts :", 1)
    require(len(checked_control_cases(baseline, control_variation)[0]) ==
            len(checked_control_cases(baseline, sources)[0]), "valid control comment variation changed coverage")

    def control_mutation(label: str, old: str, new: str) -> None:
        require(old in control_original, f"mutation control no longer applies: {label}")
        mutated = dict(sources)
        mutated[KERNEL_CONTROLS] = control_original.replace(old, new, 1)
        refuses(label, lambda: checked_control_cases(baseline, mutated))

    control_mutation("missing mapped control", "theorem shift_under_binder_accepts",
                     "theorem renamed_shift_control")
    control_mutation("unclassified public control", "end " + CONTROL_NAMESPACE,
                     "theorem unclassified_control : 0 = 0 := rfl\nend " + CONTROL_NAMESPACE)
    control_mutation("mapped checker outcome differs", "mpArticle = true", "mpArticle = false")
    control_mutation("missing constructive control route", "exact complete_shift fixed_in",
                     "exact unknown_shift_witness fixed_in")
    shift_header = declarations(control_original, "theorem")["shift_under_binder_accepts"].header
    control_mutation("mapped judgment differs", shift_header, shift_header.replace("jShift", "jSubst"))
    control_mutation("missing uniform qualification control", "theorem fixed_rule_argument_count_controls",
                     "theorem renamed_fixed_qualification")
    endpoint = PRESENTATION / "CompleteCorrespondence.lean"
    mutated = dict(sources)
    mutated[endpoint] = sources[endpoint].replace("theorem derives_iff_checkRaw",
                                                "theorem renamed_checker_endpoint", 1)
    refuses("missing composed checker endpoint", lambda: required_theorem_references(mutated, endpoint,
                                                                                   ("derives_iff_checkRaw",)))
    shapes = generate_shapes(baseline)
    require(generate_manifest(baseline, sources, shapes) == generate_manifest(baseline, sources, shapes),
            "coverage generation is nondeterministic")
    print("Generator controls: 4 positive and 15 negative passed; deterministic shapes and manifest checked.",
          file=sys.stderr)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true", help="write the generated shapes and coverage manifest")
    mode.add_argument("--check", action="store_true", help="reject stale generated files without changing them")
    mode.add_argument("--stdout", action="store_true", help="print generated Lean; do not write files")
    parser.add_argument("--self-test", action="store_true", help="run source mutation controls")
    parser.add_argument("--root", type=Path, default=ROOT, help="Lean project root (defaults to this script's parent)")
    args = parser.parse_args()
    try:
        sources = load_sources(args.root)
        inventory = parse_inventory(sources[RULES], sources[SYNTAX], sources[BASIC])
        if args.self_test:
            self_test(sources)
        shapes = generate_shapes(inventory)
        manifest = generate_manifest(inventory, sources, shapes)
        outputs = {SHAPES: shapes, MANIFEST: manifest}
        if args.stdout:
            sys.stdout.write(shapes)
        elif args.write:
            for path, content in outputs.items():
                (args.root / path).write_text(content, encoding="utf-8")
        else:
            stale = [str(path) for path, content in outputs.items()
                     if not (args.root / path).is_file() or (args.root / path).read_text(encoding="utf-8") != content]
            require(not stale, "generated files are stale: " + ", ".join(stale))
        if not args.stdout:
            print(f"Rule coverage: {len(inventory.rules)} named + {len(inventory.builtins)} built-in = "
                  f"{len(inventory.order)} fixed; three admitted families; exact named semantic signatures checked.")
        return 0
    except (SourceError, OSError, json.JSONDecodeError) as error:
        print("VibeITP generation rejected: " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
