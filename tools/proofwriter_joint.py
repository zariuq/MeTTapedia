"""Audit ProofWriter OWA closure and analyze a joint uncertainty control.

The evaluator uses the release's structured representations, with hard
negation for negative conditions. Labels and proof annotations are read by
the audit, never as premises. The probabilistic extension models which
supplied facts are licensed in a world, then runs the same Horn closure.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from collections.abc import Iterable
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
import json
from math import prod
from pathlib import Path
import re
from zipfile import ZipFile


LITERAL_SYNTAX = r'\("[^"]+" "[^"]+" "[^"]+" "[+~-]"\)'
LITERAL = re.compile(LITERAL_SYNTAX)
RULE = re.compile(
    rf"\(\((?P<body>{LITERAL_SYNTAX}(?: {LITERAL_SYNTAX})*)\) -> (?P<head>{LITERAL_SYNTAX})\)"
)
MAIN_SPLIT = re.compile(r"/OWA/[^/]+/meta-(?:dev|test)\.jsonl$")
VARIABLES = {"someone", "something"}

Literal = tuple[str, str, str, bool]
Support = frozenset[str]
World = tuple[bool, ...]


@dataclass(frozen=True)
class Clause:
    source: str
    body: tuple[Literal, ...]
    head: Literal


@dataclass(frozen=True)
class Report:
    event: str
    fact: int
    positive: bool
    common_source: bool = True


def literal(text: str) -> Literal:
    if not LITERAL.fullmatch(text):
        raise ValueError(f"Unexpected ProofWriter literal: {text}")
    subject, relation, target, sign = text[2:-2].split('" "')
    return subject, relation, target, sign == "+"


def theory(record: dict) -> tuple[dict[str, Literal], tuple[Clause, ...]]:
    facts = {key: literal(value["representation"]) for key, value in record["triples"].items()}
    rules = []
    for key, value in record["rules"].items():
        text = value["representation"]
        match = RULE.fullmatch(text)
        if match is None:
            raise ValueError(f"{record['id']} {key}: unexpected rule {text}")
        body = tuple(literal(text) for text in LITERAL.findall(match["body"]))
        rules.append(Clause(key, body, literal(match["head"])))

    # In the release, "is" is an attribute predicate. Its target is an
    # adjective, while the target of a relational predicate is an entity.
    literals = list(facts.values()) + [
        atom for rule in rules for atom in (*rule.body, rule.head)
    ]
    domain = sorted({
        name
        for subject, relation, target, _ in literals
        for name in ((subject,) if relation == "is" else (subject, target))
        if name not in VARIABLES
    })
    ground_rules = []
    for rule in rules:
        variables = sorted(VARIABLES.intersection(
            name for atom in (*rule.body, rule.head) for name in (atom[0], atom[2])
        ))
        for arguments in product(domain, repeat=len(variables)):
            binding = dict(zip(variables, arguments))

            def ground(atom: Literal) -> Literal:
                subject, relation, target, positive = atom
                return binding.get(subject, subject), relation, binding.get(target, target), positive

            ground_rules.append(Clause(rule.source, tuple(map(ground, rule.body)), ground(rule.head)))
    return facts, tuple(ground_rules)


def opposite(atom: Literal) -> Literal:
    subject, relation, target, positive = atom
    return subject, relation, target, not positive


def closure(facts: Iterable[Literal], rules: tuple[Clause, ...]) -> set[Literal]:
    known = set(facts)
    while True:
        heads = {rule.head for rule in rules if all(atom in known for atom in rule.body)}
        if heads <= known:
            return known
        known.update(heads)


def status(known: set[Literal], atom: Literal) -> str:
    supported, refuted = atom in known, opposite(atom) in known
    if supported and refuted:
        return "Both"
    if supported:
        return "True"
    return "False" if refuted else "Unknown"


def supports(facts: dict[str, Literal], rules: tuple[Clause, ...]) -> dict[Literal, set[Support]]:
    """Compute minimal fact-ID supports by absorption at the Horn fixed point."""
    lineage = defaultdict(set)
    for fact, atom in facts.items():
        lineage[atom].add(frozenset({fact}))
    while True:
        changed = False
        for rule in rules:
            for inputs in product(*(lineage[atom] for atom in rule.body)):
                support = frozenset().union(*inputs)
                previous = lineage[rule.head]
                if any(old <= support for old in previous):
                    continue
                previous.difference_update({old for old in previous if support < old})
                previous.add(support)
                changed = True
        if not changed:
            return lineage


def audit(archive: ZipFile) -> dict:
    results = {}
    for member in archive.namelist():
        if not MAIN_SPLIT.search(member):
            continue
        counts = Counter()
        examples = []
        with archive.open(member) as records:
            for line in records:
                record = json.loads(line)
                facts, rules = theory(record)
                known = closure(facts.values(), rules)
                counts["theories"] += 1
                for name, question in record["questions"].items():
                    expected = str(question["answer"])
                    actual = status(known, literal(question["representation"]))
                    counts[expected] += 1
                    if actual != expected:
                        counts["mismatches"] += 1
                        if len(examples) < 4:
                            examples.append([record["id"], name, expected, actual])
        results[member.split("/OWA/")[1]] = {**counts, "examples": examples}
    return results


def overlap_case(archive: ZipFile) -> tuple[dict, str, tuple[Support, Support]]:
    member = next(name for name in archive.namelist() if name.endswith("/OWA/depth-5/meta-dev.jsonl"))
    with archive.open(member) as records:
        for line in records:
            record = json.loads(line)
            facts, rules = theory(record)
            lineage = supports(facts, rules)
            for name, question in record["questions"].items():
                if question["answer"] is not True or question["QDep"] < 2:
                    continue
                derived = lineage[literal(question["representation"])]
                if len(derived) != 2:
                    continue
                first, second = sorted(derived, key=lambda support: sorted(support))
                if len(first) == len(second) == 2 and len(first & second) == 1:
                    return record, name, (first, second)
    raise ValueError("No overlapping two-route case in the depth-5 development split")


def condition(
    worlds: list[World], reports: list[Report], shared: bool
) -> tuple[Fraction, dict[World, Fraction]]:
    """Uniform fact prior and symmetric report errors with optional shared reliability."""
    unique = {}
    for report in reports:
        if unique.setdefault(report.event, report) != report:
            raise ValueError(f"Conflicting payload for observation {report.event}")
    accuracy = Fraction(3, 4)
    rates = (Fraction(1, 2), Fraction(1)) if shared else (accuracy,)
    weights = {}
    for world in worlds:
        weight = Fraction()
        for rate in rates:
            likelihood = Fraction(1)
            for report in unique.values():
                reliability = rate if report.common_source else accuracy
                likelihood *= (
                    reliability if world[report.fact] == report.positive else 1 - reliability
                )
            weight += likelihood
        weights[world] = weight / (len(rates) * len(worlds))
    normalizer = sum(weights.values())
    return normalizer, {world: weight / normalizer for world, weight in weights.items()}


def bayesian_analysis(record: dict, name: str, routes: tuple[Support, Support]) -> dict:
    shared, = routes[0] & routes[1]
    a, = routes[0] - {shared}
    b, = routes[1] - {shared}
    uncertain = (shared, a, b)
    facts, rules = theory(record)
    atom = literal(record["questions"][name]["representation"])
    hard_facts = [fact for key, fact in facts.items() if key not in uncertain]
    cases = {}
    for world in product((False, True), repeat=len(uncertain)):
        active = [facts[key] for key, on in zip(uncertain, world) if on]
        cases[world] = status(closure(hard_facts + active, rules), atom)
        s, left, right = world
        expected = "True" if s and (left or right) else "Unknown"
        if cases[world] != expected:
            raise ValueError(f"Provenance disagrees with exact closure in world {world}")

    reports = [Report(f"original-{key}", i, True) for i, key in enumerate(uncertain)]
    sequences = {
        "prior": [],
        "initial_reports": reports,
        "replayed_report": reports + reports[:1],
        "independent_confirmation": reports + [Report("independent-positive", 0, True, False)],
        "independent_disagreement": reports + [Report("independent-negative", 0, False, False)],
    }
    models = {}
    investigations = {}
    for model, shared_source in (("independent_reports", False), ("shared_reliability", True)):
        readouts = {}
        for label, observations in sequences.items():
            normalizer, posterior = condition(list(cases), observations, shared_source)
            status_mass = Counter()
            for world, weight in posterior.items():
                status_mass[cases[world]] += weight
            route_mass = [sum(weight for w, weight in posterior.items() if w[0] and w[i])
                          for i in (1, 2)]
            readouts[label] = {
                "evidence_mass": normalizer,
                "supported_joint_mass": status_mass["True"] * normalizer,
                "query_status_posterior": {s: status_mass[s] for s in ("True", "False", "Unknown")},
                "premise_marginals": [sum(p for w, p in posterior.items() if w[i])
                                      for i in range(len(uncertain))],
                "route_marginals": route_mass,
                "both_routes": posterior[(True, True, True)],
                "independent_route_estimate": 1 - prod(1 - p for p in route_mass),
            }
        if readouts["initial_reports"] != readouts["replayed_report"]:
            raise ValueError("Replaying an observation changed the model")
        models[model] = readouts

        evidence_mass, posterior = condition(list(cases), reports, shared_source)
        proved = {world for world, result in cases.items() if result == "True"}
        query_mass = sum(posterior[world] for world in proved)
        abduction = [sum(posterior[w] for w in proved if w[i]) / query_mass
                     for i in range(len(uncertain))]
        next_report = {}
        for i, fact in enumerate(uncertain):
            forecasts = {}
            gain = Fraction()
            for sign in (True, False):
                with_report = reports + [Report(f"new-{fact}", i, sign, False)]
                updated_mass, updated = condition(list(cases), with_report, shared_source)
                prediction = sum(updated[w] for w in proved)
                prevalence = updated_mass / evidence_mass
                forecasts["positive" if sign else "negative"] = {
                    "probability": prevalence,
                    "query_support_posterior": prediction,
                }
                gain += prevalence * (prediction - query_mass) ** 2
            next_report[fact] = {
                "prediction_by_outcome": forecasts,
                "expected_brier_loss_reduction": gain,
            }
        investigations[model] = {
            "premise_marginals_given_proof_exists": abduction,
            "single_independent_follow_up_reports": next_report,
        }

    # The Fréchet lower bound for shared ∧ left is 1/2, and shared
    # itself upper-bounds the query by 3/4. These couplings attain both.
    endpoints = {
        "lower": {(True, True, True): Fraction(1, 2),
                  (True, False, False): Fraction(1, 4), (False, True, True): Fraction(1, 4)},
        "upper": {(True, True, True): Fraction(3, 4), (False, False, False): Fraction(1, 4)},
    }
    bounds = {}
    for key, weights in endpoints.items():
        assert sum(weights.values()) == 1
        assert all(sum(p for w, p in weights.items() if w[i]) == Fraction(3, 4)
                   for i in range(len(uncertain)))
        bounds[key] = sum(p for w, p in weights.items() if cases[w] == "True")
    return {
        "uncertain_fact_ids": uncertain,
        "models": models,
        "marginal_only_bounds": bounds,
        "premise_worlds": [{"bits": w, "status": result} for w, result in cases.items()],
        "investigations": investigations,
    }


def reused_premise_control(archive: ZipFile) -> tuple[dict, str, str]:
    member = next(name for name in archive.namelist() if name.endswith("/OWA/depth-5/meta-dev.jsonl"))
    with archive.open(member) as records:
        for line in records:
            record = json.loads(line)
            if record["id"] != "AttNoneg-OWA-D5-1364":
                continue
            name, reused = "Q5", "triple9"
            facts, rules = theory(record)
            atom = literal(record["questions"][name]["representation"])
            if supports(facts, rules)[atom] != {frozenset({reused})}:
                raise ValueError("Unexpected fact supports for reused-premise control")
            return record, name, reused
    raise ValueError("Missing AttNoneg-OWA-D5-1364 control")


def reuse_slices(record: dict, name: str, fact: str) -> tuple[dict, dict]:
    """Isolate the source proof and its deductively composed rule."""
    premise = record["triples"][fact]
    query = record["questions"][name]["representation"]
    original = {
        **record,
        "triples": {fact: premise},
        "rules": {key: record["rules"][key] for key in ("rule5", "rule7")},
    }
    composed = {
        **original,
        "rules": {"derived": {"representation": f"(({premise['representation']}) -> {query})"}},
    }
    for fixture in (original, composed):
        facts, rules = theory(fixture)
        atom = literal(query)
        if status(closure(facts.values(), rules), atom) != "True":
            raise ValueError("The reused-premise slice must derive the query")
        if status(closure([], rules), atom) != "Unknown":
            raise ValueError("Removing the reused premise must block the derivation")
    return original, composed


def metta_cases(record: dict, name: str, uncertain: tuple[str, ...], output: Path,
                patrick: Path, roman: Path) -> None:
    facts, rules = theory(record)
    question_data = record["questions"]
    question_names = [
        name,
        next(key for key, question in question_data.items() if question["answer"] is False),
        next(key for key, question in question_data.items() if question["answer"] == "Unknown"),
    ]
    queries = [(key, literal(question_data[key]["representation"])) for key in question_names]

    def term(atom: Literal) -> str:
        subject, relation, target, positive = atom
        # Use ordinary ground terms. Negation is represented by the sign field
        # so that neither chainer interprets it as negation by failure.
        tokens = (subject, relation, target)
        if any(not re.fullmatch(r"[a-zA-Z0-9_-]+", token) for token in tokens):
            raise ValueError(f"MeTTa exporter needs quoting for {tokens}")
        return f"(PW {'positive' if positive else 'negative'} {' '.join(tokens)})"

    rule_names = [f"{rule.source}_{i}" for i, rule in enumerate(rules, 1)]
    stamps = dict(enumerate([*facts, *rule_names], 1))
    output.mkdir(parents=True, exist_ok=True)
    for variant in ("hard", "soft", "without_shared"):
        # Feed the baseline engines the same premise strengths in the soft
        # control. Their reported STVs retain their own rule semantics.
        hammer = [f"!(import! &self {patrick.resolve().with_suffix('')})", "(= (pw-kb) ("]
        treutlein = [f"!(import! &self {roman.resolve().with_suffix('')})"]
        for index, (key, atom) in enumerate(facts.items(), 1):
            if variant == "without_shared" and key == uncertain[0]:
                continue
            strength = "0.75" if variant == "soft" and key in uncertain else "1.0"
            hammer.append(f"  (Sentence ({term(atom)} (stv {strength} 0.9)) ({index}))")
            treutlein.append(f"!(compileadd pw (: {key} {term(atom)} (STV {strength} 0.9)))")
        for index, (key, rule) in enumerate(zip(rule_names, rules), len(facts) + 1):
            implication = term(rule.head)
            for atom in reversed(rule.body):
                implication = f"(Implication {term(atom)} {implication})"
            hammer.append(f"  (Sentence ({implication} (stv 1.0 0.9)) ({index}))")
            premises = [term(atom) for atom in rule.body]
            antecedent = premises[0] if len(premises) == 1 else f"(And {' '.join(premises)})"
            treutlein.append(
                f"!(compileadd pw (: (no_inverse {key}) (Implication {antecedent} {term(rule.head)}) "
                "(CTV (STV 1.0 0.9) (STV 0.0 1.0))))"
            )
        hammer.append("))")
        hammer.extend([
            "(= (pw-report $beliefs $id $goal)",
            "   (println! (PWResult $id (collapse (let (Sentence ($goal $tv) $stamps)",
            "                                      (superpose $beliefs) ($tv $stamps))))))",
        ])
        marker_calls = []
        for key, atom in queries:
            for sign, goal in (("query", atom), ("opposite", opposite(atom))):
                marker = f"{key}-{sign}"
                marker_calls.append(f"(pw-report $beliefs {marker} {term(goal)})")
                treutlein.append(
                    f"!(println! (PWResult {marker} "
                    f"(collapse (query 200 pw (: $proof {term(goal)} $tv)))))"
                )
        hammer.append(
            "!(let ($tasks $beliefs) (PLN.Derive (pw-kb) (pw-kb) 180 512 512) "
            f"(progn {' '.join(marker_calls)} (println! (PWPending (length $tasks)))))"
        )
        for label, lines in (("hammer", hammer), ("treutlein", treutlein)):
            (output / f"{label}-{variant}.metta").write_text("\n".join(lines) + "\n")
    (output / "ground-stamps.json").write_text(json.dumps(stamps, indent=2) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path, help="ProofWriter OWA ZIP")
    parser.add_argument("--audit", action="store_true", help="Check all main dev/test members")
    parser.add_argument("--export", type=Path, help="Directory for optional MeTTa chainer inputs")
    parser.add_argument("--hammer-library", type=Path, help="Path to Hammer's lib_pln.metta")
    parser.add_argument("--treutlein-library", type=Path, help="Path to Treutlein's petta_chainer.metta")
    args = parser.parse_args()
    if args.export and not (args.hammer_library and args.treutlein_library):
        parser.error("--export requires both chainer library paths")
    with ZipFile(args.archive) as archive:
        if args.audit:
            results = audit(archive)
            print(json.dumps(results, indent=2))
            if not results or any(row.get("mismatches") for row in results.values()):
                raise SystemExit(1)
        else:
            record, name, routes = overlap_case(archive)
            analysis = bayesian_analysis(record, name, routes)
            reuse, reuse_query, fact = reused_premise_control(archive)
            source_slice, composed_slice = reuse_slices(reuse, reuse_query, fact)
            if args.export:
                metta_cases(record, name, analysis["uncertain_fact_ids"], args.export,
                            args.hammer_library, args.treutlein_library)
                metta_cases(reuse, reuse_query, (fact,), args.export / "reused-premise",
                            args.hammer_library, args.treutlein_library)
                metta_cases(source_slice, reuse_query, (fact,), args.export / "original-proof-slice",
                            args.hammer_library, args.treutlein_library)
                metta_cases(composed_slice, reuse_query, (fact,), args.export / "composed-rule",
                            args.hammer_library, args.treutlein_library)
            print(json.dumps({
                "id": record["id"], "question": name,
                "query": record["questions"][name],
                "routes": [sorted(route) for route in routes],
                "facts": record["triples"], "rules": record["rules"],
                **analysis,
                "reused_premise_control": {
                    "id": reuse["id"],
                    "question": reuse_query,
                    "query": reuse["questions"][reuse_query],
                    "minimal_fact_support": [fact],
                    "source_proof_slice": source_slice["rules"],
                    "composed_rule": composed_slice["rules"]["derived"]["representation"],
                },
            }, indent=2, default=str))


if __name__ == "__main__":
    main()
