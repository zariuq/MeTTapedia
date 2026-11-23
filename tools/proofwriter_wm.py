"""Replay controlled report evidence over ProofWriter's structured OWA theories.

Build Mettapedia.Examples.PLN.ProofWriterWorldModel before running this tool.
The observations are simulated. The archive supplies the Horn programs and
an independently annotated all-facts-enabled control.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
import json
from math import prod
from pathlib import Path
import random
import re
import subprocess
from zipfile import ZipFile

from proofwriter_joint import (
    closure, literal, opposite, overlap_case, reuse_slices, reused_premise_control, status, theory,
)


RATES = (Fraction(1, 2), Fraction(1))
OUTCOMES = ("True", "False", "Unknown", "Both")


@dataclass(frozen=True)
class Component:
    mass: Fraction
    probabilities: tuple[Fraction, ...]


@dataclass(frozen=True)
class Report:
    event: str
    source: int
    signal: bool
    accuracy: tuple[Fraction, ...]


def score(components: tuple[Component, ...], report: Report) -> tuple[Component, ...]:
    updated = []
    for component, accuracy in zip(components, report.accuracy, strict=True):
        probabilities = component.probabilities
        present = probabilities[report.source]
        match_weight = accuracy if report.signal else 1 - accuracy
        joint = present * match_weight
        evidence = joint + (1 - present) * (1 - match_weight)
        if evidence:
            probabilities = (*probabilities[:report.source], joint / evidence,
                             *probabilities[report.source + 1:])
        updated.append(Component(component.mass * evidence, probabilities))
    return tuple(updated)


@dataclass(frozen=True)
class Ledger:
    prior: tuple[Component, ...]
    reports: tuple[Report, ...] = ()

    def observe(self, report: Report) -> Ledger:
        for recorded in self.reports:
            if recorded.event == report.event:
                if recorded != report:
                    raise ValueError(f"Conflicting payload for {report.event}")
                return self
        return Ledger(self.prior, (*self.reports, report))

    def retract(self, event: str) -> Ledger:
        return Ledger(self.prior, tuple(report for report in self.reports if report.event != event))

    def posterior(self) -> tuple[Fraction, tuple[Component, ...]] | None:
        components = self.prior
        for report in self.reports:
            components = score(components, report)
        normalizer = sum((component.mass for component in components), Fraction())
        if normalizer == 0:
            return None
        return normalizer, tuple(Component(c.mass / normalizer, c.probabilities) for c in components)


def atom_indices(facts, rules, queries) -> dict:
    atoms = set(facts.values()) | set(queries) | {opposite(query) for query in queries}
    for rule in rules:
        atoms.update((*rule.body, rule.head))
    return {atom: i for i, atom in enumerate(sorted(atoms))}


def packet(facts, rules, queries) -> dict:
    index = atom_indices(facts, rules, queries)
    return {
        "atomCount": len(index),
        "sources": [index[atom] for atom in facts.values()],
        "clauses": [[index[rule.head], [index[atom] for atom in rule.body]] for rule in rules],
        "queries": [[index[query], index[opposite(query)]] for query in queries],
    }


def evaluate(process, program, worlds, laws) -> dict:
    payload = {
        **program,
        "worlds": worlds,
        "productLaws": [[[p.numerator, p.denominator] for p in law] for law in laws],
    }
    return exchange(process, payload)


def exchange(process, payload) -> dict:
    process.stdin.write(json.dumps(payload) + "\n")
    process.stdin.flush()
    line = process.stdout.readline()
    if not line:
        raise RuntimeError("Lean evaluator exited before returning a complete answer")
    try:
        return json.loads(line)
    except json.JSONDecodeError as error:
        raise RuntimeError(f"Lean evaluator returned {line.strip()}") from error


def distribution(counts) -> tuple[Fraction, ...]:
    positive, negative, both = map(Fraction, counts)
    return positive - both, negative - both, 1 - positive - negative + both, both


def mixtures(rows, weights):
    return tuple(
        sum((weight * value for weight, value in zip(weights, column, strict=True)), Fraction())
        for column in zip(*(distribution(row) for row in rows), strict=True)
    )


def simulated_reports(facts, rng):
    choices = tuple(bool(rng.getrandbits(1)) for _ in facts)
    rate = RATES[rng.randrange(len(RATES))]
    prior = tuple(Component(Fraction(1, len(RATES)), (Fraction(1, 2),) * len(facts)) for _ in RATES)
    ledger = Ledger(prior)
    for source, (name, present) in enumerate(zip(facts, choices, strict=True)):
        signal = present if rng.randrange(rate.denominator) < rate.numerator else not present
        ledger = ledger.observe(Report(name, source, signal, RATES))
    return choices, ledger


def follow_report_controls(archive: ZipFile, process) -> dict:
    record, key, routes = overlap_case(archive)
    facts, rules = theory(record)
    query = literal(record["questions"][key]["representation"])
    program = packet(facts, rules, [query])
    soft = routes[0] | routes[1]
    common, = routes[0] & routes[1]
    ids = {name: i for i, name in enumerate(facts)}
    independent_rate = (Fraction(3, 4),)
    prior = (Component(Fraction(1), tuple(Fraction(1, 2) if f in soft else Fraction(1) for f in facts)),)
    reports = tuple(Report(name, ids[name], True, independent_rate) for name in sorted(soft))
    initial = Ledger(prior)
    for report in reports:
        initial = initial.observe(report)
    confirmed = initial.observe(Report("fresh", ids[common], True, independent_rate))
    disputed = initial.observe(Report("fresh", ids[common], False, independent_rate))
    stages = {
        "initial": initial, "replayed": initial.observe(reports[0]),
        "confirmed": confirmed, "disputed": disputed, "retracted": confirmed.retract("fresh"),
    }
    posteriors = [ledger.posterior() for ledger in stages.values()]
    result = evaluate(process, program, [], [laws[0].probabilities for _, laws in posteriors])
    readouts = {
        name: {"normalizer": evidence, "supported": distribution(row[0])[0]}
        for name, (evidence, _), row in zip(stages, posteriors, result["masses"], strict=True)
    }
    expected = {"initial": Fraction(45, 64), "replayed": Fraction(45, 64), "confirmed": Fraction(27, 32),
                "disputed": Fraction(15, 32), "retracted": Fraction(45, 64)}
    assert {key: row["supported"] for key, row in readouts.items()} == expected
    try:
        initial.observe(Report(reports[0].event, reports[0].source, False, independent_rate))
    except ValueError:
        pass
    else:
        raise AssertionError("An event accepted two different payloads")
    impossible = Ledger((Component(Fraction(1), (Fraction(0),)),))
    assert impossible.observe(Report("certain", 0, True, (Fraction(1),))).posterior() is None

    opposed = {key: atom for key, atom in (("pos", query), ("neg", opposite(query)))}
    result = evaluate(process, packet(opposed, [], [query]), [], [(Fraction(1, 2),) * 2])
    assert distribution(result["masses"][0][0]) == (Fraction(1, 4),) * 4
    return {"case": record["id"], "revisions": readouts, "inconsistent_support_distribution": ["1/4"] * 4}


def replay(records, process, seed: int) -> tuple[dict, list]:
    rng = random.Random(seed)
    counts = Counter()
    losses = Counter()
    native_sample = []
    for record in records:
        facts, rules = theory(record)
        questions = list(record["questions"].values())
        queries = [literal(question["representation"]) for question in questions]
        program = packet(facts, rules, queries)
        n = len(facts)
        choices, ledger = simulated_reports(facts, rng)
        _, posterior = ledger.posterior()
        weights = [c.mass for c in posterior]
        modes = [c.probabilities for c in posterior]
        marginals = tuple(sum((c.mass * c.probabilities[i] for c in posterior), Fraction()) for i in range(n))
        laws = [*modes, marginals]

        exhaustive = counts["enumerated_theories"] < 8 and n <= 8
        all_worlds = list(product((False, True), repeat=n)) if exhaustive else []
        result = evaluate(process, program, [(True,) * n, choices, *all_worlds], laws)
        labels, draws, *enum_labels = result["labels"]
        expected = [str(question["answer"]) for question in questions]
        if labels != expected:
            raise ValueError(f"Gold discrepancy in {record['id']}")
        true_world = closure((a for a, on in zip(facts.values(), choices, strict=True) if on), rules)
        assert draws == [status(true_world, query) for query in queries]

        if exhaustive:
            enum_mass = [[[Fraction() for _ in OUTCOMES] for _ in queries] for _ in laws]
            for world, compiled_labels in zip(all_worlds, enum_labels, strict=True):
                direct = closure((a for a, on in zip(facts.values(), world, strict=True) if on), rules)
                assert compiled_labels == [status(direct, q) for q in queries]
                for law, by_query in zip(laws, enum_mass, strict=True):
                    weight = prod(p if on else 1 - p for on, p in zip(world, law, strict=True))
                    for assigned, out in zip(compiled_labels, by_query, strict=True):
                        out[OUTCOMES.index(assigned)] += weight
            for explicit, compiled in zip(enum_mass, result["masses"], strict=True):
                assert [tuple(row) for row in explicit] == list(map(distribution, compiled))
            counts["enumerated_theories"] += 1
            counts["enumerated_worlds"] += len(all_worlds)

        for drawn, *all_counts in zip(draws, *result["masses"], strict=True):
            exact = mixtures(all_counts[:-1], weights)
            baseline = distribution(all_counts[-1])
            assert sum(exact) == sum(baseline) == 1 and min(*exact, *baseline) >= 0
            counts["queries"] += 1
            counts["different_posteriors"] += int(exact != baseline)
            # The joint law supplies the conditional distribution of the
            # four-valued outcome. Squared distance is excess Brier risk.
            losses["joint_expected"] += 1 - sum(p * p for p in exact)
            losses["excess_expected"] += sum((p - q) ** 2 for p, q in zip(exact, baseline, strict=True))
            index = OUTCOMES.index(drawn)
            losses["joint_observed"] += sum((p - (i == index)) ** 2 for i, p in enumerate(exact))
            losses["collapsed_observed"] += sum((p - (i == index)) ** 2 for i, p in enumerate(baseline))
        counts["theories"] += 1
        counts.update(labels)
        if counts["theories"] % 29 == 1 and len(native_sample) < 32:
            native_sample.append((record["id"], facts, rules, queries))

    if counts["queries"] == 0:
        raise ValueError("No ProofWriter questions evaluated")
    return {
        **counts, "seed": seed,
        "mean_brier": {name: value / counts["queries"] for name, value in losses.items()},
    }, native_sample


def datalog(program: dict, sources: set[int], demand: bool) -> str:
    code = [
        *[f".decl {p}(x:number)\n.output {p}" for p in ("Need", "Have", "Used")],
        ".decl Head(r:number,h:number)",
        ".decl Input(x:number)",
        "Have(H) :- Head(R,H), Used(R).",
        "Have(H) :- Input(H), Need(H)." if demand else "Have(H) :- Input(H).",
    ]
    code.extend(f"Input({a})." for a in sorted(sources))
    if demand:
        code.extend((".decl Member(r:number,p:number)", "Need(P) :- Need(H), Head(R,H), Member(R,P)."))
        targets = sorted({atom for pair in program["queries"] for atom in pair})
        code.extend(f"Need({a})." for a in targets)
    installed = set()
    for i, (head, raw_body) in enumerate(program["clauses"]):
        body = list(dict.fromkeys(raw_body))
        width = len(body)
        if width not in installed:
            installed.add(width)
            fields = ["r:number", "h:number", *(f"p{j}:number" for j in range(width))]
            relation = f"Rule{width}"
            variables = [f"P{j}" for j in range(width)]
            code.append(f".decl {relation}({','.join(fields)})")
            premises = [f"{relation}({','.join(['R', 'H', *variables])})"]
            if demand:
                premises.append("Need(H)")
            premises.extend(f"Have({var})" for var in variables)
            code.append(f"Used(R) :- {', '.join(premises)}.")
        code.append(f"Head({i},{head}).")
        code.append(f"Rule{width}({','.join(map(str, [i, head, *body]))}).")
        if demand:
            code.extend(f"Member({i},{a})." for a in body)
    return "\n".join(dict.fromkeys(code)) + "\n"


def read_tcalc(executable: Path, path: Path, engine: str = "seminaive") -> dict[str, set[int]]:
    run = subprocess.run([executable.resolve(), "--engine", engine, path.resolve()],
                         capture_output=True, text=True, timeout=45)
    if run.returncode:
        raise RuntimeError(f"tcalc declined {path.name}: {run.stderr.strip()}")
    relations = re.findall(r"-+\n(Need|Have|Used)\n=+\n([\d\n]*)=+\n", run.stdout)
    output = {name: set(map(int, body.split())) for name, body in relations}
    if output.keys() != {"Need", "Have", "Used"}:
        raise ValueError(f"Unexpected tcalc output {run.stdout}")
    return output


def compare_tcalc(executable: Path, directory: Path, sample: list) -> dict:
    directory.mkdir(parents=True, exist_ok=True)
    summary = Counter()
    details = {}
    for name, facts, rules, queries in sample:
        program = packet(facts, rules, queries)
        sources = set(program["sources"])
        index = atom_indices(facts, rules, queries)
        known = {index[atom] for atom in closure(facts.values(), rules)}
        need = {atom for pair in program["queries"] for atom in pair}
        while additions := {
            a for head, body in program["clauses"] if head in need for a in body if a not in need
        }:
            need.update(additions)
        results = {}
        for demand in (False, True):
            mode = "demand" if demand else "forward"
            path = directory / f"{name}-{mode}.dl"
            path.write_text(datalog(program, sources, demand))
            results[mode] = read_tcalc(executable, path)
            have = results[mode]["Have"]
            assert results[mode]["Need"] == (need if demand else set())
            assert have == (known & need if demand else known)
            used = {i for i, (head, body) in enumerate(program["clauses"])
                    if (not demand or head in results[mode]["Need"]) and set(body) <= have}
            assert results[mode]["Used"] == used
        summary["theories"] += 1
        summary["queries_matched"] += len(queries)
        summary["forward_enabled_rule_instances"] += len(results["forward"]["Used"])
        summary["demand_enabled_rule_instances"] += len(results["demand"]["Used"])
        if name.startswith(("fiona-", "lion-")):
            have = results["demand"]["Have"]
            flags = [(pos in have, neg in have) for pos, neg in program["queries"]]
            labels = {(True, False): "True", (False, True): "False",
                       (False, False): "Unknown", (True, True): "Both"}
            details[name] = {
                "labels": [labels[pair] for pair in flags],
                "demand_rule_instances": [
                    {"source_rule": rules[i].source, "head": rules[i].head, "premises": rules[i].body}
                    for i in sorted(results["demand"]["Used"])
                ],
            }

    path = directory / "fiona-slice-demand.dl"
    assert read_tcalc(executable, path, "naive") == read_tcalc(executable, path)
    limited = subprocess.run([executable.resolve(), "--engine", "naive", "--max-candidates", "1", path],
                             capture_output=True, text=True, timeout=45)
    assert limited.returncode == 2 and "BudgetCutoff" in limited.stderr
    worlds = [bits for bits in product((0, 1), repeat=3)
              if details[f"lion-world-{''.join(map(str, bits))}"]["labels"] == ["True"]]
    independent_mass = sum(prod(Fraction(3 if on else 1, 4) for on in bits) for bits in worlds)
    shared_mass = sum(Fraction(1, 16) + (Fraction(1, 2) if all(bits) else 0) for bits in worlds)
    assert independent_mass == Fraction(45, 64) and shared_mass == Fraction(11, 16)
    return {
        **summary, "named_controls": details, "budget_cutoff_status": limited.returncode,
        "lion_mass_from_native_world_labels": {"independent": independent_mass, "shared": shared_mass},
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path)
    parser.add_argument("--lean-root", type=Path, default=Path(__file__).resolve().parents[1] / "lean/mettapedia")
    parser.add_argument("--seed", type=int, default=19)
    parser.add_argument("--tcalc", type=Path, help="Optional native dl_tcalc executable")
    parser.add_argument("--fixtures", type=Path, help="Output directory for generated Datalog fixtures")
    args = parser.parse_args()
    if bool(args.tcalc) != bool(args.fixtures):
        parser.error("--tcalc and --fixtures are supplied together")

    command = ["lake", "env", "lean", "-M", "24576", "--run",
               "Mettapedia/Examples/PLN/ProofWriterWorldModel.lean"]
    with ZipFile(args.archive) as archive:
        member = next(name for name in archive.namelist() if name.endswith("/OWA/depth-5/meta-test.jsonl"))
        with subprocess.Popen(command, cwd=args.lean_root, stdin=subprocess.PIPE,
                              stdout=subprocess.PIPE, text=True) as process:
            controls = follow_report_controls(archive, process)
            with archive.open(member) as records:
                experiment, sample = replay(map(json.loads, records), process, args.seed)
            process.stdin.close()
            if process.wait(timeout=45):
                raise RuntimeError("Lean evaluator failed while closing")
        summary = {"split": member, "report_controls": controls, "replay": experiment}
        if args.tcalc:
            fiona, fiona_query, fiona_shared = reused_premise_control(archive)
            lion, lion_query, (first, second) = overlap_case(archive)
            reduced, _ = reuse_slices(fiona, fiona_query, fiona_shared)
            facts, rules = theory(reduced)
            query = literal(reduced["questions"][fiona_query]["representation"])
            sample.append(("fiona-slice", facts, rules, [query]))
            lion_shared, = first & second
            for prefix, (record, key, shared) in (
                ("fiona", (fiona, fiona_query, fiona_shared)), ("lion", (lion, lion_query, lion_shared))
            ):
                facts, rules = theory(record)
                query = literal(record["questions"][key]["representation"])
                sample.append((f"{prefix}-full", facts, rules, [query]))
                sample.append((f"{prefix}-without-shared",
                               {key: atom for key, atom in facts.items() if key != shared}, rules, [query]))
                if prefix == "lion":
                    soft = sorted(first | second)
                    for bits in product((0, 1), repeat=len(soft)):
                        off = {key for key, on in zip(soft, bits, strict=True) if not on}
                        active = {key: atom for key, atom in facts.items() if key not in off}
                        sample.append((f"lion-world-{''.join(map(str, bits))}", active, rules, [query]))
            summary["tcalc"] = compare_tcalc(args.tcalc, args.fixtures, sample)
    print(json.dumps(summary, indent=2, default=str))


if __name__ == "__main__":
    main()
