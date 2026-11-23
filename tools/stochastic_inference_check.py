#!/usr/bin/env python3
"""Check the Lean JSON replay against a separate rational world enumerator."""

import json
from fractions import Fraction
from itertools import product
from math import prod
from pathlib import Path
from random import Random
import subprocess


def ratio(value):
    rational = Fraction(value)
    return [rational.numerator, rational.denominator]


def factor(scope, weights):
    return {"scope": scope, "rows": [ratio(w) for w in weights]}


def read_factor(domains, world, table):
    row = 0
    for coordinate in table["scope"]:
        row = row * domains[coordinate] + world[coordinate]
    return Fraction(*table["rows"][row])


def enumerate_masses(domains, factors, event):
    support = joint = Fraction(0)
    for world in product(*(range(d) for d in domains)):
        weight = prod(read_factor(domains, world, table) for table in factors)
        support += weight
        joint += weight * read_factor(domains, world, event)
    return joint, support


def status(value):
    return {"status": value}


def check_masses(reply, expected):
    joint, support = expected
    assert Fraction(*reply["joint"]) == joint, (reply, expected)
    assert Fraction(*reply["evidence"]) == support, (reply, expected)
    if support:
        assert Fraction(*reply["value"]) == joint / support, (reply, expected)
    else:
        assert reply["value"] is None, reply


def supplynet_diagnosis():
    domains = [2, 2, 2, 2]
    front, blocked, delay, quality = range(4)
    prior = [
        factor([front], ["1/2", "1/2"]),
        factor([front, blocked], ["9/10", "1/10", "1/5", "4/5"]),
        factor([blocked, delay], ["9/10", "1/10", "1/10", "9/10"]),
        factor([quality], ["1/2", "1/2"]),
    ]
    clear = factor([front], [1, 0])
    storm = factor([front], [0, 1])
    report = factor([delay, quality], ["9/20", "1/20", "11/20", "19/20"])
    no_report = factor([delay, quality], ["11/20", "19/20", "9/20", "1/20"])
    event = factor([blocked], [0, 1])
    operations, expected = [], []

    def add(op, result):
        operations.append(op)
        expected.append(result)

    def observe(id_, likelihood, result="recorded"):
        add({"observe": {"id": id_, "likelihood": likelihood}}, status(result))

    def query(*active):
        add({"probability": {"event": event}}, enumerate_masses(domains, prior + list(active), event))

    observe("clear", clear)
    query(clear)
    observe("delay/7", report)
    query(clear, report)
    observe("delay/7", report, "replay")
    query(clear, report)
    observe("delay/8", report)
    query(clear, report, report)
    add({"observe": {"id": "delay/8", "likelihood": no_report}},
        {"error": "Conflicting observation delay/8"})
    query(clear, report, report)
    add({"retract": {"id": "delay/8"}}, status("retracted"))
    observe("delay/8", report, "replay")
    query(clear, report)
    add({"restore": {"id": "delay/8"}}, status("restored"))
    query(clear, report, report)
    observe("delay/9", no_report)
    query(clear, report, report, no_report)
    observe("contradiction", storm)
    query(clear, report, report, no_report, storm)
    return {"domains": domains, "base": prior, "operations": operations}, expected


def finite_cases(seed=19, count=32):
    rng = Random(seed)
    for _ in range(count):
        n = rng.randrange(0, 6)
        domains = [rng.randrange(1, 4) for _ in range(n)]

        def table(make_weight):
            scope = rng.sample(range(n), rng.randrange(min(n, 3) + 1))
            size = prod(domains[v] for v in scope)
            return factor(scope, [make_weight() for _ in range(size)])

        prior = [table(lambda: Fraction(rng.randrange(5), 4)) for _ in range(n // 2)]
        likelihood = table(lambda: Fraction(rng.randrange(5), 4))
        event = table(lambda: rng.randrange(2))
        payoff = table(lambda: Fraction(rng.randrange(-4, 5), 3))
        cases = [
            ({"probability": {"event": event}}, enumerate_masses(domains, prior, event)),
            ({"observe": {"id": "soft", "likelihood": likelihood}}, status("recorded")),
            ({"probability": {"event": event}}, enumerate_masses(domains, prior + [likelihood], event)),
            ({"expectation": {"payoff": payoff}}, enumerate_masses(domains, prior + [likelihood], payoff)),
            ({"retract": {"id": "soft"}}, status("retracted")),
            ({"probability": {"event": event}}, enumerate_masses(domains, prior, event)),
        ]
        if domains:
            index = rng.randrange(n)
            results = [
                enumerate_masses(domains, prior, factor([index], [x == k for x in range(domains[index])]))
                for k in range(domains[index])
            ]
            marginal = [ratio(z / total) for z, total in results] if results[0][1] else None
            cases.append(({"marginal": {"variableIndex": index}}, marginal))
        operations, expected = zip(*cases)
        yield {"domains": domains, "base": prior, "operations": operations}, expected


def main():
    lean_root = Path(__file__).resolve().parents[1] / "lean/mettapedia"
    cases = [supplynet_diagnosis(), *finite_cases()]
    command = [
        "lake", "env", "lean", "--run",
        "Mettapedia/ProbabilityTheory/StochasticInference/JsonReplay.lean",
    ]
    completed = subprocess.run(
        command, cwd=lean_root, input="".join(json.dumps(packet) + "\n" for packet, _ in cases),
        capture_output=True, text=True, check=True,
    )
    responses = list(map(json.loads, completed.stdout.splitlines()))
    for response, (_, expected) in zip(responses, cases, strict=True):
        for reply, check in zip(response, expected, strict=True):
            if isinstance(check, tuple):
                check_masses(reply, check)
            else:
                assert reply == check, (reply, check)
    summary = {
        "packets": len(cases),
        "checked_operations": sum(len(expected) for _, expected in cases),
        "diagnosis": [item["value"] for item in responses[0] if "value" in item],
    }
    print(json.dumps(summary))


if __name__ == "__main__":
    main()
