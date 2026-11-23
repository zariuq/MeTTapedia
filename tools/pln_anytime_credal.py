#!/usr/bin/env python3
"""Run the Lean credal projection against exact small joint witnesses."""

import json
from fractions import Fraction as Q
from pathlib import Path
import subprocess


def event(n, bit):
    return [bool(i & (1 << bit)) for i in range(n)]


def complement(mask):
    return [not value for value in mask]


def conjunction(first, second):
    return [a and b for a, b in zip(first, second, strict=True)]


def pair(x):
    return [x.numerator, x.denominator]


def interval(event, given, lower, upper=None):
    return {"event": event, "condition": given, "lower": pair(Q(lower)),
            "upper": pair(Q(lower if upper is None else upper))}


def packet(base, query, evidence, budgets):
    return {"worlds": len(query), "constraints": base, "query": query,
            "evidence": evidence, "budgets": budgets}


def mass(weights, mask):
    return sum((w for w, holds in zip(weights, mask, strict=True) if holds), Q(0))


def check_witness(weights, problem):
    assert sum(weights) == 1 and min(weights) >= 0
    for rule in problem["constraints"]:
        support = mass(weights, rule["condition"])
        joint = mass(weights, conjunction(rule["event"], rule["condition"]))
        assert Q(*rule["lower"]) * support <= joint <= Q(*rule["upper"]) * support
    return mass(weights, conjunction(problem["query"], problem["evidence"])) / mass(weights, problem["evidence"])


def chain_witness(in_branch, out_branch):
    # The bit order is A, B, C. Each row here is a two-by-two coupling.
    output = [Q(0)] * 8
    for inside, common, first, second in ((True, in_branch, Q(2, 5), Q(3, 8)),
                                         (False, out_branch, Q(1, 10), Q(1, 8))):
        prefix = int(inside) << 1
        output[prefix | 5] = common
        output[prefix | 1] = first - common
        output[prefix | 4] = second - common
        output[prefix] = Q(1, 2) - first - second + common
    return output


def cases():
    budgets = [0, 8, 32, 128]
    a, b, c = (event(8, index) for index in range(3))
    all_worlds = [True] * 8
    base = [interval(a, all_worlds, Q(1, 2)), interval(b, all_worlds, Q(1, 2)),
            interval(b, a, Q(4, 5)), interval(c, b, Q(3, 4)),
            interval(c, complement(b), Q(1, 4))]
    chain = packet(base, c, a, budgets)
    endpoints = [chain_witness(Q(11, 40), Q(0)), chain_witness(Q(3, 8), Q(1, 10))]
    yield "three_period_no_screening", chain, [check_witness(w, chain) for w in endpoints]

    # These rows encode certified absolute deviations of 1/20 and 1/10
    # from 3/4 and 1/4 on their corresponding A strata.
    learned = base + [interval(c, conjunction(a, b), Q(7, 10), Q(4, 5)),
                      interval(c, conjunction(a, complement(b)), Q(3, 20), Q(7, 20))]
    bounded = packet(learned, c, a, budgets)
    witnesses = [chain_witness(Q(7, 25), Q(3, 200)), chain_witness(Q(8, 25), Q(7, 200))]
    yield "three_period_certified_deviations", bounded, [check_witness(w, bounded) for w in witnesses]

    a, c = event(4, 0), event(4, 1)
    all_worlds = [True] * 4
    sparse = packet([interval(c, a, Q(3, 4))], c, a, budgets)
    assert check_witness([Q(0), Q(1, 4), Q(0), Q(3, 4)], sparse) == Q(3, 4)
    assert mass([Q(1), Q(0), Q(0), Q(0)], a) == 0
    yield "support_can_be_zero", sparse, [Q(3, 4), Q(3, 4)]
    yield "no_support", packet([interval(a, all_worlds, Q(0))], c, a, budgets), None
    yield "inconsistent", packet([interval(a, all_worlds, Q(0)),
                                 interval(a, all_worlds, Q(1))], c, all_worlds, budgets), None


def check(stages, request, expected):
    previous = [Q(0), Q(1)]
    assert [row["pairsPerPivot"] for row in stages] == request["budgets"]
    for row in stages:
        observed = row["interval"]
        if observed is None:
            assert expected is None, row
            previous = None
            continue
        lo, hi = (Q(*endpoint) for endpoint in observed)
        assert previous is not None and previous[0] <= lo <= hi <= previous[1], row
        if expected is not None:
            assert lo <= expected[0] <= expected[1] <= hi, row
        if row["projectionComplete"]:
            assert [lo, hi] == expected, (row, expected)
        previous = [lo, hi]
    assert stages[-1]["projectionComplete"] or previous is None, stages
    assert previous == expected


def main():
    root = Path(__file__).resolve().parents[1]
    tasks = list(cases())
    cmd = ["lake", "env", "lean", "--run", "Mettapedia/Examples/PLN/AnytimeCredalReplay.lean"]
    result = subprocess.run(cmd, cwd=root / "lean/mettapedia", text=True, check=True,
                            input="".join(json.dumps(request) + "\n" for _, request, _ in tasks),
                            stdout=subprocess.PIPE)
    for (name, request, exact), line in zip(tasks, result.stdout.splitlines(), strict=True):
        rows = json.loads(line)
        check(rows, request, exact)
        print(json.dumps({"case": name, "expected": [str(v) for v in exact] if exact else None,
                          "stages": rows}))


if __name__ == "__main__":
    main()
