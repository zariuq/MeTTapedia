#!/usr/bin/env python3
"""Run the Lean feature learner and compare frontier policies on separate tasks."""

import itertools
import json
from fractions import Fraction
from math import log
from pathlib import Path
from random import Random
import subprocess


def label(bits, pair, inverted):
    return (bits[pair[0]] != bits[pair[1]]) != inverted


def samples(seed, pair, inverted, count=64):
    rng = Random(seed)
    result = []
    for id_ in range(count):
        channels = [rng.randrange(256) for _ in range(6)]
        bits = [value >= 128 for value in channels]
        result.append({"id": id_, "input": bits, "outcome": label(bits, pair, inverted)})
    return result


def packet(seed, pair, training):
    rows = samples(seed, pair, False)
    edits = [{"record": {"sample": row}} for row in rows]
    edits.extend([edits[0], {"withdraw": {"id": 0}}, {"restore": {"id": 0}}])
    queries = list(itertools.islice((list(bits) for bits in
                   itertools.product((False, True), repeat=6)), seed % 8, None, 5))
    return {"features": 6, "training": training, "edits": edits, "queries": queries,
            "budgets": [8, 20, 40, 80, 127], "checkFull": True, "reusePrefix": True}


def check(result, request, pair):
    exact = [Fraction(*p) for p in result["full"]]
    truths = [label(bits, pair, False) for bits in request["queries"]]
    measured = {}
    for policy in ("indexed", "learned"):
        steps = result[policy]
        assert [step["budget"] for step in steps] == request["budgets"]
        measured[policy] = []
        preceding = [(Fraction(0), Fraction(1)) for _ in exact]
        for step in steps:
            intervals = [tuple(Fraction(*end) for end in interval) for interval in step["intervals"]]
            assert all(0 <= lo <= value <= hi <= 1
                       for (lo, hi), value in zip(intervals, exact, strict=True))
            assert all(old_low <= low <= high <= old_high for (old_low, old_high), (low, high) in
                       zip(preceding, intervals, strict=True))
            preceding = intervals
            probs = [Fraction(*p) if p is not None else Fraction(1, 2) for p in step["bestPredictions"]]
            losses = [-log(float(p if truth else 1-p))
                      for truth, p in zip(truths, probs, strict=True)]
            measured[policy].append({"visited": step["visited"],
                "active": step["best"] is not None,
                "loss": sum(losses) / len(losses),
                "width": float(sum(hi-lo for lo, hi in intervals) / len(intervals))})
        assert steps[-1]["visited"] == 64
        assert [tuple(Fraction(*end) for end in interval) for interval in steps[-1]["intervals"]] == [
            (value, value) for value in exact]
    return measured


def main():
    root = Path(__file__).resolve().parents[1]
    training = [samples(seed, (2, 5), seed % 2 == 0, 96) for seed in range(1, 7)]
    tasks = [(seed, pair, packet(seed, pair, training))
             for pair in ((2, 5), (0, 1)) for seed in range(71, 75)]
    command = ["lake", "env", "lean", "--run",
               "Mettapedia/Examples/PLN/CompositionalLearningReplay.lean"]
    process = subprocess.run(command, cwd=root / "lean/mettapedia", text=True, check=True,
                             input="".join(json.dumps(request) + "\n" for _, _, request in tasks),
                             stdout=subprocess.PIPE)
    results = [json.loads(line) for line in process.stdout.splitlines()]
    for (seed, pair, request), result in zip(tasks, results, strict=True):
        if "error" in result:
            raise RuntimeError(result["error"])
        print(json.dumps({"seed": seed, "pair": pair, "budgets": request["budgets"],
                          "priority": result["priority"], **check(result, request, pair)}))


if __name__ == "__main__":
    main()
