#!/usr/bin/env python3
"""Run the exact finite Lean backend in ChainerGame's SupplyNet scale harness."""

import argparse
from fractions import Fraction
import json
from pathlib import Path
import subprocess
import sys

from stochastic_inference_check import factor


def rate(value):
    if isinstance(value, bool):
        return Fraction(int(value))
    return Fraction(str(value))


def transition(parent, child, given, without):
    p, q = rate(given), rate(without)
    return factor([parent, child], [1 - q, q, 1 - p, p])


class LeanFactors:
    name = "lean-rational-factors"

    def __init__(self, process):
        self.process = process

    def begin(self, network, rates, history):
        self.network, self.rates = network, rates
        self.periods = []
        self.observations = {}
        self.boundary = (history[-1][0].values if history else
                         dict.fromkeys(network.fronts, rates.front_stationary))

    def resolve(self, period, observed):
        assert self.periods.pop(0) == period.name
        self.boundary = period.values
        self.observations = {key: value for key, value in self.observations.items()
                             if key[2] != period.name}

    def beliefs(self, observation, queries, budget):
        self.periods.append(observation.period)
        self.observations.update(observation.seen)
        variables = (*self.network.fronts, *self.network.nodes)
        keys = [(*v, period) for period in self.periods for v in variables]
        index = {key: i for i, key in enumerate(keys)}
        base = []
        for i, period in enumerate(self.periods):
            for front in self.network.fronts:
                child = index[(*front, period)]
                if i == 0:
                    previous = rate(self.boundary[front])
                    p = ((1 - previous) * rate(self.rates.front_start) +
                         previous * rate(self.rates.front_persist))
                    base.append(factor([child], [1 - p, p]))
                else:
                    parent = index[(*front, self.periods[i - 1])]
                    base.append(transition(parent, child, self.rates.front_persist, self.rates.front_start))
            for v, node in self.network.nodes.items():
                base.append(transition(index[(*node.parent, period)], index[(*v, period)],
                                       node.given, node.without))
        edits = [
            {"observe": {"id": "/".join(key),
                         "likelihood": factor([index[key]], [int(not value), int(value)])}}
            for key, value in self.observations.items()
        ]
        requests = [{"probability": {"event": factor([index[key]], [0, 1])}} for key in queries]
        packet = {"domains": [2] * len(keys), "base": base, "operations": edits + requests}
        self.process.stdin.write(json.dumps(packet) + "\n")
        self.process.stdin.flush()
        line = self.process.stdout.readline()
        if not line:
            raise RuntimeError("The Lean backend ended during a round")
        replies = json.loads(line)
        assert isinstance(replies, list) and len(replies) == len(edits) + len(queries), replies
        assert all(reply.get("status") == "recorded" for reply in replies[:len(edits)]), replies
        return {key: float(Fraction(*reply["value"]))
                for key, reply in zip(queries, replies[len(edits):], strict=True)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("harness", type=Path, help="ChainerGame-benchmarks checkout")
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--rounds", type=int, default=10)
    parser.add_argument("--size", default="s")
    args = parser.parse_args()
    sys.path.insert(0, str(args.harness.resolve() / "src"))
    from supplynet import scale

    config = scale.GameConfig(seed=args.seed, size=scale.SIZES[args.size], rounds=args.rounds)
    cmd = ["lake", "env", "lean", "--run",
           "Mettapedia/ProbabilityTheory/StochasticInference/JsonReplay.lean"]
    repo = Path(__file__).resolve().parents[1]
    with subprocess.Popen(cmd, cwd=repo / "lean/mettapedia", text=True,
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE) as process:
        try:
            def record(row):
                if row["coverage"] != 1 or row["posterior_error"] >= 1e-12:
                    raise AssertionError(row)
                print(json.dumps(row), flush=True)

            summary = scale.run_game(config, LeanFactors(process), on_round=record)
        finally:
            process.stdin.close()
        if process.wait():
            raise RuntimeError("The Lean backend failed")
    print(json.dumps(summary), flush=True)


if __name__ == "__main__":
    main()
