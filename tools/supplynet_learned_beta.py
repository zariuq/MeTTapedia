#!/usr/bin/env python3
"""Compare plug-in and integrated Beta predictions on learned SupplyNet stages 1 and 2."""

import argparse
from fractions import Fraction
from functools import cache
from itertools import product
import json
from math import factorial, prod
from pathlib import Path
import sys


@cache
def word_mass(positives, negatives):
    return Fraction(factorial(positives) * factorial(negatives),
                    factorial(positives + negatives + 1))


@cache
def row_mass(prior, current, integrate):
    yes, no = prior
    m_yes, m_no = current
    if integrate:
        return word_mass(yes + m_yes, no + m_no) / word_mass(yes, no)
    p = Fraction(yes + 1, yes + no + 2)
    return p ** m_yes * (1 - p) ** m_no


def likelihood(training, parents, outcomes, integrate):
    current = [[0, 0], [0, 0]]
    for parent, outcome in zip(parents, outcomes, strict=True):
        if outcome is not None:
            current[parent][int(not outcome)] += 1
    return prod(row_mass(training[parent], tuple(current[parent]), integrate)
                for parent in (False, True))


class LearnedForest:
    """Learn rule rows from the serialized statements seen by the chainer.

    Each region is a storm chain with block children and shipment leaves.
    Within a region, sum over each storm path, and within a route sum over
    its block paths. Each parameter is integrated once over all its uses.
    """

    def __init__(self, statements, parser, integrate, plug_in_reference=None):
        self.statements = statements
        self.parser = parser
        self.integrate = integrate
        self.name = "integrated-beta" if integrate else "laplace-plug-in"
        self.reference = plug_in_reference
        self.plug_in_max_delta = 0.0

    def begin(self, network, rates, history):
        if self.reference is not None:
            self.reference.begin(network, rates, history)
        self.rules = {}
        self.truth = {}
        self.resolved = []
        self.window = []
        self.configure(network, rates)
        if not history:
            raise ValueError("A resolved history establishes the initial storm boundary")
        for period, observation in history:
            self.add(self.statements.observation_facts(observation))
            self.record_resolution(period, observation)

    def configure(self, network, rates):
        self.routes = {}
        self.shipments = {}
        for index, text in enumerate(self.statements.rules(network, rates, learned=True)):
            rule = self.parser.rule(text, index)
            kind, args = rule.head
            node = (kind, *args)
            if len(args) != 1 or rule.rates is not None or node in self.rules:
                raise ValueError(f"Expected a unique learned node {text}")
            self.rules[node] = rule
            if kind == "Storm":
                expected = ["And", ["NextPeriod", "$p", "$t"], ["Storm", args[0], "$p"]]
                if rule.antecedent != expected or rule.consequent[-1] != "$t":
                    raise ValueError(f"Expected a storm persistence rule {text}")
            else:
                parents = {"Blocked": ("Storm", self.routes), "Late": ("Blocked", self.shipments)}
                if kind not in parents:
                    raise ValueError(f"Unsupported learned rule {text}")
                parent_kind, children = parents[kind]
                if (len(rule.antecedent) != 3 or rule.antecedent[0] != parent_kind or
                    rule.antecedent[-1] != rule.consequent[-1]):
                    raise ValueError(f"Expected a same-period edge {text}")
                children.setdefault(tuple(rule.antecedent[:2]), []).append(node)
        self.roots = self.routes.keys()
        self.temporal = any(node[0] == "Storm" for node in self.rules)

    def add(self, lines):
        for text in lines:
            _, _, term, (_, value, confidence) = self.parser.parse(text)
            if float(confidence) != 1 or float(value) not in (0, 1):
                raise ValueError(f"Expected a hard label {text}")
            key, result = tuple(term), bool(float(value))
            if key in self.truth and self.truth[key] != result:
                raise ValueError(f"Conflicting labels for {key}")
            self.truth[key] = result

    def record_resolution(self, period, observation):
        self.add(self.statements.resolution_facts(period, observation))
        self.resolved.append(period.name)

    def resolve(self, period, observation):
        if self.reference is not None:
            self.reference.resolve(period, observation)
        if self.window.pop(0) != period.name:
            raise ValueError(f"Out-of-order resolution {period.name}")
        self.record_resolution(period, observation)

    def fitted_counts(self):
        resolved = set(self.resolved)
        learner = self.parser.Learner([(list(key), value) for key, value in self.truth.items()
                                     if key[-1] in resolved])
        counts = {}
        for node in self.rules.keys() | set(self.roots):
            rows = [[0, 0], [0, 0]]
            rule = self.rules.get(node)
            for period in self.resolved:
                outcome = learner.truth.get((*node, period))
                if outcome is None:
                    continue
                parent = (learner.antecedent(rule.antecedent, {rule.consequent[-1]: period})
                          if rule is not None else False)
                if parent is not None:
                    rows[parent][int(not outcome)] += 1
            counts[node] = tuple(map(tuple, rows))
        return counts

    def route_paths(self, route, counts):
        choices = []
        for period in self.window:
            observed = self.truth.get((*route, period))
            choices.append((False, True) if observed is None else (observed,))
        for blocks in product(*choices):
            shipment_mass = prod(
                likelihood(counts[shipment], blocks,
                           [self.truth.get((*shipment, p)) for p in self.window], self.integrate)
                for shipment in self.shipments.get(route, ()))
            yield blocks, shipment_mass

    def posterior(self):
        counts = self.fitted_counts()
        answers = {}
        width = len(self.window)
        for storm, routes in self.routes.items():
            paths = {route: list(self.route_paths(route, counts)) for route in routes}
            true_mass = {(node, i): Fraction(0) for node in (storm, *routes) for i in range(width)}
            evidence = Fraction(0)
            for storms in product((False, True), repeat=width):
                if storm in self.rules:
                    before = self.truth[(*storm, self.resolved[-1])]
                    previous = (before, *storms[:-1])
                else:
                    previous = (False,) * width
                storm_mass = likelihood(counts[storm], previous, storms, self.integrate)
                route_marginals = {}
                for route in routes:
                    weights = [(blocks, shipments * likelihood(counts[route], storms, blocks, self.integrate))
                               for blocks, shipments in paths[route]]
                    z = sum(weight for _, weight in weights)
                    storm_mass *= z
                    route_marginals[route] = tuple(
                        sum(weight for blocks, weight in weights if blocks[i]) / z for i in range(width))
                evidence += storm_mass
                for i, is_storm in enumerate(storms):
                    if is_storm:
                        true_mass[storm, i] += storm_mass
                for route, marginals in route_marginals.items():
                    for i, marginal in enumerate(marginals):
                        true_mass[route, i] += storm_mass * marginal
            for (node, i), mass in true_mass.items():
                answers[(*node, self.window[i])] = mass / evidence
        return answers

    def beliefs(self, observation, keys, budget):
        self.add(self.statements.observation_facts(observation))
        if self.temporal:
            previous = self.window[-1] if self.window else self.resolved[-1]
            if self.truth.get(("NextPeriod", previous, observation.period)) is not True:
                raise ValueError(f"Missing predecessor of {observation.period}")
        self.window.append(observation.period)
        posterior = self.posterior()
        answers = {key: float(posterior[key]) for key in keys}
        if self.reference is not None:
            reference = self.reference.beliefs(observation, keys, budget)
            delta = max(abs(value - reference[key]) for key, value in answers.items())
            self.plug_in_max_delta = max(delta, self.plug_in_max_delta)
            if delta > 1e-12:
                raise AssertionError(f"Plug-in answer disagreed with the learned reference by {delta}")
        return answers

    def summary(self):
        return {"plug_in_max_delta": self.plug_in_max_delta} if self.reference is not None else {}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("harness", type=Path, help="ChainerGame-benchmarks checkout")
    parser.add_argument("--stage", type=int, choices=(1, 2), default=2)
    parser.add_argument("--seeds", type=int, nargs="+", default=[1, 2, 3, 4])
    parser.add_argument("--regions", type=int, default=3)
    parser.add_argument("--history", type=int, default=30)
    parser.add_argument("--rounds", type=int, default=20)
    args = parser.parse_args()
    sys.path.insert(0, str(args.harness.resolve() / "src"))
    from supplynet import metta, problog_backend
    from supplynet.backends import LearnedReferenceBackend
    from supplynet.game import GameConfig, run_game

    for seed in args.seeds:
        config = GameConfig(seed=seed, stage=args.stage, regions=args.regions,
                            history=args.history, rounds=args.rounds)
        for integrate in (False, True):
            backend = LearnedForest(metta, problog_backend, integrate,
                                    None if integrate else LearnedReferenceBackend())
            print(json.dumps(run_game(config, backend)), flush=True)


if __name__ == "__main__":
    main()
