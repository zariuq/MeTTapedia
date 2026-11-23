#!/usr/bin/env python3
"""Exact tied-rate inference over the unresolved window of SupplyNet."""

import argparse
from dataclasses import replace
from fractions import Fraction
from functools import lru_cache
from itertools import product
import json
from math import prod
from pathlib import Path
import sys

from supplynet_learned_beta import LearnedForest, row_mass


@lru_cache(maxsize=8192)
def common_denominator(counts, width, integrate):
    """Denominators of any uses of each row divide the width-use denominator."""
    totals = [sum(row) + 2 for row in counts]
    if integrate:
        return prod(start + i for start in totals for i in range(width))
    return prod(total ** width for total in totals)


@lru_cache(maxsize=65536)
def integer_weight(counts, width, parent_true, child_true, both_true, integrate):
    parent_false = width - parent_true
    child_true_parent_false = child_true - both_true
    weight = (row_mass(counts[0], (child_true_parent_false, parent_false - child_true_parent_false), integrate) *
              row_mass(counts[1], (both_true, parent_true - both_true), integrate))
    numerator, remainder = divmod(weight.numerator * common_denominator(counts, width, integrate),
                                 weight.denominator)
    if remainder:
        raise ArithmeticError("The common denominator failed")
    return numerator


class Trajectories(LearnedForest):
    def __init__(self, statements, parser, integrate, plug_in_reference=None, *, scale=False):
        super().__init__(statements, parser, integrate, plug_in_reference)
        self.scale = scale

    def configure(self, network, rates):
        texts = (self.statements.rules(network, rates) if self.scale else
                 self.statements.rules(network, rates, learned=True))
        self.parents, self.children, self.persistence = {}, {}, set()
        self.cell = None
        given = []
        for i, text in enumerate(texts):
            clause = self.parser.rule(text, i)
            if self.scale:
                clause = replace(clause, rates=None)
            if clause.rates is not None:
                if clause.rates != (1, 0):
                    raise ValueError(f"Expected a deterministic production rule {text}")
                given.append(clause)
                continue
            node = (clause.head[0], *clause.head[1])
            if len(node) != 2 or node in self.rules:
                raise ValueError(f"Expected one learned row pair per node {text}")
            self.rules[node] = clause
            body = clause.antecedent
            if body[0] == "And":
                expected = ["And", ["NextPeriod", "$p", "$t"], [*node, "$p"]]
                if body != expected or clause.consequent[-1] != "$t":
                    raise ValueError(f"Expected a persistence rule {text}")
                self.persistence.add(node)
            else:
                if len(body) != 3 or body[-1] != clause.consequent[-1]:
                    raise ValueError(f"Expected a same-period edge {text}")
                parent = tuple(body[:2])
                self.parents[node] = parent
                self.children.setdefault(parent, []).append(node)
        nodes = self.rules.keys() | self.children.keys()
        self.roots = tuple(sorted(nodes - self.parents.keys()))
        self.temporal = bool(self.persistence)
        if given:
            self.cell = ProductionCell.from_rules(given)
            if self.cell.fuel not in self.parents:
                raise ValueError("Missing fuel route")
        detached = set(self.cell.degradation) if self.cell is not None else set()
        attached = set()
        pending = list(set(self.roots) - detached)
        while pending:
            node = pending.pop()
            if node in attached:
                raise ValueError("Expected a forest of trajectories")
            attached.add(node)
            pending.extend(self.children.get(node, ()))
        if attached | detached != nodes:
            raise ValueError("The learned dependencies are not a forest")

    def beliefs(self, observation, keys, budget):
        self.requested = {key[:2] for key in keys}
        return super().beliefs(observation, keys, budget)

    def posterior(self):
        periods = self.window
        width = len(periods)
        counts = self.fitted_counts()
        wanted = self.requested
        readouts = set(wanted)
        if self.cell is not None:
            readouts.add(self.cell.fuel)
        relevant = {key[:2] for key in self.truth
                    if len(key) == 3 and key[-1] in periods and key[:2] in counts}

        def ancestors(nodes):
            for node in tuple(nodes):
                while node in self.parents:
                    node = self.parents[node]
                    nodes.add(node)
            return nodes

        needed = ancestors(readouts)
        useful = ancestors(needed | relevant)

        def paths(node):
            seen = [self.truth.get((*node, period)) for period in periods]
            for bits in product(*((False, True) if bit is None else (bit,) for bit in seen)):
                yield sum(int(bit) << i for i, bit in enumerate(bits))

        def mass(node, parent, path):
            return integer_weight(counts[node], width, parent.bit_count(), path.bit_count(),
                                  (parent & path).bit_count(), self.integrate)

        def root_mass(node, path):
            parents = (((path << 1) & ((1 << width) - 1)) |
                       int(self.truth[(*node, self.resolved[-1])])) if node in self.persistence else 0
            return mass(node, parents, path)

        local, upward = {}, {}
        cell_paths = {}
        if self.cell is not None:
            cell_paths = {node: [(path, root_mass(node, path)) for path in paths(node)]
                          for node in self.cell.degradation}
        cell_messages = {}
        answers = {}

        def gather(node):
            children = [child for child in self.children.get(node, ()) if child in useful]
            observed_leaves = {}
            for child in children:
                if child not in needed and not self.children.get(child):
                    measured = [(i, self.truth[(*child, period)]) for i, period in enumerate(periods)
                                if (*child, period) in self.truth]
                    mask = sum(1 << i for i, _ in measured)
                    yes = sum(1 << i for i, truth in measured if truth)
                    observed_leaves[child] = (mask, yes)
                else:
                    gather(child)
            table = {}
            for path in paths(node):
                weight = 1
                if self.cell is not None and node == self.cell.fuel:
                    weight, marginals = self.cell.read(self.truth, periods, self.resolved[-1],
                                                       path, cell_paths)
                    cell_messages[path] = marginals
                for child in children:
                    if child in observed_leaves:
                        mask, yes = observed_leaves[child]
                        # Integrate every unreported emission over both outcomes.
                        message = integer_weight(counts[child], mask.bit_count(), (path & mask).bit_count(),
                                                 yes.bit_count(), (path & yes).bit_count(), self.integrate)
                    else:
                        message = sum(weight * mass(child, path, outcome)
                                      for outcome, weight in local[child].items())
                        upward[child][path] = message
                    weight *= message
                if weight:
                    table[path] = weight
            local[node] = table
            upward[node] = {}

        def publish(node, outside, normalizer):
            if node in wanted:
                for i, period in enumerate(periods):
                    answers[(*node, period)] = Fraction(sum(outside[path] * weight
                        for path, weight in local[node].items() if path & (1 << i)), normalizer)
            if self.cell is not None and node == self.cell.fuel:
                for path, weight in local[node].items():
                    probability = Fraction(weight * outside[path], normalizer)
                    for key, value in cell_messages[path].items():
                        answers[key] = answers.get(key, 0) + probability * value
            for child in self.children.get(node, ()):
                if child not in needed:
                    continue
                updated = dict.fromkeys(local[child], 0)
                for path, weight in local[node].items():
                    if outside[path]:
                        # The stored inside weight contains this message as a factor.
                        cavity = outside[path] * (weight // upward[child][path])
                        for outcome in updated:
                            updated[outcome] += cavity * mass(child, path, outcome)
                publish(child, updated, normalizer)

        detached = set(self.cell.degradation) if self.cell is not None else set()
        for root in self.roots:
            if root not in useful or root in detached:
                continue
            gather(root)
            outside = {path: root_mass(root, path) for path in local[root]}
            normalizer = sum(weight * outside[path] for path, weight in local[root].items())
            if not normalizer:
                raise ValueError("The reports have zero evidence mass")
            publish(root, outside, normalizer)
        return answers


class ProductionCell:
    """A deterministic cell whose earlier production is observed each period.

    Conditional on the fuel route path and those reports, the degradation
    trajectories have independent weights. The untimed positive loop uses
    its least fixed point.
    """

    def __init__(self, fuel, mine, power, inputs, timed):
        self.fuel, self.mine, self.power, self.inputs, self.timed = fuel, mine, power, inputs, timed
        self.degradation = [("Degraded", site) for site in (power, mine, *inputs)]

    @classmethod
    def from_rules(cls, rules):
        by_name = {tuple(rule.consequent[:-1]): rule.antecedent for rule in rules}
        if len(by_name) != len(rules):
            raise ValueError("Duplicate production heads")
        arrival = by_name.pop(("FuelArrived",))
        timed = len(arrival) == 4
        transport_time = "$p" if timed else "$t"
        mine, fuel = arrival[-2][1], arrival[-1][1][1]
        expected = ["And"] + ([["NextPeriod", "$p", "$t"]] if timed else [])
        expected += [["Producing", mine, transport_time], ["Not", ["Blocked", fuel, transport_time]]]
        (fuelled,) = [head for head in by_name if head[0] == "Fuelled" and len(head) == 2]
        power = fuelled[1]
        if (arrival != expected or by_name.pop(fuelled) !=
            ["Or", ["StockedFuel", "$t"], ["FuelArrived", "$t"]]):
            raise ValueError("Unrecognized fuel rule")
        if (by_name.pop(("Producing", power)) !=
            ["And", ["Fuelled", power, "$t"], ["Not", ["Degraded", power, "$t"]]]):
            raise ValueError("Unrecognized power rule")
        inputs = {}
        for (predicate, site), antecedent in by_name.items():
            terms = [part[1] for part in antecedent[1:] if part[0] == "InputArrived"]
            expected = ["And", ["Producing", power, "$t"]]
            if site != mine:
                (input_name,) = terms
                inputs[site] = input_name
                expected.append(["InputArrived", input_name, "$t"])
            expected.append(["Not", ["Degraded", site, "$t"]])
            if predicate != "Producing" or antecedent != expected:
                raise ValueError(f"Unrecognized production rule for {site}")
        return cls(("Blocked", fuel), mine, power, inputs, timed)

    def read(self, truth, periods, boundary, fuel, trajectories):
        predecessors = (boundary, *periods[:-1])
        fuel_bits = tuple(bool(fuel & (1 << i)) for i in range(len(periods)))
        blocked = (truth[(*self.fuel, boundary)], *fuel_bits[:-1]) if self.timed else fuel_bits
        supplied = [truth["StockedFuel", period] or
                    (self.timed and truth["Producing", self.mine, before] and not is_blocked)
                    for period, before, is_blocked in zip(periods, predecessors, blocked, strict=True)]
        total, marginals = 1, {}
        for node in self.degradation:
            site = node[1]
            has_input = [site not in self.inputs or truth["InputArrived", self.inputs[site], period]
                         for period in periods]
            enabled = (supplied[:-1] if site == self.power else
                       [truth["Producing", self.power, period] and available
                        for period, available in zip(periods[:-1], has_input[:-1], strict=True)])
            reported = [truth["Producing", site, period] for period in periods[:-1]]
            eligible = [(path, weight) for path, weight in trajectories[node]
                        if all((can_produce and not (path & (1 << i))) == observed
                               for i, (can_produce, observed) in enumerate(zip(enabled, reported, strict=True)))]
            support = sum(weight for _, weight in eligible)
            if not support:
                return 0, {}
            total *= support
            for i, period in enumerate(periods):
                marginals[(*node, period)] = Fraction(
                    sum(weight for path, weight in eligible if path & (1 << i)), support)
            marginals["Producing", site, periods[-1]] = (
                (1 - marginals[(*node, periods[-1])]) * has_input[-1])
        power_key = ("Producing", self.power, periods[-1])
        marginals[power_key] *= supplied[-1]
        for site in (self.mine, *self.inputs):
            marginals["Producing", site, periods[-1]] *= marginals[power_key]
        return total, marginals


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("harness", type=Path, help="ChainerGame-benchmarks checkout")
    parser.add_argument("--stage", choices=("3", "scale"), default="3")
    parser.add_argument("--cycle", choices=("timed", "untimed"), default="timed")
    parser.add_argument("--seeds", type=int, nargs="+", default=[1, 2, 3, 4])
    parser.add_argument("--regions", type=int, default=3)
    parser.add_argument("--size", default="s")
    parser.add_argument("--window", type=int, default=4)
    parser.add_argument("--history", type=int, default=30)
    parser.add_argument("--rounds", type=int, default=20)
    parser.add_argument("--stream", action="store_true", help="Emit each completed round")
    args = parser.parse_args()
    sys.path.insert(0, str(args.harness.resolve() / "src"))
    from supplynet import metta, problog_backend, scale
    from supplynet.backends import LearnedReferenceBackend
    from supplynet.game import GameConfig, run_game

    for seed in args.seeds:
        for integrate in (False, True):
            def on_round(row):
                print(json.dumps({"seed": seed, "backend": backend.name, **row}), flush=True)

            report = on_round if args.stream else None
            if args.stage == "scale":
                backend = Trajectories(scale, problog_backend, integrate, scale=True)
                config = scale.GameConfig(seed=seed, size=scale.SIZES[args.size], window=args.window,
                                          history=args.history, rounds=args.rounds)
                result = scale.run_game(config, backend, on_round=report)
                result["variant"] = "withheld-rates"
            else:
                backend = Trajectories(metta, problog_backend, integrate,
                                       None if integrate else LearnedReferenceBackend())
                config = GameConfig(seed=seed, stage=3, cycle=args.cycle, regions=args.regions,
                                    history=args.history, rounds=args.rounds)
                result = run_game(config, backend, on_round=report)
            print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
