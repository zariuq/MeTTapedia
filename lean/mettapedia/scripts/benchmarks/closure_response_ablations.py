"""Direct closure-distribution convolution with the same local maintenance."""
from __future__ import annotations

from decimal import Decimal
from fractions import Fraction
import math

from closure_response import (
    Answer, Interval, IntervalOps, LocalState, ProductTree, RationalOps,
    Unsupported, response_profiles, world_weights,
)


class DistributionOps:
    def __init__(self, width, scalar):
        self.scalar = scalar
        self.one = {(1 << (1 << width)) - 1: scalar.one}
        self.products = 0

    def mul(self, first, second):
        result = {}
        for left, p in first.items():
            for right, q in second.items():
                self.products += 1
                key = left & right
                result[key] = self.scalar.add(result.get(key, self.scalar.zero), self.scalar.mul(p, q))
        return result


class DirectPrepared:
    def __init__(self, program):
        program.validate()
        self.width = len(program.boundary)
        self.shared_keys = program.shared
        self.shared_cases = 1 << len(program.shared)
        self.choice_keys = tuple(c.choices for c in program.components)
        self.profiles = []
        for component in program.components:
            atoms = program.boundary + component.choices + program.shared + component.private
            positions = {a: i for i, a in enumerate(atoms)}
            rules = tuple((sum(1 << i for i in {positions[a] for a in rule.body}), 1 << positions[rule.head])
                          for rule in component.rules)
            self.profiles.append(response_profiles(self.width, len(component.choices), len(program.shared), len(atoms), rules))


def local_distributions(prepared, index, state, ops):
    if len(state.probabilities) != len(prepared.choice_keys[index]):
        raise Unsupported('component choice count mismatch')
    weights = world_weights(state, ops)
    result = []
    for profile in prepared.profiles[index]:
        distribution = {}
        for family, weight in zip(profile, weights):
            if weight != ops.zero:
                distribution[family] = ops.add(distribution.get(family, ops.zero), weight)
        result.append(distribution)
    return tuple(result)


class DirectEngine:
    def __init__(self, prepared, states, shared=None):
        if len(states) != len(prepared.choice_keys):
            raise Unsupported('component state count mismatch')
        self.prepared, self.states = prepared, list(states)
        self.shared = shared or LocalState.make([Fraction(1, 2)] * len(prepared.shared_keys))
        if len(self.shared.probabilities) != len(prepared.shared_keys):
            raise Unsupported('shared choice count mismatch')
        self.ops, self.exact_ops = IntervalOps(), RationalOps()
        self.convolution = DistributionOps(prepared.width, self.ops)
        rows = [local_distributions(prepared, i, state, self.ops) for i, state in enumerate(states)]
        self.tree = ProductTree(rows, prepared.shared_cases, self.convolution)
        self.exact_tree = None
        self.exact_dirty = set()
        self.fallbacks = 0

    def update(self, changed, shared=None):
        if any(not 0 <= i < len(self.states) for i in changed):
            raise Unsupported('unknown component')
        if shared is not None and len(shared.probabilities) != len(self.prepared.shared_keys):
            raise Unsupported('shared choice count mismatch')
        rows = {i: local_distributions(self.prepared, i, state, self.ops) for i, state in changed.items()}
        self.tree.replace(rows)
        for i, state in changed.items():
            self.states[i] = state
            self.exact_dirty.add(i)
        if shared is not None:
            self.shared = shared

    def totals(self, root, seed, target, ops):
        avoiding = sum(1 << t for t in range(1 << self.prepared.width)
                       if t & seed == seed and not (t >> target & 1))
        numerator = total = ops.zero
        for h, shared_weight in enumerate(world_weights(self.shared, ops)):
            for family, mass in root[h].items():
                contribution = ops.mul(shared_weight, mass)
                total = ops.add(total, contribution)
                if family & avoiding == 0:
                    numerator = ops.add(numerator, contribution)
        return numerator, total

    def rational(self, seed, target):
        if self.exact_tree is None:
            rows = [local_distributions(self.prepared, i, state, self.exact_ops) for i, state in enumerate(self.states)]
            self.exact_convolution = DistributionOps(self.prepared.width, self.exact_ops)
            self.exact_tree = ProductTree(rows, self.prepared.shared_cases, self.exact_convolution)
        elif self.exact_dirty:
            self.exact_tree.replace({i: local_distributions(self.prepared, i, self.states[i], self.exact_ops)
                                     for i in self.exact_dirty})
        self.exact_dirty.clear()
        numerator, total = self.totals(self.exact_tree.root, seed, target, self.exact_ops)
        return None if not total else numerator / total

    def query(self, seed, target):
        if not 0 <= seed < 1 << self.prepared.width or not 0 <= target < self.prepared.width:
            raise Unsupported('query outside interface')
        numerator, total = self.totals(self.tree.root, seed, target, self.ops)
        if total.lo > 0:
            raw = self.ops.div(numerator, total)
            value = Interval(max(Decimal(0), raw.lo), min(Decimal(1), raw.hi))
            if self.ops.accurate(value):
                return Answer(value, None, self.ops.zero if value.hi == 0 else self.ops.one, False)
        self.fallbacks += 1
        value = self.rational(seed, target)
        if value is None:
            return Answer(None, None, None, True)
        return Answer(self.ops.from_fraction(value), value, self.ops.zero if value == 0 else self.ops.one, True)
