"""Exact closure-response specification and an outward-rounded update prototype.

The mathematical laws are in Logic/RandomClosure.lean and
Logic/BDD/ClosureResponseCounting.lean. This runtime is independently tested;
the Lean results do not certify CPython or its decimal implementation.
"""

from __future__ import annotations

from dataclasses import dataclass
from decimal import Context, Decimal, ROUND_CEILING, ROUND_FLOOR
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
import math
from typing import Any, Iterable, Sequence


class Unsupported(ValueError):
    """Input does not satisfy the representation's structural contract."""


@dataclass(frozen=True, slots=True)
class Interval:
    lo: Decimal
    hi: Decimal

    def __post_init__(self):
        if self.lo.is_nan() or self.hi.is_nan() or self.lo > self.hi:
            raise ValueError("invalid interval")

    def contains(self, value: Fraction) -> bool:
        return Fraction(self.lo) <= value <= Fraction(self.hi)


class IntervalOps:
    def __init__(self, precision: int = 34):
        self.down = Context(prec=precision, rounding=ROUND_FLOOR)
        self.up = Context(prec=precision, rounding=ROUND_CEILING)
        self.zero = Interval(Decimal(0), Decimal(0))
        self.one = Interval(Decimal(1), Decimal(1))
        self.operations = 0

    def from_fraction(self, value: Fraction | int) -> Interval:
        value = Fraction(value)
        n, d = Decimal(value.numerator), Decimal(value.denominator)
        return Interval(self.down.divide(n, d), self.up.divide(n, d))

    def add(self, a: Interval, b: Interval) -> Interval:
        self.operations += 1
        return Interval(self.down.add(a.lo, b.lo), self.up.add(a.hi, b.hi))

    def neg(self, a: Interval) -> Interval:
        return Interval(a.hi.copy_negate(), a.lo.copy_negate())

    def sub(self, a: Interval, b: Interval) -> Interval:
        return self.add(a, self.neg(b))

    def mul(self, a: Interval, b: Interval) -> Interval:
        self.operations += 1
        if a.lo >= 0 and b.lo >= 0:
            return Interval(self.down.multiply(a.lo, b.lo), self.up.multiply(a.hi, b.hi))
        endpoints = [(x, y) for x in (a.lo, a.hi) for y in (b.lo, b.hi)]
        return Interval(min(self.down.multiply(x, y) for x, y in endpoints),
                        max(self.up.multiply(x, y) for x, y in endpoints))

    def div(self, a: Interval, b: Interval) -> Interval:
        if b.lo <= 0 <= b.hi:
            raise ZeroDivisionError("denominator enclosure contains zero")
        endpoints = [(x, y) for x in (a.lo, a.hi) for y in (b.lo, b.hi)]
        self.operations += 1
        return Interval(min(self.down.divide(x, y) for x, y in endpoints),
                        max(self.up.divide(x, y) for x, y in endpoints))

    @staticmethod
    def abs(a: Interval) -> Interval:
        if a.lo >= 0:
            return a
        if a.hi <= 0:
            return Interval(a.hi.copy_negate(), a.lo.copy_negate())
        return Interval(Decimal(0), max(a.lo.copy_abs(), a.hi.copy_abs()))

    def accurate(self, a: Interval) -> bool:
        width = self.up.subtract(a.hi, a.lo)
        if width > Decimal("1e-12"):
            return False
        if a.lo == a.hi == 0:
            return True
        return a.lo > 0 and width <= self.down.multiply(Decimal("1e-10"), a.lo)


class RationalOps:
    zero, one = Fraction(0), Fraction(1)

    def __init__(self):
        self.operations = 0

    @staticmethod
    def from_fraction(value):
        return Fraction(value)

    def add(self, a, b):
        self.operations += 1
        return a + b

    def mul(self, a, b):
        self.operations += 1
        return a * b

    def sub(self, a, b):
        return self.add(a, -b)

    def div(self, a, b):
        self.operations += 1
        return a / b

    abs = staticmethod(abs)


@dataclass(frozen=True)
class Rule:
    head: str
    body: tuple[str, ...] = ()


@dataclass(frozen=True)
class Component:
    name: str
    choices: tuple[str, ...]
    private: tuple[str, ...]
    rules: tuple[Rule, ...]


@dataclass(frozen=True)
class Program:
    boundary: tuple[str, ...]
    components: tuple[Component, ...]
    shared: tuple[str, ...] = ()

    def validate(self):
        common = set(self.boundary) | set(self.shared)
        if len(common) != len(self.boundary) + len(self.shared):
            raise Unsupported("duplicate interface/shared names")
        owned = set(common)
        names = set()
        for component in self.components:
            if component.name in names:
                raise Unsupported("duplicate component identity")
            names.add(component.name)
            local_names = component.choices + component.private
            if len(set(local_names)) != len(local_names) or owned.intersection(local_names):
                raise Unsupported("shared choices or private atoms require explicit ownership")
            owned.update(local_names)
            scope = common | set(local_names)
            choice_names = set(component.choices) | set(self.shared)
            for rule in component.rules:
                if rule.head not in scope or any(atom not in scope for atom in rule.body):
                    raise Unsupported("rule reads or derives outside its declared scope")
                if rule.head in choice_names:
                    raise Unsupported("base choices must not be derived by rules")


def close(rules: Sequence[tuple[int, int]], initial: int) -> int:
    current = initial
    while True:
        before = current
        for body, head in rules:
            if body & current == body:
                current |= head
        if current == before:
            return current


@lru_cache(maxsize=None)
def intersection_hull(family: int, width: int) -> int:
    members = {i for i in range(1 << width) if family >> i & 1}
    members.add((1 << width) - 1)
    while True:
        extra = {a & b for a in members for b in members}
        if extra <= members:
            return sum(1 << i for i in members)
        members.update(extra)


def query_coefficients(width: int, seed: int, query: int) -> dict[int, int]:
    if not 0 <= seed < 1 << width or not 0 <= query < width:
        raise Unsupported("query outside interface")
    avoiding = [t for t in range(1 << width) if seed & t == seed and not (t >> query & 1)]
    coefficients: dict[int, int] = {}
    for selected in range(1 << len(avoiding)):
        family = sum(1 << t for j, t in enumerate(avoiding) if selected >> j & 1)
        key = intersection_hull(family, width)
        coefficients[key] = coefficients.get(key, 0) + (-1 if selected.bit_count() % 2 else 1)
    return {key: value for key, value in coefficients.items() if value}


@lru_cache(maxsize=None)
def response_profiles(width: int, choices: int, shared: int, atom_count: int,
                      rules: tuple[tuple[int, int], ...]) -> tuple[tuple[int, ...], ...]:
    """Each entry is the fixed-point family of one actual local rule closure."""
    del atom_count  # retained in the cache key to distinguish source signatures
    boundary_mask = (1 << width) - 1
    profiles = []
    for h in range(1 << shared):
        cases = []
        for world in range(1 << choices):
            fixed = 0
            base = (world << width) | (h << (width + choices))
            for seed in range(1 << width):
                if close(rules, base | seed) & boundary_mask == seed:
                    fixed |= 1 << seed
            cases.append(fixed)
        profiles.append(tuple(cases))
    return tuple(profiles)


class Prepared:
    def __init__(self, program: Program, queries: Sequence[tuple[int, int]]):
        program.validate()
        self.width = len(program.boundary)
        self.choice_keys = tuple(component.choices for component in program.components)
        self.component_names = tuple(component.name for component in program.components)
        self.shared_keys = program.shared
        self.shared_cases = 1 << len(program.shared)
        self.coefficients = {key: query_coefficients(self.width, *key) for key in queries}
        empty = intersection_hull(0, self.width)
        self.families = tuple(sorted({empty} | {f for values in self.coefficients.values() for f in values}))
        self.normalizer = self.families.index(empty)
        self.coefficients = {key: tuple((self.families.index(f), coefficient) for f, coefficient in values.items())
                             for key, values in self.coefficients.items()}
        self.acceptance = []
        self.profiles = []
        for component in program.components:
            atoms = program.boundary + component.choices + program.shared + component.private
            indices = {atom: i for i, atom in enumerate(atoms)}
            rules = tuple((sum(1 << i for i in {indices[a] for a in rule.body}), 1 << indices[rule.head])
                          for rule in component.rules)
            profile = response_profiles(self.width, len(component.choices), len(program.shared), len(atoms), rules)
            self.profiles.append(profile)
            self.acceptance.append(acceptance_table(profile, self.families))


@lru_cache(maxsize=None)
def acceptance_table(profiles, families):
    return tuple(tuple(world for world, fixed in enumerate(profile) if family & fixed == family)
                 for profile in profiles for family in families)


@dataclass(frozen=True)
class LocalState:
    probabilities: tuple[Fraction, ...]
    evidence: tuple[bool | None, ...]

    def __post_init__(self):
        if len(self.evidence) != len(self.probabilities) or any(
                not isinstance(p, Fraction) or p < 0 or p > 1 for p in self.probabilities):
            raise Unsupported("invalid exact probability vector")
        if any(e is not None and type(e) is not bool for e in self.evidence):
            raise Unsupported("invalid evidence vector")

    @classmethod
    def make(cls, probabilities: Iterable[Fraction], evidence=None):
        ps = tuple(Fraction(p) for p in probabilities)
        es = tuple(evidence) if evidence is not None else (None,) * len(ps)
        if len(es) != len(ps) or any(p < 0 or p > 1 for p in ps):
            raise Unsupported("invalid probability/evidence vector")
        if any(e is not None and type(e) is not bool for e in es):
            raise Unsupported("evidence must be true, false or absent")
        return cls(ps, es)


def world_weights(state: LocalState, ops) -> tuple[Any, ...]:
    probabilities = tuple(ops.from_fraction(p) for p in state.probabilities)
    complements = tuple(ops.sub(ops.one, p) for p in probabilities)
    result = [ops.one]
    for i, p in enumerate(probabilities):
        absent = ([ops.zero] * len(result) if state.evidence[i] is True else
                  [ops.mul(value, complements[i]) for value in result])
        present = ([ops.zero] * len(result) if state.evidence[i] is False else
                   [ops.mul(value, p) for value in result])
        result = absent + present
    return tuple(result)


def local_rows(prepared: Prepared, index: int, state: LocalState, ops) -> tuple[Any, ...]:
    if len(state.probabilities) != len(prepared.choice_keys[index]):
        raise Unsupported("component choice count mismatch")
    weights = world_weights(state, ops)
    total = ops.one
    for p, evidence in zip(state.probabilities, state.evidence):
        if evidence is not None:
            total = ops.mul(total, ops.from_fraction(p if evidence else 1 - p))
    rows = []
    for selected in prepared.acceptance[index]:
        if len(selected) == len(weights):
            rows.append(total)
        else:
            value = ops.zero
            for world in selected:
                value = ops.add(value, weights[world])
            rows.append(value)
    return tuple(rows)


class ProductTree:
    """Cached pointwise products; replacement uses no division."""
    def __init__(self, rows: Sequence[tuple[Any, ...]], columns: int, ops):
        self.ops, self.columns, self.count = ops, columns, len(rows)
        self.size = 1 << max(0, (len(rows) - 1).bit_length()) if rows else 1
        identity = (ops.one,) * columns
        self.values = [identity for _ in range(self.size * 2)]
        self.visits = 0
        for i, row in enumerate(rows):
            if len(row) != columns:
                raise ValueError("row width mismatch")
            self.values[self.size + i] = row
        for i in range(self.size - 1, 0, -1):
            self._recompute(i)

    def _recompute(self, index: int):
        self.values[index] = tuple(self.ops.mul(a, b) for a, b in zip(self.values[index * 2], self.values[index * 2 + 1]))
        self.visits += 1

    def replace(self, updates: dict[int, tuple[Any, ...]]):
        if any(not 0 <= index < self.count or len(row) != self.columns for index, row in updates.items()):
            raise IndexError("invalid product-tree update")
        dirty = set()
        for index, row in updates.items():
            cursor = self.size + index
            self.values[cursor] = row
            while cursor > 1:
                cursor //= 2
                dirty.add(cursor)
        for cursor in sorted(dirty, reverse=True):
            self._recompute(cursor)

    @property
    def root(self):
        return self.values[1]


@dataclass(frozen=True)
class Answer:
    enclosure: Interval | None
    exact: Fraction | None
    cancellation: Interval | None
    fallback: bool


class Engine:
    def __init__(self, prepared: Prepared, states: Sequence[LocalState], shared: LocalState | None = None,
                 precision: int = 34):
        if len(states) != len(prepared.choice_keys):
            raise Unsupported("component state count mismatch")
        self.prepared, self.states = prepared, list(states)
        self.shared = shared or LocalState.make([Fraction(1, 2)] * len(prepared.shared_keys))
        if len(self.shared.probabilities) != len(prepared.shared_keys):
            raise Unsupported("shared choice count mismatch")
        self.ops = IntervalOps(precision)
        columns = len(prepared.families) * prepared.shared_cases
        self.tree = ProductTree([local_rows(prepared, i, state, self.ops) for i, state in enumerate(states)], columns, self.ops)
        self.exact_ops = RationalOps()
        self.exact_tree: ProductTree | None = None
        self.exact_dirty = set()
        self.fallbacks = 0

    def update(self, changed: dict[int, LocalState], shared: LocalState | None = None):
        if any(not 0 <= i < len(self.states) for i in changed):
            raise Unsupported("unknown component update")
        if shared is not None and len(shared.probabilities) != len(self.prepared.shared_keys):
            raise Unsupported("shared choice count mismatch")
        rows = {i: local_rows(self.prepared, i, state, self.ops) for i, state in changed.items()}
        self.tree.replace(rows)
        for i, state in changed.items():
            self.states[i] = state
            self.exact_dirty.add(i)
        if shared is not None:
            self.shared = shared

    def _mixture(self, root, ops):
        if self.prepared.shared_cases == 1:
            return root
        weights = world_weights(self.shared, ops)
        width = len(self.prepared.families)
        result = []
        for column in range(width):
            value = ops.zero
            for h, weight in enumerate(weights):
                value = ops.add(value, ops.mul(weight, root[h * width + column]))
            result.append(value)
        return result

    def _extract(self, rows, key, ops):
        if key not in self.prepared.coefficients:
            raise Unsupported("query was not declared during preparation")
        numerator = ops.zero
        amplitude = ops.zero
        for index, coefficient in self.prepared.coefficients[key]:
            term = ops.mul(ops.from_fraction(coefficient), rows[index])
            numerator = ops.add(numerator, term)
            amplitude = ops.add(amplitude, ops.abs(term))
        return numerator, rows[self.prepared.normalizer], amplitude

    def rational(self, key):
        if self.exact_tree is None:
            rows = [local_rows(self.prepared, i, state, self.exact_ops) for i, state in enumerate(self.states)]
            self.exact_tree = ProductTree(rows, self.tree.columns, self.exact_ops)
        elif self.exact_dirty:
            self.exact_tree.replace({i: local_rows(self.prepared, i, self.states[i], self.exact_ops)
                                     for i in self.exact_dirty})
        self.exact_dirty.clear()
        numerator, denominator, amplitude = self._extract(self._mixture(self.exact_tree.root, self.exact_ops), key, self.exact_ops)
        if denominator == 0:
            return None, None
        value = numerator / denominator
        if not 0 <= value <= 1:
            raise AssertionError("exact extraction escaped probability bounds")
        cancellation = amplitude / abs(numerator) if numerator else (Fraction(0) if not amplitude else math.inf)
        return value, cancellation

    def query(self, seed: int, target: int) -> Answer:
        key = (seed, target)
        numerator, denominator, amplitude = self._extract(self._mixture(self.tree.root, self.ops), key, self.ops)
        if denominator.lo > 0:
            raw = self.ops.div(numerator, denominator)
            if raw.hi < 0 or raw.lo > 1:
                raise AssertionError("interval excludes all probabilities")
            value = Interval(max(Decimal(0), raw.lo), min(Decimal(1), raw.hi))
            if self.ops.accurate(value):
                absolute = self.ops.abs(numerator)
                if absolute.lo > 0:
                    cancellation = self.ops.div(amplitude, absolute)
                elif amplitude.hi == 0:
                    cancellation = self.ops.zero
                else:
                    cancellation = Interval(Decimal(0), Decimal("Infinity"))
                return Answer(value, None, cancellation, False)
        self.fallbacks += 1
        value, cancellation = self.rational(key)
        if value is None:
            return Answer(None, None, None, True)
        ratio = Interval(Decimal("Infinity"), Decimal("Infinity")) if cancellation == math.inf else self.ops.from_fraction(cancellation)
        return Answer(self.ops.from_fraction(value), value, ratio, True)


def enumerate_probability(program: Program, states: Sequence[LocalState], seed: int, target: int,
                          shared: LocalState | None = None) -> Fraction | None:
    """Independent small-instance oracle: enumerate worlds, then close all rules."""
    program.validate()
    shared = shared or LocalState.make([Fraction(1, 2)] * len(program.shared))
    names = list(program.boundary) + list(program.shared)
    for component in program.components:
        names.extend(component.choices + component.private)
    indices = {name: i for i, name in enumerate(names)}
    rules = [(sum(1 << i for i in {indices[a] for a in rule.body}), 1 << indices[rule.head])
             for component in program.components for rule in component.rules]
    chance_names = list(program.shared) + [a for component in program.components for a in component.choices]
    probabilities = shared.probabilities + tuple(p for state in states for p in state.probabilities)
    evidence = shared.evidence + tuple(e for state in states for e in state.evidence)
    if len(chance_names) != len(probabilities):
        raise Unsupported("oracle choice count mismatch")
    total = answer = Fraction(0)
    for world in range(1 << len(chance_names)):
        mass = Fraction(1)
        initial = seed
        for j, name in enumerate(chance_names):
            bit = bool(world >> j & 1)
            if evidence[j] is not None and evidence[j] != bit:
                mass = 0
                break
            mass *= probabilities[j] if bit else 1 - probabilities[j]
            if bit:
                initial |= 1 << indices[name]
        total += mass
        if mass and close(rules, initial) >> target & 1:
            answer += mass
    return answer / total if total else None
