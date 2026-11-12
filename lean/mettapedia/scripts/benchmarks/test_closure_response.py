"""Independent rational and adversarial checks for closure-response updates."""
from fractions import Fraction as F
import itertools
import random
import unittest
from closure_response_ablations import DirectEngine, DirectPrepared

from closure_response import (
    Answer, Component, Engine, IntervalOps, LocalState, Prepared, ProductTree,
    Program, RationalOps, Rule, Unsupported, close, enumerate_probability,
    intersection_hull, query_coefficients,
)


class ClosureResponseTests(unittest.TestCase):
    def assert_answer(self, program, states, key, shared=None):
        engine = Engine(Prepared(program, [key]), states, shared)
        truth = enumerate_probability(program, states, *key, shared)
        result = engine.query(*key)
        self.assertEqual(engine.rational(key)[0], truth)
        direct = DirectEngine(DirectPrepared(program), states, shared)
        self.assertEqual(direct.rational(*key), truth)
        direct_result = direct.query(*key)
        self.assertTrue(direct_result.enclosure is None if truth is None else direct_result.enclosure.contains(truth))
        if truth is None:
            self.assertIsNone(result.enclosure)
        else:
            self.assertTrue(result.enclosure.contains(truth), (truth, result))
            self.assertTrue(result.exact == truth or engine.ops.accurate(result.enclosure))
        return engine, result

    @staticmethod
    def chain(shared=False):
        if shared:
            a = Component('a', (), (), (Rule('b', ('a', 'z')),))
            b = Component('b', (), (), (Rule('c', ('b', 'z')),))
            return Program(('a', 'b', 'c'), (a, b), ('z',)), [LocalState.make([])] * 2
        a = Component('a', ('x',), (), (Rule('b', ('a', 'x')),))
        b = Component('b', ('y',), (), (Rule('c', ('b', 'y')),))
        return Program(('a', 'b', 'c'), (a, b)), [LocalState.make([F(1, 2)])] * 2

    def test_independent_and_shared_choices(self):
        program, states = self.chain()
        engine, _ = self.assert_answer(program, states, (1, 2))
        self.assertEqual(engine.rational((1, 2))[0], F(1, 4))
        program, states = self.chain(shared=True)
        engine, _ = self.assert_answer(program, states, (1, 2), LocalState.make([F(1, 2)]))
        self.assertEqual(engine.rational((1, 2))[0], F(1, 2))

    def test_shared_choice_reweighting_and_evidence(self):
        program, states = self.chain(shared=True)
        for prepared, constructor in [(Prepared(program, [(1, 2)]), Engine), (DirectPrepared(program), DirectEngine)]:
            engine = constructor(prepared, states, LocalState.make([F(1, 2)]))
            for p, evidence, expected in [(F(3, 4), None, F(3, 4)), (F(1, 3), True, F(1)),
                                           (F(2, 3), False, F(0)), (F(0), True, None)]:
                engine.update({}, LocalState.make([p], [evidence]))
                result = engine.query(1, 2)
                self.assertTrue(result.enclosure is None if expected is None else result.enclosure.contains(expected))

    def test_undeclared_queries_are_rejected(self):
        program, states = self.chain()
        engine = Engine(Prepared(program, [(1, 2)]), states)
        with self.assertRaises(Unsupported):
            engine.query(0, 2)

    def test_feedback_needs_more_than_one_pass(self):
        left = Component('l', (), (), (Rule('c', ('b',)),))
        right = Component('r', (), (), (Rule('b', ('a',)),))
        program = Program(('a', 'b', 'c'), (left, right))
        engine, _ = self.assert_answer(program, [LocalState.make([])] * 2, (1, 2))
        self.assertEqual(engine.rational((1, 2))[0], 1)
        self.assertEqual(close([(2, 4)], 1), 1)
        self.assertEqual(close([(1, 2)], close([(2, 4)], 1)), 3)

    def test_empty_seed_is_not_a_response_summary(self):
        component = Component('c', (), (), (Rule('b', ('a',)),))
        program = Program(('a', 'b'), (component,))
        engine = Engine(Prepared(program, [(0, 1), (1, 1)]), [LocalState.make([])])
        self.assertEqual(engine.rational((0, 1))[0], 0)
        self.assertEqual(engine.rational((1, 1))[0], 1)

    def test_self_loop_does_not_create_support(self):
        p = Program(('a',), (Component('c', (), (), (Rule('a', ('a',)),)),))
        engine, _ = self.assert_answer(p, [LocalState.make([])], (0, 0))
        self.assertEqual(engine.rational((0, 0))[0], 0)

    def test_private_atoms_are_not_interface_ports(self):
        a = Component('a', (), ('hidden',), (Rule('hidden', ('a',)),))
        b = Component('b', (), (), (Rule('b', ('hidden',)),))
        with self.assertRaises(Unsupported):
            Prepared(Program(('a', 'b'), (a, b)), [(1, 1)])

    def test_reused_choice_id_is_not_independence(self):
        a = Component('a', ('x',), (), (Rule('b', ('a', 'x')),))
        b = Component('b', ('x',), (), (Rule('c', ('b', 'x')),))
        with self.assertRaises(Unsupported):
            Prepared(Program(('a', 'b', 'c'), (a, b)), [(1, 2)])

    def test_no_rule_can_derive_a_base_choice(self):
        a = Component('a', ('x',), (), (Rule('x', ()),))
        with self.assertRaises(Unsupported):
            Prepared(Program(('a',), (a,)), [(0, 0)])

    def test_impossible_evidence_and_probability_zero_differ(self):
        program, states = self.chain()
        states[0] = LocalState.make([0], [True])
        engine, result = self.assert_answer(program, states, (1, 2))
        self.assertIsNone(result.enclosure)
        engine.update({0: LocalState.make([0])})
        self.assertEqual(engine.rational((1, 2))[0], 0)
        self.assertIsNotNone(engine.query(1, 2).enclosure)

    def test_zero_weights_and_replacements(self):
        program, states = self.chain()
        engine = Engine(Prepared(program, [(1, 2)]), states)
        for first, second in itertools.product([F(0), F(1, 3), F(1)], repeat=2):
            engine.update({0: LocalState.make([first]), 1: LocalState.make([second])})
            result = engine.query(1, 2)
            self.assertTrue(result.enclosure.contains(first * second))
            self.assertEqual(engine.rational((1, 2))[0], first * second)

    def test_invalid_update_is_atomic(self):
        program, states = self.chain()
        engine = Engine(Prepared(program, [(1, 2)]), states)
        before = engine.tree.root
        with self.assertRaises(Unsupported):
            engine.update({0: LocalState.make([1]), 2: LocalState.make([1])})
        self.assertEqual(engine.tree.root, before)
        with self.assertRaises(Unsupported):
            engine.update({0: LocalState.make([1])}, LocalState.make([F(1, 2)]))
        self.assertEqual(engine.tree.root, before)
        self.assertEqual(engine.rational((1, 2))[0], F(1, 4))

    def test_cancellation_falls_back_to_rationals(self):
        program, _ = self.chain()
        small = F(1, 10**50)
        states = [LocalState.make([small])] * 2
        engine, result = self.assert_answer(program, states, (1, 2))
        self.assertTrue(result.fallback)
        self.assertEqual(result.exact, small * small)
        self.assertGreater(engine.fallbacks, 0)
        self.assertGreater(result.cancellation.lo, 10**90)

    def test_interval_primitives_enclose_exact_values(self):
        ops = IntervalOps(precision=8)
        values = [F(n, d) for n in [-11, -1, 0, 1, 11] for d in [3, 7, 1000]]
        for a, b in itertools.product(values, repeat=2):
            x, y = ops.from_fraction(a), ops.from_fraction(b)
            self.assertTrue(ops.add(x, y).contains(a + b))
            self.assertTrue(ops.sub(x, y).contains(a - b))
            self.assertTrue(ops.mul(x, y).contains(a * b))
            if b:
                self.assertTrue(ops.div(x, y).contains(a / b))

    def test_empty_component_family_is_identity(self):
        program = Program(('a', 'b'), ())
        for key, expected in [((0, 0), 0), ((1, 0), 1), ((1, 1), 0)]:
            engine, _ = self.assert_answer(program, [], key)
            self.assertEqual(engine.rational(key)[0], expected)

    def test_family_hull_preserves_closed_observations(self):
        width = 3
        systems = [mask for mask in range(1 << (1 << width))
                   if intersection_hull(mask, width) == mask]
        self.assertEqual(len(systems), 61)
        for family in range(1 << (1 << width)):
            hull = intersection_hull(family, width)
            for system in systems:
                self.assertEqual(family & system == family, hull & system == hull)
        for first, second in itertools.product(systems, repeat=2):
            self.assertIn(first & second, systems)
            for seed in range(1 << width):
                for query in range(width):
                    coefficients = query_coefficients(width, seed, query)
                    actual = sum(c for f, c in coefficients.items() if f & (first & second) == f)
                    fixed = [t for t in range(1 << width) if (first & second) >> t & 1 and seed & t == seed]
                    closure = (1 << width) - 1
                    for t in fixed:
                        closure &= t
                    self.assertEqual(actual, int(bool(closure >> query & 1)))

    def test_random_programs_against_possible_worlds(self):
        rng = random.Random(517)
        for case in range(300):
            width = rng.randrange(1, 4)
            boundary = tuple(f'b{i}' for i in range(width))
            shared = ('h',) if rng.randrange(3) == 0 else ()
            modules, states = [], []
            for i in range(rng.randrange(1, 4)):
                choices = tuple(f'c{i}_{j}' for j in range(rng.randrange(3)))
                private = tuple(f'p{i}_{j}' for j in range(rng.randrange(3)))
                atoms = boundary + choices + private + shared
                rules = tuple(Rule(rng.choice(boundary + private), tuple(rng.sample(atoms, rng.randrange(min(3, len(atoms)) + 1))))
                              for _ in range(rng.randrange(1, 8)))
                modules.append(Component(f'm{i}', choices, private, rules))
                states.append(LocalState.make([rng.choice([F(0), F(1, 4), F(1, 2), F(3, 4), F(1)]) for _ in choices]))
            program = Program(boundary, tuple(modules), shared)
            shared_state = LocalState.make([F(1, 3)] * len(shared))
            key = rng.randrange(1 << width), rng.randrange(width)
            engine, _ = self.assert_answer(program, states, key, shared_state)
            index = rng.randrange(len(states))
            states[index] = LocalState.make([rng.choice([F(0), F(1, 3), F(1)]) for _ in states[index].probabilities],
                                           [rng.choice([None, None, False, True]) for _ in states[index].evidence])
            engine.update({index: states[index]})
            truth = enumerate_probability(program, states, *key, shared_state)
            self.assertEqual(engine.rational(key)[0], truth, case)
            result = engine.query(*key)
            self.assertTrue(result.enclosure is None if truth is None else result.enclosure.contains(truth), case)
            direct = DirectEngine(DirectPrepared(program), [LocalState.make([F(1, 2)] * len(m.choices)) for m in modules], shared_state)
            direct.update(dict(enumerate(states)))
            self.assertEqual(direct.rational(*key), truth, case)
            direct_result = direct.query(*key)
            self.assertTrue(direct_result.enclosure is None if truth is None else direct_result.enclosure.contains(truth), case)
            reversed_program = Program(boundary, tuple(Component(m.name, m.choices, m.private, tuple(reversed(m.rules)))
                                                        for m in reversed(modules)), shared)
            other = Engine(Prepared(reversed_program, [key]), list(reversed(states)), shared_state)
            self.assertEqual(other.rational(key)[0], truth, case)


if __name__ == '__main__':
    unittest.main()
