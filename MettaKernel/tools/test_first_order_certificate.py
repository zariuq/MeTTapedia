#!/usr/bin/env python3
"""Controls for the untrusted producer's binding and completion accounting."""

import unittest

from first_order_certificate import Search, Variable, parse_pattern, unify


def app(name, *arguments):
    return [name, list(arguments)]


def var(name):
    return {"var": name}


def rule(name, variables, premises, conclusion):
    return dict(id=name, vars=variables, premises=premises, conclusion=conclusion)


class ProducerControls(unittest.TestCase):
    def setUp(self):
        self.a, self.b = app("a"), app("b")
        self.rules = [
            rule("join", ["x", "middle", "z"],
                 [app("edge", var("x"), var("middle")), app("edge", var("middle"), var("z"))],
                 app("path", var("x"), var("z"))),
            rule("ab", [], [], app("edge", self.a, self.b)),
            rule("ba", [], [], app("edge", self.b, self.a)),
        ]

    def test_premise_outputs_are_threaded(self):
        result = Search(self.rules, 100, 20).first(app("path", self.a, self.a))
        self.assertEqual(result["status"], "candidate")
        self.assertEqual(result["article"]["arguments"], [self.a, self.b, self.a])
        self.assertEqual([c["rule"] for c in result["article"]["children"]], ["ab", "ba"])

    def test_shared_holes_disagree(self):
        rules = [rule("same", ["x"], [], app("same", var("x"), var("x")))]
        self.assertEqual(Search(rules, 10, 5).first(app("same", self.a, self.b))["status"], "no-candidate")

    def test_occurs_check(self):
        x = Variable(0, "x")
        self.assertIsNone(unify(x, ("cycle", (x,)), {}))

    def test_failed_branch_leaves_inputs_unchanged(self):
        x = Variable(0, "x")
        before = {x: ("a", ())}
        self.assertIsNone(unify(x, ("b", ()), before))
        self.assertEqual(before, {x: ("a", ())})

    def test_rule_variables_are_fresh(self):
        rules = [rule("use-twice", [], [app("id", self.a), app("id", self.b)], app("ok")),
                 rule("id", ["x"], [], app("id", var("x")))]
        result = Search(rules, 10, 5).first(app("ok"))
        self.assertEqual(result["status"], "candidate")
        self.assertEqual([p["arguments"] for p in result["article"]["children"]], [[self.a], [self.b]])

    def test_budget_is_not_refusal(self):
        self.assertEqual(Search(self.rules, 0, 20).first(app("path", self.a, self.a))["status"], "budget-exhausted")

    def test_depth_is_not_refusal(self):
        self.assertEqual(Search(self.rules, 100, 0).first(app("path", self.a, self.a))["status"], "budget-exhausted")

    def test_invalid_seed_arity(self):
        with self.assertRaisesRegex(ValueError, "argument arity"):
            Search(self.rules, 100, 20).first(app("path", self.a, self.a),
                dict(rule="join", arguments=[], children=[None, None]))

    def test_undeclared_variable(self):
        with self.assertRaises(KeyError):
            parse_pattern(var("missing"), {})

    def test_rule_identity_collision(self):
        with self.assertRaisesRegex(ValueError, "duplicate rule identifier"):
            Search(self.rules + self.rules, 10, 10)

    def test_unused_variable_does_not_become_ground(self):
        rules = [rule("underdetermined", ["x"], [], app("ok"))]
        self.assertEqual(Search(rules, 10, 5).first(app("ok"))["status"], "no-candidate")


if __name__ == "__main__":
    unittest.main()
