from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from mm2_atoms import Expr, Symbol, parse_atoms, render
from protocol import decode_string, nat_atom, observe_result, string_atom, validate_passive_data


def expr(tag, *args):
    return Expr((Symbol(tag),) + args)


def source_rows(owner="unit"):
    own = string_atom(owner)
    span = expr("mm-source-span", string_atom("unit.mm"), nat_atom(0), nat_atom(2))
    name = expr("mm-source-name", span, string_atom("w"))
    statement = expr("mm-source-const", span, expr("mm-cons", name, expr("mm-nil")), span)
    rows = [expr("mm-source-start", own),
            expr("mm-linked-row", string_atom("source-statement"), own, nat_atom(0), nat_atom(1), statement),
            expr("mm-source-end", own, nat_atom(1))]
    return rows, statement, own


class PassiveBoundaryTests(unittest.TestCase):
    def test_valid_initial_source_and_unicode_owner(self):
        rows, _, _ = source_rows("oruži")
        self.assertEqual(validate_passive_data(rows, owner="oruži").end, 1)
        self.assertEqual(decode_string(string_atom("oruži")), "oruži")

    def test_raw_variables_and_nested_code_are_rejected(self):
        rows, _, own = source_rows()
        for payload in (Symbol("$x"), expr("exec", Symbol("x")),
                        expr("mm-internal-future-carrier", Symbol("x")),
                        expr("mm-source-theorem-admitted", Symbol("x")),
                        expr("mm-body-prefix", Symbol("x")),
                        expr("mm-compressed-owned-runtime-rule", Symbol("x"))):
            extra = expr("mm-linked-row", string_atom("source-action"), own, nat_atom(0), nat_atom(1),
                         expr("mm-source-action-add", payload))
            with self.subTest(payload=render(payload)), self.assertRaises(ValueError):
                validate_passive_data(rows + [extra], owner="unit")

    def test_top_level_header_and_control_cannot_preapprove(self):
        rows, _, own = source_rows()
        for extra in (expr("mm-assertion-header", own, nat_atom(0), string_atom("a"), nat_atom(0)),
                      expr("mm-normal-control", own, own, nat_atom(0), nat_atom(0)),
                      expr("mm-source-control", own, nat_atom(1))):
            with self.assertRaises(ValueError):
                validate_passive_data(rows + [extra], owner="unit")

    def test_prepared_control_and_assertion_publication_are_allowed(self):
        rows, _, own = source_rows()
        proof_owner = expr("mm-source-proof-owner", own, nat_atom(0))
        prepared = expr("mm-source-proof-control-prepared", own, proof_owner,
                        expr("mm-normal-control", own, proof_owner, nat_atom(0), nat_atom(0)))
        header = expr("mm-assertion-header", own, nat_atom(0), string_atom("a"), nat_atom(0))
        action = expr("mm-linked-row", string_atom("source-action"),
                      expr("mm-source-action-owner", own, nat_atom(0)), nat_atom(0), nat_atom(1),
                      expr("mm-source-action-add", header))
        self.assertEqual(validate_passive_data(rows + [prepared, action], owner="unit").end, 1)

    def test_owner_and_missing_statement_edges_are_rejected(self):
        rows, _, _ = source_rows()
        with self.assertRaisesRegex(ValueError, "owner mismatch"):
            validate_passive_data(rows, owner="other")
        with self.assertRaisesRegex(ValueError, "does not cover"):
            validate_passive_data([rows[0], rows[2]], owner="unit")


class OutcomeTests(unittest.TestCase):
    def setUp(self):
        rows, self.statement, self.owner = source_rows()
        self.source = validate_passive_data(rows, owner="unit")
        self.end = rows[2]
        self.applied = expr("mm-source-statement-applied", self.owner, nat_atom(0), self.statement)
        self.control = expr("mm-source-control", self.owner, nat_atom(1))

    def test_exact_completed_source_is_accepted(self):
        self.assertEqual(observe_result([self.end, self.applied, self.control], self.source)["outcome"], "accepted")

    def test_absence_and_incomplete_cursor_are_not_rejection(self):
        for rows in ([], [self.end], [self.end, self.control], [self.end, self.applied]):
            self.assertEqual(observe_result(rows, self.source)["outcome"], "execution-failure")

    def test_payload_owner_and_position_forgery_do_not_accept(self):
        changed = expr("mm-source-statement-applied", self.owner, nat_atom(0), Symbol("not-the-original"))
        other_control = expr("mm-source-control", string_atom("other"), nat_atom(1))
        false_admission = expr("mm-source-theorem-admitted", self.owner, nat_atom(0), self.statement, Symbol("occurrence"))
        for rows in ([self.end, changed, self.control], [self.end, self.applied, other_control],
                     [self.end, self.applied, self.control, false_admission]):
            self.assertEqual(observe_result(rows, self.source)["outcome"], "execution-failure")

    def test_explicit_statement_rejection_has_exact_source_binding(self):
        rejection = expr("mm-source-statement-rejected", self.owner, nat_atom(0), self.statement,
                         Symbol("duplicate-constant-name"), Symbol("name"))
        result = observe_result([self.end, rejection], self.source)
        self.assertEqual(result["outcome"], "rejected")
        self.assertEqual(result["detail"], "duplicate-constant-name")
        self.assertEqual(observe_result([self.end, rejection, self.control], self.source)["outcome"], "execution-failure")

    def test_incomplete_marker_without_completion_is_failure(self):
        marker = expr("mm-compressed-proof-incomplete", self.owner, self.owner, nat_atom(0), Symbol("occurrence"))
        self.assertEqual(observe_result([self.end, marker], self.source)["outcome"], "execution-failure")
        self.assertEqual(observe_result([self.end, self.applied, self.control, marker], self.source)["outcome"], "execution-failure")

    def test_incomplete_is_bound_to_its_theorem_not_prior_admissions(self):
        from protocol import SourceData
        first = expr("mm-source-theorem", *(Symbol("earlier") for _ in range(7)))
        second = expr("mm-source-theorem", *(Symbol("unknown") for _ in range(7)))
        source = SourceData(self.owner, "unit", 2, {0: first, 1: second})
        proof_owner = expr("mm-source-proof-owner", self.owner, nat_atom(1))
        marker = expr("mm-compressed-proof-incomplete", self.owner, proof_owner, nat_atom(0), Symbol("occurrence"))
        prior_admission = expr("mm-source-theorem-admitted", self.owner, nat_atom(0), first, Symbol("prior-proof"))
        complete = [expr("mm-source-end", self.owner, nat_atom(2)),
                    expr("mm-source-control", self.owner, nat_atom(2)),
                    expr("mm-source-statement-applied", self.owner, nat_atom(0), first),
                    expr("mm-source-statement-applied", self.owner, nat_atom(1), second), prior_admission, marker]
        observed = observe_result(complete, source)
        self.assertEqual(observed["outcome"], "incomplete-proof")
        self.assertEqual(observed["incomplete_positions"], [1])
        current_admission = expr("mm-source-theorem-admitted", self.owner, nat_atom(1), second, Symbol("unknown-proof"))
        self.assertEqual(observe_result(complete + [current_admission], source)["outcome"], "execution-failure")


if __name__ == '__main__':
    unittest.main()
