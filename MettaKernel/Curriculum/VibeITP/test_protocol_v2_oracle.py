"""Controls for the external oracle's outcome and challenge-count observations."""
import unittest

from check_protocol_v2 import matches_result


def expected(outcome, setup, proof, remaining):
    return {'expected': outcome, 'diagnostic': None,
            'challenges': {'setup': setup, 'proof': proof, 'remaining': remaining}}


class OutcomeControls(unittest.TestCase):
    def test_complete_duplicates(self):
        self.assertTrue(matches_result(expected('success', 1, 2, 0), 0,
                                       'Success! All 3 challenges proved! :-)\n'))

    def test_wrong_total_is_refused(self):
        self.assertFalse(matches_result(expected('success', 1, 2, 0), 0,
                                        'Success! All 1 challenges proved! :-)\n'))

    def test_partial_counts(self):
        entry = expected('incomplete', 1, 2, 2)
        self.assertTrue(matches_result(entry, 0, 'Remaining unproven challenges. Proved 1 / 3 challenges.\n'))
        self.assertFalse(matches_result(entry, 0, 'Remaining unproven challenges. Proved 2 / 3 challenges.\n'))
        self.assertFalse(matches_result(entry, 0, 'Success! All 3 challenges proved! :-)\n'))

    def test_empty_run_has_no_success_credit(self):
        output = 'Successfully processed axioms, definitions & proofs.\n'
        self.assertTrue(matches_result(expected('incomplete', 0, 0, 0), 0, output))
        self.assertFalse(matches_result(expected('success', 0, 0, 0), 0, output))
        self.assertFalse(matches_result(expected('incomplete', 0, 0, 0), 0, ''))

    def test_zero_exit_does_not_prove_completion(self):
        self.assertFalse(matches_result(expected('success', 1, 0, 0), 0, ''))

    def test_faults_and_conflicting_summaries(self):
        entry = expected('success', 1, 0, 0)
        good = 'Success! All 1 challenges proved! :-)\n'
        for output in [good + 'runtime error: invalid access', good + good,
                       good + 'Remaining unproven challenges. Proved 0 / 1 challenges.\n']:
            self.assertFalse(matches_result(entry, 0, output))
        self.assertFalse(matches_result(entry, -9, good))

    def test_refusal_needs_its_diagnostic(self):
        entry = {'expected': 'refused', 'diagnostic': 'theorem derivation failed'}
        self.assertTrue(matches_result(entry, 1, 'theorem derivation failed'))
        self.assertFalse(matches_result(entry, 1, 'different error'))
        self.assertFalse(matches_result(entry, 0, 'theorem derivation failed'))

    def test_invalid_declared_counts(self):
        with self.assertRaises(ValueError):
            matches_result(expected('incomplete', 1, 0, 2), 0, '')
        with self.assertRaises(ValueError):
            matches_result(expected('success', -1, 0, 0), 0, '')


if __name__ == '__main__':
    unittest.main()
