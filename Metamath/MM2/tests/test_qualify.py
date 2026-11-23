"""Qualification never hides absent cases or turns process limits into verdicts."""

import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from assemble import load_verifier
from qualify import registered, snapshot_verifier, suite_verdict


class QualificationTests(unittest.TestCase):
    def fixture(self, entries, files):
        root = Path(tempfile.mkdtemp(prefix="mm2-suite-test-"))
        (root / "reference").mkdir()
        (root / "reference/reference.txt").write_text(entries)
        for name in files:
            path = root / "tests" / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("$c wff $.")
        return root

    def test_cases_are_explicit_including_incomplete(self):
        root = self.fixture("ACCEPT unit/a.mm\nREJECT unit/b.mm # comment\n",
                            ["unit/a.mm", "unit/b.mm"])
        self.assertEqual([entry[0] for entry in registered(root)], ["ACCEPT", "REJECT"])
        self.assertEqual(suite_verdict("accepted"), "ACCEPT")
        self.assertEqual(suite_verdict("incomplete-proof"), "ACCEPT")
        self.assertEqual(suite_verdict("rejected"), "REJECT")
        self.assertIsNone(suite_verdict("execution-failure"))
        self.assertIsNone(suite_verdict("timeout"))

    def test_missing_duplicate_and_escaping_fixture_fail(self):
        for entries in ("ACCEPT unit/missing.mm\n",
                        "ACCEPT unit/a.mm\nACCEPT unit/a.mm\n",
                        "ACCEPT ../outside.mm\n", "ACCEPT /outside.mm\n"):
            with self.assertRaises(ValueError):
                registered(self.fixture(entries, ["unit/a.mm"]))

    def test_snapshot_has_exact_ordered_verifier_identity(self):
        original = load_verifier()
        directory = Path(tempfile.mkdtemp(prefix="mm2-snapshot-test-"))
        snapshot = snapshot_verifier(directory)
        frozen = load_verifier(snapshot)
        self.assertEqual(frozen.atoms, original.atoms)
        self.assertEqual(json.loads(snapshot.read_text())["fragments"][0]["file"], "verifier.mm2")


if __name__ == "__main__":
    unittest.main()
