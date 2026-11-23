"""The optional offline gate compares data sets, but pins ordered A forms."""

from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from check_reference import compare
from mm2_atoms import parse_atoms


class ReferenceTests(unittest.TestCase):
    def fixture(self, **texts):
        directory = Path(tempfile.mkdtemp(prefix="mm2-reference-test-"))
        paths = {}
        for name, text in texts.items():
            paths[name] = directory / (name + ".mm2")
            paths[name].write_text(text)
        return paths

    def test_data_order_and_set_duplicates_are_not_execution_order(self):
        paths = self.fixture(native="(b 2) (a 1) (a 1)", reference="(a 1) (b 2)")
        self.assertTrue(compare(**paths)["equal"])

    def test_occurrence_index_change_is_detected(self):
        paths = self.fixture(native="(proof-label 1 ax)", reference="(proof-label 0 ax)")
        report = compare(**paths)
        self.assertFalse(report["equal"])
        self.assertEqual(len(report["missing"]), 1)
        self.assertEqual(len(report["unexpected"]), 1)

    def test_combined_program_requires_exact_prefix(self):
        paths = self.fixture(native="(a 1)", reference="(fixed rule) (a 1)")
        prefix = tuple(parse_atoms("(fixed rule)"))
        self.assertTrue(compare(**paths, verifier_prefix=prefix)["equal"])
        with self.assertRaisesRegex(ValueError, "pinned verifier"):
            compare(**paths, verifier_prefix=tuple(parse_atoms("(other rule)")))


if __name__ == "__main__":
    unittest.main()
