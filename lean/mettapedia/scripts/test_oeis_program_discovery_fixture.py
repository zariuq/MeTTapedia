from __future__ import annotations

import importlib.util
import json
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MODULE_PATH = ROOT / "scripts" / "oeis_program_discovery_fixture.py"
FIXTURE_PATH = (
    ROOT
    / "Mettapedia"
    / "MachineLearning"
    / "SearchGuidance"
    / "ProgramDiscovery"
    / "fixtures"
    / "oeis_program_discovery_v1.json"
)

SPEC = importlib.util.spec_from_file_location("oeis_program_discovery_fixture", MODULE_PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ProgramDiscoveryFixtureTests(unittest.TestCase):
    def test_shared_fixture_recomputes_all_invariants(self) -> None:
        value = json.loads(FIXTURE_PATH.read_text(encoding="utf-8"))
        MODULE.validate_fixture(value)

    def test_shared_fixture_is_canonical_json(self) -> None:
        value = json.loads(FIXTURE_PATH.read_text(encoding="utf-8"))
        self.assertEqual(FIXTURE_PATH.read_text(encoding="utf-8"), MODULE.canonical_json(value))


if __name__ == "__main__":
    unittest.main()
