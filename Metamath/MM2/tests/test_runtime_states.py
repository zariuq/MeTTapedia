import contextlib
import io
import json
from pathlib import Path
import sys
import subprocess
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from assemble import load_verifier
from mm2_atoms import Expr, Symbol, head, parse_atoms, render, walk
from protocol import validate_passive_data
from test_runtime_state import STATE_MANIFEST, load_state, main


class InternalStateTests(unittest.TestCase):
    def test_missing_fresh_output_never_reuses_old_result(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            result = root / "old-result.mm2"
            result.write_text("old result must be preserved\n")
            reply = subprocess.CompletedProcess([], 0, "executing 1 steps took 0 ms\n", "")
            with patch("test_runtime_state.executable", return_value=Path("fake-mork")), \
                    patch("test_runtime_state.subprocess.run", return_value=reply), \
                    contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                code = main(["--case", "constant-duplicate", "--output", str(root / "program.mm2"),
                             "--result", str(result), "--mork", "fake-mork"])
            self.assertEqual(code, 2)
            self.assertEqual(result.read_text(), "old result must be preserved\n")
            self.assertEqual(len(list(root.glob("internal-state-run-*"))), 1)

    def test_all_eleven_fixed_continuations_match_canonical_a(self):
        assembly = load_verifier()
        cases = json.loads(STATE_MANIFEST.read_text())["cases"]
        self.assertEqual(len(cases), 11)
        for entry in cases:
            text, actual = load_state(entry["name"], assembly)
            self.assertEqual(actual, entry)
            with self.assertRaises(ValueError):
                validate_passive_data(parse_atoms(text))

    def test_floating_conflict_is_an_active_duplicate(self):
        text, _ = load_state("floating-conflict")
        atoms = parse_atoms(text)
        links = [atom for atom in atoms if head(atom) == "mm-source-active-hypothesis-link"]
        lookups = [atom for atom in atoms if head(atom) == "mm-hypothesis-lookup"]
        self.assertEqual(len(links), 1)
        self.assertEqual(links[0].items[-1], lookups[0])
        frontier = next(atom for atom in atoms if head(atom) == "mm-source-activity-frontier"
                        and head(atom.items[1]) == "mm-source-active-hypothesis-ledger")
        self.assertEqual(frontier.items[2], links[0].items[3])

    def test_added_error_rules_survive_normal_dispatch_reload(self):
        atoms = load_verifier().atoms
        for name in ("mm-normal-terminal-stack-fault", "mm-normal-empty-stack-fault",
                     "mm-normal-assertion-stack-underflow"):
            live = [atom for atom in atoms if head(atom) == "exec"
                    and atom.items[1].items[-1] == Symbol(name)]
            owned = [atom.items[1] for atom in atoms if head(atom) == "mm-internal-normal-dispatch-rule"
                     and atom.items[1].items[1].items[-1] == Symbol(name)]
            self.assertEqual(len(live), 1)
            self.assertEqual(live, owned)
            self.assertIn("mm-internal-compressed-source-theorem-fault-reject", render(live[0]))
        terminal = next(atom for atom in atoms if head(atom) == "exec"
                        and atom.items[1].items[-1] == Symbol("mm-normal-terminal-stack-fault"))
        proof = next(node for node in walk(terminal.items[2]) if head(node) == "mm-proof")
        self.assertEqual(proof.items[3], Symbol("normal"))

    def test_all_reloaded_floating_gates_match_live_definitions(self):
        atoms = load_verifier().atoms
        names = {"mm-source-floating-variable-active", "mm-source-floating-history-reuse",
                 "mm-source-floating-history-conflict", "mm-source-floating-history-fresh"}
        templates = {atom.items[1].items[-1].text: atom for atom in atoms
                     if head(atom) == "exec" and atom.items[1].items[-1].text in names}
        for atom in atoms:
            for node in walk(atom):
                if head(node) == "exec" and len(node.items) == 4 and isinstance(node.items[2], Expr):
                    name = node.items[1].items[-1].text
                    if name in names:
                        self.assertEqual(node, templates[name])
                        self.assertNotIn("mm-internal-source-variable-typecode-found", render(node.items[2]))
                        self.assertNotIn("mm-internal-source-variable-typecode-missing", render(node.items[2]))

    def test_active_floating_completion_reactivates_its_callbacks(self):
        atoms = load_verifier().atoms
        carrier = next(atom for atom in atoms if head(atom) == "mm-internal-source-floating-consumer-rules")
        self.assertEqual(len(carrier.items), 4)
        for name in ("mm-source-active-floating-hit", "mm-source-active-floating-missing"):
            producer = next(atom for atom in atoms if head(atom) == "exec"
                            and atom.items[1].items[-1] == Symbol(name))
            captures = [node for node in walk(producer.items[2])
                        if head(node) == "mm-internal-source-floating-consumer-rules"]
            self.assertEqual(len(captures), 1)
            for callback in captures[0].items[1:]:
                self.assertIn(Expr((Symbol("+"), callback)), producer.items[3].items[1:])

    def test_every_theorem_commit_copy_updates_its_assertion_counter(self):
        atoms = load_verifier().atoms
        live = next(atom for atom in atoms if head(atom) == "exec"
                    and atom.items[1].items[-1] == Symbol("mm-source-action-after-proof-finish"))
        environment = next(node for node in live.items[2].items if head(node) == "mm-source-environment")
        candidate = next(node for node in live.items[2].items if head(node) == "mm-source-assertion-candidate")
        self.assertEqual([head(node) for node in live.items[2].items[1:]], [
            "mm-source-assertion-candidate", "mm-source-environment", "mm-source-action-running",
            "mm-source-theorem-admission-pending", "mm-internal-source-verifier-reload"])
        self.assertFalse(any(head(node) == "+" and head(node.items[1]) == "exec"
                             for node in live.items[3].items))
        self.assertEqual(environment.items[4], candidate.items[5])
        self.assertIn(Expr((Symbol("-"), environment)), live.items[3].items)
        updated = next(node.items[1] for node in live.items[3].items
                       if head(node) == "+" and head(node.items[1]) == "mm-source-environment")
        self.assertEqual(updated.items[:4], environment.items[:4])
        self.assertEqual(updated.items[4], candidate.items[6])
        for atom in atoms:
            for node in walk(atom):
                if head(node) == "exec" and len(node.items) == 4 and isinstance(node.items[2], Expr) \
                        and node.items[1].items[-1] == Symbol("mm-source-action-after-proof-finish"):
                    self.assertEqual(node, live)

    def test_each_proof_start_reactivates_the_exact_one_shot_finish(self):
        atoms = load_verifier().atoms
        carrier = next(atom for atom in atoms if head(atom) == "mm-internal-source-theorem-finish-rule")
        live = next(atom for atom in atoms if head(atom) == "exec"
                    and atom.items[1].items[-1] == Symbol("mm-source-action-after-proof-finish"))
        self.assertEqual(carrier.items, (Symbol("mm-internal-source-theorem-finish-rule"), live))
        starts = [node for atom in atoms for node in walk(atom)
                  if head(node) == "exec" and len(node.items) == 4 and isinstance(node.items[2], Expr)
                  and node.items[1].items[-1] == Symbol("mm-source-action-after-proof-start")]
        self.assertGreater(len(starts), 1)
        for start in starts:
            captures = [node for node in start.items[2].items
                        if head(node) == "mm-internal-source-theorem-finish-rule"]
            self.assertEqual(len(captures), 1)
            self.assertIn(Expr((Symbol("+"), captures[0].items[1])), start.items[3].items)


if __name__ == "__main__":
    unittest.main()
