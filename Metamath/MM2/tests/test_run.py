from pathlib import Path
import sys
import subprocess
from unittest import mock
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from run import performed_steps, run_case
from mm2_atoms import render_atoms
from test_protocol import source_rows, expr
from protocol import nat_atom


class RunnerTests(unittest.TestCase):
    def test_step_count_is_unique_and_exact(self):
        self.assertEqual(performed_steps("loaded x\nexecuting 42 steps took 1 ms (writes 3)\n"), 42)
        self.assertIsNone(performed_steps("executing 1 steps took 0 ms\nexecuting 2 steps took 0 ms\n"))
        self.assertIsNone(performed_steps("no receipt"))

    def fake_run(self, steps_run, *, completed=True, exitcode=0):
        rows, statement, owner = source_rows()
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            data = base / "input.mm2"
            data.write_text(render_atoms(rows))

            def invoke(command, **kwargs):
                result_path = Path(command[-1])
                output = [rows[2]]
                if completed:
                    output += [expr("mm-source-statement-applied", owner, nat_atom(0), statement),
                               expr("mm-source-control", owner, nat_atom(1))]
                result_path.write_text(render_atoms(output))
                return mock.Mock(returncode=exitcode, stdout=f"executing {steps_run} steps took 1 ms\n", stderr="")

            with mock.patch("run.subprocess.run", side_effect=invoke):
                return run_case(data_path=data, mork=sys.executable, work_dir=base / "work", steps=20, owner="unit")

    def test_completed_native_receipt(self):
        result = self.fake_run(10)
        self.assertEqual(result["outcome"], "accepted")
        self.assertEqual(result["steps_ifparsed"], 10)

    def test_budget_missing_terminal_and_process_failure_do_not_reject(self):
        for result in (self.fake_run(20), self.fake_run(10, completed=False), self.fake_run(10, exitcode=1)):
            self.assertEqual(result["outcome"], "execution-failure")

    def test_bad_input_combination_fails_before_tools(self):
        result = run_case(mork=sys.executable, work_dir="unused")
        self.assertEqual(result["outcome"], "execution-failure")

    def test_timeout_keeps_partial_logs_and_names_phase(self):
        rows, _, _ = source_rows()
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            data = base / "input.mm2"
            data.write_text(render_atoms(rows))
            failure = subprocess.TimeoutExpired("mork", 1, output=b"partial\xff output", stderr=b"diagnostic")
            with mock.patch("run.subprocess.run", side_effect=failure):
                result = run_case(data_path=data, mork=sys.executable, work_dir=base / "work",
                                  steps=20, timeout=1, owner="unit")
            self.assertEqual(result["outcome"], "execution-failure")
            self.assertEqual(result["timeout_phase"], "MORK")
            self.assertIn("MORK exceeded", result["detail"])
            self.assertEqual(Path(result["artifacts"]["mork.stdout"]).read_text(), "partial\ufffd output")
            self.assertEqual(Path(result["artifacts"]["mork.stderr"]).read_text(), "diagnostic")


if __name__ == '__main__':
    unittest.main()
