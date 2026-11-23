import json
import os
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory
import unittest


TOOLS = Path(__file__).resolve().parent


class SnapshotRecheckTest(unittest.TestCase):
    def test_rebuilt_chain_uses_frozen_siblings_and_blocks_dependents(self):
        prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
        lean = prefix / "bin" / "lean"
        with TemporaryDirectory(prefix="lean-snapshot-") as temporary:
            root = Path(temporary)
            live = root / "live"
            (root / "Batch").mkdir()
            (live / "Batch").mkdir(parents=True)
            env = {**os.environ, "LEAN_SYSROOT": str(prefix), "LEAN_PATH": str(live),
                   "PATH": str(lean.parent) + os.pathsep + os.environ["PATH"]}

            def run(*args, expected=0):
                result = subprocess.run(args, cwd=root, env=env, text=True, capture_output=True)
                self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
                return result

            def write_source(name, body):
                path = Path("Batch") / f"{name}.lean"
                (root / path).write_text("module\n" + body)
                return path

            def publish(name):
                run(lean, "-o", live / "Batch" / f"{name}.olean", f"Batch/{name}.lean")

            def reading(value):
                return write_source("Provider", f"@[expose] public def reading : Nat := {value}\n")

            provider = reading("1")
            publish("Provider")
            bridge = write_source("Bridge",
                "public import Batch.Provider\n@[expose] public def doubled := reading * 2\n")
            publish("Bridge")
            write_source("Sibling", "@[expose] public def offset := (1 : Nat)\n")
            publish("Sibling")
            check = write_source("Check",
                "import Batch.Bridge\nimport Batch.Sibling\nexample : doubled + offset = 5 := rfl\n")
            independent = write_source("Independent", "example : (2 : Nat) + 3 = 5 := rfl\n")

            def capture(output):
                run(sys.executable, "-B", TOOLS / "freeze_lean_imports.py",
                    output, check, bridge, provider, independent)

            def recheck(snapshot, output, *modules, expected=0, measure=False):
                options = ["--measure"] if measure else []
                return run(sys.executable, "-B", TOOLS / "recheck_lean_snapshot.py", snapshot, output,
                           *(f"Batch.{name}" for name in modules), *options, expected=expected)

            def results(output):
                receipt = json.loads((root / output / "receipt.json").read_text())
                return receipt["results"]

            def statuses(output):
                return {name: entry["status"] for name, entry in results(output).items()}

            reading("2")
            capture("frozen")
            reading("3")
            publish("Provider")
            write_source("Sibling", "@[expose] public def offset := (7 : Nat)\n")
            publish("Sibling")
            modules = ("Provider", "Bridge", "Check", "Independent")
            recheck("frozen", "complete", *modules)
            self.assertEqual(statuses("complete"), {f"Batch.{name}": "passed" for name in modules})
            self.assertTrue(all("measurement" not in item for item in results("complete").values()))

            rejected = recheck("frozen", "incomplete", "Provider", "Check", expected=1)
            self.assertIn("Include Batch.Bridge in the recheck", rejected.stderr)
            self.assertFalse((root / "incomplete").exists())

            reading("false")
            capture("bad")
            recheck("bad", "blocked", *modules, expected=1, measure=True)
            self.assertEqual(statuses("blocked"), {
                "Batch.Provider": "failed", "Batch.Bridge": "blocked",
                "Batch.Check": "blocked", "Batch.Independent": "passed",
            })
            measured = results("blocked")
            independent_measurement = measured["Batch.Independent"]["measurement"]
            self.assertGreater(independent_measurement["peak_rss_kib"], 0)
            self.assertGreaterEqual(independent_measurement["wall_seconds"], 0)
            self.assertGreaterEqual(independent_measurement["cpu_seconds"], 0)
            artifact = root / "blocked/objects/Batch/Independent.olean"
            self.assertEqual(independent_measurement["olean_bytes"], artifact.stat().st_size)
            self.assertIsNone(measured["Batch.Provider"]["measurement"]["olean_bytes"])
            self.assertNotIn("measurement", measured["Batch.Check"])

            private = root / "frozen" / "objects" / "Batch" / "Sibling.olean.private"
            private.rename(private.with_suffix(".withheld"))
            rejected = recheck("frozen", "missing", "Check", expected=1)
            self.assertIn("missing captured artifact: Batch/Sibling.olean.private", rejected.stderr)


if __name__ == "__main__":
    unittest.main()
