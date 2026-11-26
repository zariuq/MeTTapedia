from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory
import unittest

from freeze_lean_imports import import_graph, literal_elaboration_inputs


TOOLS = Path(__file__).resolve().parent


class SnapshotRecheckTest(unittest.TestCase):
    def test_explicit_lean_bypasses_the_ambient_executable(self):
        prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
        lean = prefix / "bin" / "lean"
        with TemporaryDirectory(prefix="lean-snapshot-toolchain-") as temporary:
            root = Path(temporary)
            source = root / "Sample.lean"
            source.write_text("prelude\n")
            ambient = root / "lean"
            ambient.write_text("#!/bin/sh\nexit 97\n")
            ambient.chmod(0o700)
            env = {**os.environ, "LEAN_PATH": "", "PATH": str(root) + os.pathsep + os.environ["PATH"]}
            command = [sys.executable, "-B", TOOLS / "freeze_lean_imports.py", "frozen", source]
            default = subprocess.run(command, cwd=root, env=env, text=True, capture_output=True)
            self.assertEqual(default.returncode, 1)
            self.assertIn("lean exited with status 97", default.stderr)
            selected = subprocess.run([*command, "--lean", lean], cwd=root, env=env,
                                      text=True, capture_output=True)
            self.assertEqual(selected.returncode, 0, selected.stdout + selected.stderr)
            manifest = json.loads((root / "frozen" / "snapshot.json").read_text())
            self.assertEqual(Path(manifest["lean"]), lean.resolve())

    def test_import_policy_larger_than_one_command_line_argument(self):
        prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
        env = {**os.environ, "LEAN_PATH": "", "LEAN_SYSROOT": str(prefix)}
        excluded = {"Batch.Provider"}
        excluded.update(f"Batch.Provider{index}." + "Nested" * 12 for index in range(1600))
        self.assertGreater(len(json.dumps(sorted(excluded))), 131072)
        with TemporaryDirectory(prefix="lean-import-request-") as temporary:
            source = Path(temporary) / "Consumer 🍃.lean"
            source.write_text("prelude\nimport Batch.Provider\n")
            self.assertEqual(import_graph(prefix / "bin" / "lean", TOOLS / "lean_import_graph.lean",
                                          [source], env, excluded), [])

    def test_elaboration_input_keeps_relative_path_and_original_bytes(self):
        prefix = subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
        env = {**os.environ, "PATH": str(Path(prefix) / "bin") + os.pathsep + os.environ["PATH"],
               "LEAN_PATH": "", "LEAN_SYSROOT": prefix}
        with TemporaryDirectory(prefix="lean-snapshot-") as temporary:
            root = Path(temporary)
            project = root / "project"
            project.mkdir()
            data = root / "data.txt"
            data.write_text("original")
            (project / "alias.txt").symlink_to("../data.txt")
            source = project / "Reading.lean"
            source.write_text(
                'def reading : String := include_str "alias.txt"\n'
                '#guard reading == "original"\n'
            )
            capture = [sys.executable, "-B", TOOLS / "freeze_lean_imports.py", "frozen", source,
                       "--source-root", project, "--workspace-root", root]
            subprocess.run(capture, cwd=root, env=env, check=True, capture_output=True)
            data.write_text("edited in the live tree")
            command = [sys.executable, "-B", TOOLS / "recheck_lean_snapshot.py", "frozen",
                       "checked", "Reading"]
            result = subprocess.run(command, cwd=root, env=env, text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

            frozen_data = root / "frozen" / "sources" / "data.txt"
            self.assertEqual(frozen_data.read_text(), "original")
            frozen_alias = root / "frozen" / "sources" / "project" / "alias.txt"
            self.assertEqual(os.readlink(frozen_alias), "../data.txt")
            frozen_alias.unlink()
            frozen_alias.write_text("original")
            command[-2] = "rejected-link"
            result = subprocess.run(command, cwd=root, env=env, text=True, capture_output=True)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn("captured elaboration input changed: sources/project/alias.txt", result.stderr)
            frozen_alias.unlink()
            frozen_alias.symlink_to("../data.txt")
            frozen_data.write_text("altered snapshot")
            command[-2] = "rejected"
            result = subprocess.run(command, cwd=root, env=env, text=True, capture_output=True)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn("captured elaboration input changed: sources/data.txt", result.stderr)
            self.assertFalse((root / "rejected").exists())

    def test_file_reader_recognition_skips_comment_and_string_text(self):
        with TemporaryDirectory(prefix="lean-literal-inputs-") as temporary:
            root = Path(temporary)
            for name in ("example.module", "rules.metta", "decoy.txt"):
                (root / name).write_text("")
            source = root / "Reader.lean"
            source.write_text(
                '-- #module_file "decoy.txt"\n'
                '/- include_str "decoy.txt" /- nested -/ -/\n'
                'def message := r#"petta_source_file% "decoy.txt""#\n'
                '#module_file "example.module"\n'
                'def source := petta_source_file%\n  "rules.metta"\n'
            )
            self.assertEqual(list(literal_elaboration_inputs(source)),
                             [root / "example.module", root / "rules.metta"])

    def test_module_tree_and_dialect_quotation_inputs(self):
        with TemporaryDirectory(prefix="lean-tree-inputs-") as temporary:
            root = Path(temporary)
            for name in ("data.metta", "program.metta", "pinned.metta", "commands.metta",
                         "chunks.metta", "lines.metta",
                         "parser.abi", "grammar.bin", "decoy.module"):
                (root / name).write_text("")
            modules = root / "modules"
            modules.mkdir()
            parent = modules / "Parent.module"
            child = modules / "Child.module"
            parent.write_text(
                '/- import "../decoy.module" as decoy -/\n'
                'import "Child.module" as child\nModule Parent {}\n'
            )
            child.write_text('Module Child {}\n')
            alias = root / "Alias.module"
            alias.symlink_to("modules/Parent.module")
            source = root / "Reader.lean"
            source.write_text(
                '#module_tree "Alias.module" as Bundle\n'
                'def code := metta_sexpr_file% petta "data.metta"\n'
                'def program := metta_sexpr_program_file%\n  he "program.metta"\n'
                'def pinned := metta_sexpr_pinned_file% petta "pinned.metta" sha256 "pin"\n'
                'def commands := metta_sexpr_commands_file% petta "commands.metta"\n'
                'def chunks := metta_sexpr_command_chunks_file%\n  petta "chunks.metta"\n'
                'def lines := metta_sexpr_lines_file% he "lines.metta"\n'
                'def pack := parser_pack_text_file% "parser.abi"\n'
                'def grammar := parser_snapshot_grammar_file% "grammar.bin"\n'
            )
            self.assertEqual(list(literal_elaboration_inputs(source, root)),
                             [alias, parent, child, root / "data.metta", root / "program.metta",
                              root / "pinned.metta", root / "commands.metta", root / "chunks.metta",
                              root / "lines.metta", root / "parser.abi", root / "grammar.bin"])

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

            def capture(output, *extra_sources, seal_imports=False):
                options = ["--seal-imports"] if seal_imports else []
                run(sys.executable, "-B", TOOLS / "freeze_lean_imports.py",
                    output, check, bridge, provider, independent, *extra_sources, *options)

            def recheck(snapshot, output, *modules, expected=0, measure=False, jobs=1,
                        link_imports=False, map_imports=False):
                options = ["--jobs", str(jobs)]
                if link_imports:
                    options.append("--link-imports")
                if map_imports:
                    options.append("--map-imports")
                if measure:
                    options.append("--measure")
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
            recheck("frozen", "parallel", *modules, jobs=2)
            self.assertEqual(statuses("parallel"), statuses("complete"))

            rejected = recheck("frozen", "writable", *modules, expected=1, link_imports=True)
            self.assertIn("shared compiled import must be read-only", rejected.stderr)
            self.assertFalse((root / "writable").exists())

            write_source("Sibling", "@[expose] public def offset := (1 : Nat)\n")
            publish("Sibling")
            reading("2")
            capture("sealed", seal_imports=True)
            frozen_provider = root / "sealed/objects/Batch/Provider.olean"
            frozen_sibling = root / "sealed/objects/Batch/Sibling.olean"
            provider_before = frozen_provider.read_bytes()
            recheck("sealed", "linked", *modules, link_imports=True)
            self.assertEqual(statuses("linked"), statuses("complete"))
            self.assertTrue(frozen_sibling.samefile(root / "linked/objects/Batch/Sibling.olean"))
            self.assertFalse(frozen_provider.samefile(root / "linked/objects/Batch/Provider.olean"))
            self.assertEqual(frozen_provider.read_bytes(), provider_before)
            self.assertEqual(
                (root / "linked/objects/Batch/Check.olean").read_bytes(),
                (root / "complete/objects/Batch/Check.olean").read_bytes(),
            )
            recheck("sealed", "mapped", *modules, jobs=2, map_imports=True)
            self.assertEqual(statuses("mapped"), statuses("complete"))
            self.assertFalse((root / "mapped/objects/Batch/Sibling.olean").exists())
            self.assertEqual(
                (root / "mapped/objects/Batch/Check.olean").read_bytes(),
                (root / "complete/objects/Batch/Check.olean").read_bytes(),
            )

            from_sealed = {**env, "LEAN_PATH": str(root / "sealed/objects")}
            command = [sys.executable, "-B", TOOLS / "freeze_lean_imports.py",
                       "recaptured", check, "--reuse-imports", "sealed"]
            result = subprocess.run(command, cwd=root, env=from_sealed, text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            reused = root / "recaptured/objects/Batch"
            self.assertTrue(frozen_sibling.samefile(reused / "Sibling.olean"))
            self.assertTrue(frozen_provider.samefile(reused / "Provider.olean"))

            reading("4")
            publish("Provider")
            latest = write_source("Latest",
                "import Batch.Provider\nimport Batch.Sibling\nexample : reading + offset = 5 := rfl\n")
            run(sys.executable, "-B", TOOLS / "freeze_lean_imports.py",
                "retained", latest, "--reuse-imports", "sealed")
            current = root / "retained/objects/Batch"
            self.assertTrue(frozen_sibling.samefile(current / "Sibling.olean"))
            self.assertFalse(frozen_provider.samefile(current / "Provider.olean"))
            self.assertFalse((current / "Provider.olean").stat().st_mode & 0o222)
            recheck("retained", "retained-result", "Latest", link_imports=True)

            frozen_sibling.touch()
            rejected = recheck("sealed", "changed", *modules, expected=1, map_imports=True)
            self.assertIn("captured import changed: Batch/Sibling.olean", rejected.stderr)
            self.assertFalse((root / "changed").exists())
            run(sys.executable, "-B", TOOLS / "freeze_lean_imports.py",
                "refreshed", latest, "--reuse-imports", "sealed")
            self.assertFalse(frozen_sibling.samefile(root / "refreshed/objects/Batch/Sibling.olean"))
            recheck("refreshed", "refreshed-result", "Latest", link_imports=True)

            invalid = recheck("frozen", "invalid", *modules, expected=1, jobs=0)
            self.assertIn("jobs must be positive", invalid.stderr)
            self.assertFalse((root / "invalid").exists())

            rejected = recheck("frozen", "incomplete", "Provider", "Check", expected=1)
            self.assertIn("Include Batch.Bridge in the recheck", rejected.stderr)
            self.assertFalse((root / "incomplete").exists())

            extra = write_source("Extra", "@[expose] public def input := (2 : Nat)\n")
            write_source("Sibling", "@[expose] public def offset := (1 : Nat)\n")
            publish("Sibling")
            capture("variant", extra)
            manifest_path = root / "variant" / "snapshot.json"
            manifest = json.loads(manifest_path.read_text())
            bridge_entry = next(entry for entry in manifest["sources"]
                                if entry["source"].endswith("/Batch/Bridge.lean"))
            variant_bridge = root / "variant" / bridge_entry["copy"]
            variant_bridge.write_text(
                "module\npublic import Batch.Extra\n@[expose] public def doubled := input * 2\n"
            )
            bridge_entry["sha256"] = sha256(variant_bridge.read_bytes()).hexdigest()
            manifest_path.write_text(json.dumps(manifest))
            self.assertFalse((root / "variant/objects/Batch/Extra.olean").exists())
            rejected = recheck("variant", "absent-provider", *modules, expected=1, jobs=2)
            self.assertIn("Batch.Bridge has an unrecorded import: Batch.Extra", rejected.stderr)
            recheck("variant", "new-provider", *modules, "Extra", jobs=2)
            self.assertTrue(all(status == "passed" for status in statuses("new-provider").values()))

            consumer = write_source("Uncached", "import Batch.Extra\nexample : input = 2 := rfl\n")
            freeze = [sys.executable, "-B", TOOLS / "freeze_lean_imports.py"]
            missing = run(*freeze, "missing-import", consumer, expected=1)
            self.assertIn("Batch/Uncached.lean imports Batch.Extra", missing.stderr)
            self.assertFalse((root / "missing-import").exists())

            live_provider = live / "Batch/Provider.olean"
            parked = live_provider.rename(root / "Provider.olean")
            try:
                missing = run(*freeze, "missing-transitive", check, expected=1)
                self.assertIn("Batch.Bridge imports Batch.Provider", missing.stderr)
                self.assertFalse((root / "missing-transitive").exists())
            finally:
                parked.rename(live_provider)

            absent = run(*freeze, "missing-source", consumer, "--from-source", "Batch.Extra", expected=1)
            self.assertIn("missing source for --from-source: Batch.Extra", absent.stderr)
            run(*freeze, "uncached", consumer, extra, "--from-source", "Batch.Extra")
            self.assertFalse((root / "uncached/objects/Batch/Extra.olean").exists())
            rejected = recheck("uncached", "unbuilt", "Uncached", expected=1)
            self.assertIn("Batch.Uncached requires source-only module Batch.Extra", rejected.stderr)
            recheck("uncached", "built-from-source", "Uncached", "Extra", jobs=2)
            self.assertEqual(statuses("built-from-source"), {
                "Batch.Extra": "passed", "Batch.Uncached": "passed",
            })

            run(*freeze, "source-only-ancestor", check, provider, "--from-source", "Batch.Provider")
            rejected = recheck("source-only-ancestor", "stale-ancestor", "Check", expected=1)
            self.assertIn("Include Batch.Bridge in the recheck", rejected.stderr)

            reading("false")
            capture("bad", seal_imports=True)
            recheck("bad", "blocked", *modules, expected=1, measure=True, jobs=2)
            self.assertEqual(statuses("blocked"), {
                "Batch.Provider": "failed", "Batch.Bridge": "blocked",
                "Batch.Check": "blocked", "Batch.Independent": "passed",
            })
            recheck("bad", "blocked-linked", *modules, expected=1, link_imports=True)
            self.assertEqual(statuses("blocked-linked"), statuses("blocked"))
            recheck("bad", "blocked-mapped", *modules, expected=1, jobs=2, map_imports=True)
            self.assertEqual(statuses("blocked-mapped"), statuses("blocked"))
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
