import contextlib
import io
import os
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from prepare import main, validate_output_paths


class PrepareSafetyTests(unittest.TestCase):
    def test_duplicate_and_source_aliases(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "source.mm"
            source.write_text("$c wff $.")
            hardlink = root / "hardlink.mm"
            os.link(source, hardlink)
            symlink = root / "symlink.mm"
            symlink.symlink_to(source)
            for target in (source, hardlink, symlink):
                with self.assertRaisesRegex(ValueError, "aliases"):
                    validate_output_paths([target], [source])
            with self.assertRaisesRegex(ValueError, "distinct"):
                validate_output_paths([root / "new", root / "child" / ".." / "new"], [source])
            with self.assertRaisesRegex(ValueError, "distinct"):
                validate_output_paths([source, hardlink], [])

    def test_expanded_source_identity_alias(self):
        with tempfile.TemporaryDirectory() as directory:
            include = Path(directory) / "child.mm"
            include.write_text("$c wff $.")
            identity = include.stat()
            with self.assertRaisesRegex(ValueError, "expanded source"):
                validate_output_paths([include], [], {(identity.st_dev, identity.st_ino)})

    def test_native_include_overwrite_rejected_and_staging_retained(self):
        translator = Path(__file__).resolve().parents[1] / "frontend" / "build" / "mm2-translate"
        if not translator.is_file():
            self.skipTest("Native translator is not built")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "root.mm"
            include = root / "child.mm"
            source.write_text("$[ child.mm $]\n")
            include.write_text("$c wff $.\n")
            original = include.read_bytes()
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                code = main(["--input", str(source), "--translator", str(translator),
                             "--data-output", str(include)])
            self.assertEqual(code, 2)
            self.assertEqual(include.read_bytes(), original)
            stages = list(root.glob("native-prepare-*"))
            self.assertEqual(len(stages), 1)
            self.assertTrue((stages[0] / "source-data.mm2").is_file())


if __name__ == "__main__":
    unittest.main()
