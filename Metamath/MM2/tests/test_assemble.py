import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from assemble import DEFAULT_MANIFEST, load_verifier
from mm2_atoms import atom_digest, head, parse_atoms


class AssemblyTests(unittest.TestCase):
    def test_canonical_assembly(self):
        assembly = load_verifier()
        self.assertEqual(len(assembly.atoms), 1092)
        self.assertEqual(sum(head(atom) == "exec" for atom in assembly.atoms), 221)
        self.assertEqual(atom_digest(parse_atoms(assembly.text)), assembly.manifest["parsed_sha256"])

    def test_corruption_and_manifest_reordering_fail(self):
        source = DEFAULT_MANIFEST.parent
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory)
            manifest = json.loads(DEFAULT_MANIFEST.read_text())
            for fragment in manifest["fragments"]:
                (target / fragment["file"]).write_text((source / fragment["file"]).read_text())
            manifest["fragments"].reverse()
            (target / "manifest.json").write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, "assembled verifier: parsed_sha256 mismatch"):
                load_verifier(target / "manifest.json")
            manifest["fragments"].reverse()
            (target / "manifest.json").write_text(json.dumps(manifest))
            first = target / manifest["fragments"][0]["file"]
            first.write_text(first.read_text().replace("$", "$changed", 1))
            with self.assertRaisesRegex(ValueError, "parsed_sha256 mismatch"):
                load_verifier(target / "manifest.json")


if __name__ == '__main__':
    unittest.main()
