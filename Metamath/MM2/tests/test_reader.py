"""Native B reader, provenance, and output-preservation regression checks.

Fixtures and outputs are retained in the supplied work directory. The reader
preserves proof syntax; none of these checks executes a proof verifier.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from mm2_atoms import Expr, head, parse_atoms

TRANSLATOR = ROOT / "frontend/build/mm2-translate"
WORK = None
SUITE = None


def nat(atom):
    assert head(atom) == "mm-nat"
    return int(atom.items[1].text)


def string(atom):
    assert head(atom) == "mm-string"
    cursor = atom.items[1]
    result = []
    while head(cursor) == "mm-char-cons":
        result.append(chr(nat(cursor.items[1])))
        cursor = cursor.items[2]
    assert head(cursor) == "mm-char-nil"
    return "".join(result)


def values(atom):
    result = []
    while head(atom) == "mm-cons":
        result.append(atom.items[1])
        atom = atom.items[2]
    assert head(atom) == "mm-nil"
    return result


def span(atom):
    assert head(atom) == "mm-source-span"
    return string(atom.items[1]), nat(atom.items[2]), nat(atom.items[3])


def name(atom):
    assert head(atom) == "mm-source-name"
    return string(atom.items[2])


def event_rows(path):
    return [atom.items[5] for atom in parse_atoms(path.read_text())
            if head(atom) == "mm-linked-row" and
            isinstance(atom.items[1], Expr) and
            head(atom.items[1]) == "mm-string" and
            string(atom.items[1]) == "source-statement"]


class ReaderTests(unittest.TestCase):
    def setUp(self):
        self.directory = Path(tempfile.mkdtemp(prefix="reader-", dir=WORK))

    def source(self, data, name="unit.mm"):
        path = self.directory / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        return path

    def translate(self, source, output=None, *extra):
        if output is None:
            output = self.directory / "data.mm2"
        result = subprocess.run([str(TRANSLATOR), str(source), "--output",
                                 str(output), *extra], capture_output=True, timeout=30)
        return result, output

    def success(self, source, *extra):
        result, output = self.translate(source, None, *extra)
        self.assertEqual(result.returncode, 0, result.stderr.decode(errors="replace"))
        return output

    def test_identity_is_pinned(self):
        result = subprocess.run([str(TRANSLATOR), "--identity"],
                                capture_output=True, text=True, check=True)
        identity = json.loads(result.stdout)
        self.assertEqual(identity["schema"], "mm2-source-data-v1")
        self.assertEqual(identity["profile"], "zar")
        self.assertEqual(identity["version"], "1")
        revision = next(line.split(":=", 1)[1].strip() for line in
                        (ROOT / "frontend/source.lock").read_text().splitlines()
                        if line.startswith("CETTA_REVISION :="))
        self.assertEqual(identity["reader_revision"], revision)

    def test_exact_sites_normal_and_opaque_compressed_payloads(self):
        data = (b"$c wff |- $.\n$v x $.\nwf $f wff x $.\nax $a |- x $.\n"
                b"normal $p |- x $= wf not-yet-defined ? $.\n"
                b"compact $p |- x $= ( ax ) AZ? UUA $.\n")
        output = self.success(self.source(data))
        self.assertTrue(all(head(atom) != "exec" for atom in parse_atoms(output.read_text())))
        events = event_rows(output)
        self.assertEqual([head(event) for event in events],
                         ["mm-source-const", "mm-source-var", "mm-source-floating",
                          "mm-source-axiom", "mm-source-theorem", "mm-source-theorem"])
        normal, compact = events[-2:]
        normal_start = data.index(b"$p", data.index(b"normal"))
        self.assertEqual(span(normal.items[1]), ("unit.mm", normal_start, normal_start + 2))
        self.assertEqual(name(normal.items[2]), "normal")
        self.assertEqual(head(normal.items[5]), "mm-source-normal-proof")
        self.assertEqual([name(value) for value in values(normal.items[5].items[1])],
                         ["wf", "not-yet-defined", "?"])
        for event in (normal, compact):
            file, begin, end = span(event.items[-2])
            self.assertEqual(file, "unit.mm")
            self.assertEqual(data[begin:end], b"$=")
            self.assertEqual(data[slice(*span(event.items[-1])[1:])], b"$.")
        proof = compact.items[5]
        self.assertEqual(head(proof), "mm-source-compressed-proof")
        self.assertEqual(data[slice(*span(proof.items[1])[1:])], b"(")
        self.assertEqual([name(value) for value in values(proof.items[2])], ["ax"])
        self.assertEqual(data[slice(*span(proof.items[3])[1:])], b")")
        words = values(proof.items[4])
        self.assertEqual([bytes(nat(byte) for byte in values(word.items[2]))
                          for word in words], [b"AZ?", b"UUA"])
        for word in words:
            self.assertEqual(data[slice(*span(word.items[1])[1:])],
                             bytes(nat(byte) for byte in values(word.items[2])))

    def test_scope_and_ordered_declaration_tags(self):
        data = (b"$c wff |- $.\n$v x y $.\nwx $f wff x $.\nwy $f wff y $.\n"
                b"${\n$d x y $.\nh $e |- x $.\na $a |- y $.\n$}\n")
        events = event_rows(self.success(self.source(data)))
        self.assertEqual([head(event) for event in events],
                         ["mm-source-const", "mm-source-var", "mm-source-floating",
                          "mm-source-floating", "mm-source-open-scope", "mm-source-dv",
                          "mm-source-essential", "mm-source-axiom", "mm-source-close-scope"])
        for event, directive in zip(events, [b"$c", b"$v", b"$f", b"$f", b"${",
                                           b"$d", b"$e", b"$a", b"$}"]):
            self.assertEqual(data[slice(*span(event.items[1])[1:])], directive)

    def test_parent_relative_include_dedup_and_book_cycle(self):
        child = self.source(b"$[ ../root.mm $]\n$c wff |- $.\n$v x $.\n"
                            b"wf $f wff x $.\nax $a |- x $.\n", "sub/child.mm")
        root = self.source(b"$[ sub/child.mm $]\n$[ ./sub/child.mm $]\n"
                           b"$[ link.mm $]\nth $p |- x $= wf ax $.\n", "root.mm")
        os.symlink(child, self.directory / "link.mm")
        events = event_rows(self.success(root))
        self.assertEqual(len(events), 5)
        self.assertEqual([head(event) for event in events],
                         ["mm-source-const", "mm-source-var", "mm-source-floating",
                          "mm-source-axiom", "mm-source-theorem"])
        self.assertTrue(all(span(event.items[1])[0] == "sub/child.mm" for event in events[:4]))
        self.assertEqual(span(events[-1].items[1])[0], "unit.mm")

    def test_root_and_included_output_aliases_are_preserved(self):
        child = self.source(b"$c wff $.\n", "child.mm")
        root = self.source(b"$[ child.mm $]\n", "root.mm")
        for target in (root, child):
            aliases = [target]
            for kind in ("hard", "symbolic"):
                alias = self.directory / (target.stem + "-" + kind + ".mm2")
                if kind == "hard": os.link(target, alias)
                else: os.symlink(target, alias)
                aliases.append(alias)
            before = hashlib.sha256(target.read_bytes()).digest()
            for alias in aliases:
                result, _ = self.translate(root, alias)
                self.assertEqual(result.returncode, 2)
                self.assertEqual(hashlib.sha256(target.read_bytes()).digest(), before)
                self.assertEqual(list(alias.parent.glob(alias.name + ".stage.*")), [])

    def test_source_identity_preflight_is_complete_and_path_free(self):
        child = self.source(b"$c wff $.\n", "child.mm")
        root = self.source(b"$[ child.mm $]\n$[ ./child.mm $]\n", "root.mm")
        result = subprocess.run([str(TRANSLATOR), str(root), "--source-identities"],
                                capture_output=True, text=True, check=True)
        metadata = json.loads(result.stdout)
        self.assertEqual(metadata["schema"], "mm2-source-identities-v1")
        self.assertEqual(metadata["files"],
                         [{"device": path.stat().st_dev, "inode": path.stat().st_ino}
                          for path in (root, child)])
        self.assertNotIn(str(self.directory), result.stdout)
        self.assertEqual(list(self.directory.glob("*.mm2")), [])

    def test_rejections_preserve_output_and_retain_only_own_staging(self):
        output = self.directory / "data.mm2"
        output.write_bytes(b"previous output\n")
        invalid = self.source(b"$( bad\x07comment $)\n")
        result, _ = self.translate(invalid, output)
        self.assertEqual(result.returncode, 1)
        self.assertEqual(output.read_bytes(), b"previous output\n")
        self.assertEqual(list(output.parent.glob(output.name + ".stage.*")), [])
        structural = self.source(b"$c wff $.\n$c wff $.\n", "duplicate.mm")
        result, _ = self.translate(structural, output)
        self.assertEqual(result.returncode, 1)
        self.assertEqual(output.read_bytes(), b"previous output\n")
        staging = list(output.parent.glob(output.name + ".stage.*"))
        self.assertEqual(len(staging), 1)
        self.assertIn(str(staging[0]).encode(), result.stderr)
        self.assertTrue(staging[0].is_file())

    def test_profile_and_utf8_names(self):
        source = self.source(b"$c wff $.\n")
        output = self.success(source, "--owner", "proof λ", "--root-name", "根.mm")
        events = event_rows(output)
        self.assertEqual(span(events[0].items[1])[0], "根.mm")
        result, _ = self.translate(source, self.directory / "wrong-profile.mm2",
                                   "--profile", "other")
        self.assertEqual(result.returncode, 2)
        if os.name == "posix":
            result, target = self.translate(source, self.directory / "bad-name.mm2",
                                            "--root-name", "\udcff")
            self.assertEqual(result.returncode, 2)
            self.assertFalse(target.exists())

    def test_missing_source_and_unpublishable_output_are_tool_failures(self):
        result, _ = self.translate(self.directory / "missing.mm")
        self.assertEqual(result.returncode, 2)
        source = self.source(b"$c wff $.\n")
        output = self.directory / "output-directory"
        output.mkdir()
        result, _ = self.translate(source, output)
        self.assertEqual(result.returncode, 2)
        self.assertTrue(output.is_dir())
        self.assertEqual(len(list(output.parent.glob(output.name + ".stage.*"))), 1)

    def test_comment_at_end_of_file(self):
        self.success(self.source(b"$c wff $. $( final comment $)"))

    def test_current_seven_lexical_boundaries(self):
        bodies = [b"$( bell\x07here $)\n", b"$( vertical\x0btab $)\n",
                  b"$( non\xc3\xa9ascii $)\n", b"$( before$(after $)\n",
                  b"$( before$)after $)\n", b"$c\x0bwff $.\n",
                  b"$( hidden\x00 $)\n$c wff $.\n"]
        for index, body in enumerate(bodies):
            result, target = self.translate(self.source(body, f"boundary-{index}.mm"),
                                            self.directory / f"boundary-{index}.mm2")
            self.assertEqual(result.returncode, 1, result.stderr)
            self.assertFalse(target.exists())
        if SUITE:
            registered = sorted((SUITE / "tests/unit").glob("test11[0-6]_*.mm"))
            self.assertEqual(len(registered), 7, "current lexical fixtures must all be present")
            for source in registered:
                result, target = self.translate(source, self.directory / (source.stem + ".mm2"))
                self.assertEqual(result.returncode, 1, result.stderr)
                self.assertFalse(target.exists())


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--translator", type=Path, default=TRANSLATOR)
    parser.add_argument("--work-dir", type=Path)
    parser.add_argument("--suite", type=Path)
    args, remaining = parser.parse_known_args()
    TRANSLATOR = args.translator.resolve()
    WORK = args.work_dir or ROOT / "frontend/build/reader-tests"
    WORK.mkdir(parents=True, exist_ok=True)
    SUITE = args.suite.resolve() if args.suite else None
    unittest.main(argv=[sys.argv[0], *remaining])
