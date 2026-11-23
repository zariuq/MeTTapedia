"""Controls for the untrusted data adapter, independent of proof acceptance."""
import copy
import unittest

from export_sexpr import Export, decode, encode, loads


class CodecTests(unittest.TestCase):
    def test_json_values(self):
        values = [None, True, False, 0, -1, 2**90, 1.125, [], {},
                  "quotes\"\\\nλ", "\x00\x01\ud800", {"\x00": "\t"}, [1, "1", True, None],
                  {"a": [1, 2], "b": {"body": "(x $y);"}}]
        for value in values:
            with self.subTest(value=value):
                self.assertEqual(decode(encode(value)), value)

    def test_refusals(self):
        for text in ["", "(jbool yes)", '(jnum "true")', '(jnum "NaN")',
                     '(jstr 2)', '(jarr (jnull)', '(jnull) extra',
                     '(jobj (jfield (jstr "x") (jnull)) (jfield (jstr "x") (jnull)))',
                     '(jcodes -1)', '(jcodes 1114112)', '(jobj (jfield (jnum "2") (jnull)))',
                     '(unknown)']:
            with self.subTest(text=text), self.assertRaises(ValueError):
                decode(text)
        with self.assertRaises(ValueError):
            loads('{"x": 1, "x": 2}')
        with self.assertRaises(ValueError):
            encode(float("inf"))

    def test_shared_closure(self):
        rows = [{"meta": {"format": {"version": "3.1.0"}}},
                {"in": 1, "str": {"pre": 0, "str": "P"}},
                {"ie": 0, "sort": 0},
                {"axiom": {"name": 1, "type": 0}},
                {"ie": 1, "const": {"name": 1, "us": []}},
                {"ie": 2, "app": {"fn": 1, "arg": 1}}]
        export = Export(rows)
        self.assertEqual(export.dependencies({"type": 2}), [1])
        self.assertEqual(export.children[2], [1, 1])
        self.assertEqual(len(export.exprs), 3)
        # Shared references retain multiplicity in syntax, without duplicating nodes.
        bad = copy.deepcopy(rows)
        bad[-1]["app"]["arg"] = 99
        with self.assertRaises(ValueError):
            Export(bad)
        with self.assertRaises(ValueError):
            Export(rows + [rows[-1]])
        with self.assertRaises(ValueError):
            Export([r for r in rows if "axiom" not in r])
        with self.assertRaises(ValueError):
            Export(rows + [{"thm": {"name": 1, "type": 0, "value": 1}}])


if __name__ == "__main__":
    unittest.main()
