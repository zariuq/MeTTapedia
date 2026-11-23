import sys
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from mm2_atoms import AtomSyntaxError, Expr, Symbol, atom_digest, atoms_equal, head, parse_atoms, parse_forms, render_atoms


class AtomReaderTests(unittest.TestCase):
    def test_spacing_and_comments_do_not_change_atoms(self):
        first = parse_atoms('(exec (00 $x) ())\n(a "quoted token")')
        second = parse_atoms('; comment\n(exec\t(00 $x)\n()) ; tail\n(a "quoted token")')
        self.assertTrue(atoms_equal(first, second))
        self.assertEqual(atom_digest(first), atom_digest(second))
        self.assertEqual(head(first[0]), "exec")

    def test_raw_quoted_tokens_and_comment_boundaries(self):
        atoms = parse_atoms('(a x;y "$not-a-variable" "a\\\"b")')
        self.assertEqual(atoms[0].items[1], Symbol("x;y"))
        self.assertFalse(atoms[0].items[2].is_variable)
        self.assertTrue(atoms_equal(atoms, parse_atoms(render_atoms(atoms))))

    def test_order_variables_arity_and_quote_spelling_are_significant(self):
        for changed in ('(b a)', '(a $y)', '(a ($x))', '(a "$x")'):
            self.assertNotEqual(atom_digest(parse_atoms('(a $x)')), atom_digest(parse_atoms(changed)))

    def test_source_spans_select_complete_forms(self):
        source = '; first\n(a (b)) ; middle\n(c)\n'
        forms = parse_forms(source)
        self.assertEqual([source[item.start:item.end] for item in forms], ['(a (b))', '(c)'])

    def test_deep_atoms_are_iterative(self):
        source = '(' * 5000 + 'x' + ')' * 5000
        atoms = parse_atoms(source)
        self.assertEqual(render_atoms(atoms), source + '\n')
        self.assertTrue(atoms_equal(atoms, parse_atoms(source)))
        self.assertEqual(len(atom_digest(atoms)), 64)

    def test_malformed_input_is_rejected(self):
        for source in ('(a', 'a)', '("bad)', '"trailing\\'):
            with self.subTest(source=source), self.assertRaises(AtomSyntaxError):
                parse_atoms(source)

    def test_carriage_return_is_not_a_mork_separator(self):
        self.assertEqual(parse_atoms('(a\rb)'), [Expr((Symbol('a\rb'),))])


if __name__ == '__main__':
    unittest.main()
