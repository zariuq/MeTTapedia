#!/usr/bin/env python3
"""
Unit tests for E prover to Megalodon translator
"""

import unittest
import subprocess
import os
import sys

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from e_to_megalodon import (
    parse_e_proof,
    analyze_proof_structure,
    generate_megalodon_direct_contradiction,
    generate_megalodon_orE_proof,
    ProofStep
)

EPROVER = "/tmp/E/PROVER/eprover"

class TestProofParsing(unittest.TestCase):
    """Test E proof output parsing"""

    def test_parse_simple_proof(self):
        """Test parsing a simple CNFRefutation"""
        proof_text = """
# SZS output start CNFRefutation
fof(ax1, axiom, p(a), file('test.p', ax1)).
fof(ax2, axiom, ~p(a), file('test.p', ax2)).
cnf(c_0_1, plain, (p(a)), inference(split_conjunct,[status(thm)],[ax1])).
cnf(c_0_2, plain, (~p(a)), inference(split_conjunct,[status(thm)],[ax2])).
cnf(c_0_3, plain, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_2, c_0_1])]), ['proof']).
# SZS output end CNFRefutation
"""
        steps = parse_e_proof(proof_text)
        self.assertEqual(len(steps), 5)

        # Check axioms
        axioms = [s for s in steps if s.is_axiom()]
        self.assertEqual(len(axioms), 2)

    def test_analyze_refutation(self):
        """Test proof structure analysis"""
        proof_text = """
# SZS output start CNFRefutation
fof(ax1, axiom, p(a), file('test.p', ax1)).
cnf(c_0_1, plain, ($false), inference(cn,[status(thm)],[ax1]), ['proof']).
# SZS output end CNFRefutation
"""
        steps = parse_e_proof(proof_text)
        analysis = analyze_proof_structure(steps)

        self.assertEqual(analysis['proof_type'], 'refutation')
        self.assertIsNotNone(analysis['final_step'])


class TestDirectContradiction(unittest.TestCase):
    """Test direct contradiction detection"""

    def test_simple_contradiction(self):
        """Test detection of p(a) vs ~p(a)"""
        proof_text = """
# SZS output start CNFRefutation
fof(ax1, axiom, p(a), file('test.p', ax1)).
fof(ax2, axiom, ~p(a), file('test.p', ax2)).
cnf(c_0_1, plain, (p(a)), inference(split_conjunct,[status(thm)],[ax1])).
cnf(c_0_2, plain, (~p(a)), inference(split_conjunct,[status(thm)],[ax2])).
cnf(c_0_3, plain, ($false), inference(cn,[status(thm)],[c_0_1, c_0_2]), ['proof']).
# SZS output end CNFRefutation
"""
        steps = parse_e_proof(proof_text)
        result = generate_megalodon_direct_contradiction(steps)

        self.assertIsNotNone(result)
        self.assertIn("direct contradiction", result)
        self.assertIn("p(a)", result)


class TestDisjunctionElimination(unittest.TestCase):
    """Test disjunction elimination proof generation"""

    def test_orE_chain_generation(self):
        """Test generating orE chain for disjunctions"""
        # This would need actual E prover output
        pass


class TestIntegration(unittest.TestCase):
    """Integration tests with actual E prover"""

    @unittest.skipUnless(os.path.exists(EPROVER), "E prover not found")
    def test_degree_bound_simple(self):
        """Test on degree_bound_simple.p"""
        problem_file = "/home/user/ai-agents/megalodon/ramsey36/tptp/degree_bound_simple.p"
        if not os.path.exists(problem_file):
            self.skipTest("Problem file not found")

        result = subprocess.run(
            [EPROVER, "--auto", "--proof-object", problem_file],
            capture_output=True, text=True
        )

        self.assertIn("Proof found", result.stdout)

        steps = parse_e_proof(result.stdout)
        self.assertGreater(len(steps), 0)

        # Should find direct contradiction at end
        contradiction = generate_megalodon_direct_contradiction(steps)
        self.assertIsNotNone(contradiction)

    @unittest.skipUnless(os.path.exists(EPROVER), "E prover not found")
    def test_no6indep_simple(self):
        """Test on simple no6indep case"""
        problem = """
fof(edge_4_5, axiom, adj(n4, n5)).
fof(no_edge_4_5, axiom, ~adj(n4, n5)).
fof(goal, conjecture, $false).
"""
        # Write temp file
        import tempfile
        with tempfile.NamedTemporaryFile(mode='w', suffix='.p', delete=False) as f:
            f.write(problem)
            temp_file = f.name

        try:
            result = subprocess.run(
                [EPROVER, "--auto", "--proof-object", temp_file],
                capture_output=True, text=True
            )

            self.assertIn("Proof found", result.stdout)

            steps = parse_e_proof(result.stdout)
            contradiction = generate_megalodon_direct_contradiction(steps)
            self.assertIsNotNone(contradiction)
            self.assertIn("adj(n4,n5)", contradiction)

        finally:
            os.unlink(temp_file)


class TestMegalodonOutput(unittest.TestCase):
    """Test that generated Megalodon code is syntactically correct"""

    def test_orE_proof_format(self):
        """Test orE proof has correct structure"""
        proof_text = """
# SZS output start CNFRefutation
fof(disj, axiom, (p|q), file('test.p', disj)).
fof(not_p, axiom, ~p, file('test.p', not_p)).
fof(not_q, axiom, ~q, file('test.p', not_q)).
cnf(c_0_1, plain, (p|q), inference(split_conjunct,[status(thm)],[disj])).
cnf(c_0_2, plain, (~p), inference(split_conjunct,[status(thm)],[not_p])).
cnf(c_0_3, plain, (~q), inference(split_conjunct,[status(thm)],[not_q])).
cnf(c_0_4, plain, ($false), inference(cn,[status(thm)],[c_0_1,c_0_2,c_0_3]), ['proof']).
# SZS output end CNFRefutation
"""
        steps = parse_e_proof(proof_text)
        result = generate_megalodon_orE_proof(steps)

        # Should have orE chain structure
        self.assertIn("apply orE", result)
        self.assertIn("assume H:", result)


class TestSuperpositionTranslation(unittest.TestCase):
    """Test superposition proof translation"""

    @unittest.skipUnless(os.path.exists(EPROVER), "E prover not found")
    def test_triangle_free_proof(self):
        """Test triangle_free style proof generates correct Megalodon"""
        problem = """
fof(triangle_free, axiom, ![X,Y,Z]: ~(adj(X,Y) & adj(Y,Z) & adj(X,Z))).
fof(clique_ab, axiom, adj(a,b)).
fof(clique_bc, axiom, adj(b,c)).
fof(clique_ac, axiom, adj(a,c)).
fof(goal, conjecture, $false).
"""
        import tempfile
        with tempfile.NamedTemporaryFile(mode='w', suffix='.p', delete=False) as f:
            f.write(problem)
            temp_file = f.name

        try:
            result = subprocess.run(
                [EPROVER, "--auto", "--proof-object", temp_file],
                capture_output=True, text=True
            )

            self.assertIn("Proof found", result.stdout)

            steps = parse_e_proof(result.stdout)

            # Import the function we need to test
            from e_to_megalodon import generate_superposition_proof

            spm_proof = generate_superposition_proof(steps)

            # Should find the triangle
            self.assertIsNotNone(spm_proof)
            self.assertIn("Triangle found", spm_proof)
            self.assertIn("exact Htf", spm_proof)
            # Should have correct terms
            self.assertIn("a", spm_proof)
            self.assertIn("b", spm_proof)
            self.assertIn("c", spm_proof)

        finally:
            os.unlink(temp_file)

    def test_extract_predicate_args(self):
        """Test predicate argument extraction"""
        from e_to_megalodon import extract_predicate_args

        pred, args = extract_predicate_args("adj(a,b)")
        self.assertEqual(pred, "adj")
        self.assertEqual(args, ["a", "b"])

        pred, args = extract_predicate_args("~adj(x,y)")
        self.assertEqual(pred, "adj")
        self.assertEqual(args, ["x", "y"])

        pred, args = extract_predicate_args("foo(a,b,c)")
        self.assertEqual(pred, "foo")
        self.assertEqual(args, ["a", "b", "c"])


if __name__ == '__main__':
    unittest.main(verbosity=2)
