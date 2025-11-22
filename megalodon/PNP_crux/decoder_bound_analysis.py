#!/usr/bin/env python3
"""
Analysis: What complexity bound is needed for the proof to work?

If we can prove SAT local decoders have bounded complexity, this SAVES the proof.
If we can show they can be unbounded, this BREAKS the proof.
"""

import math

def analyze_required_bound():
    """
    What circuit complexity bound on local decoders is needed?
    """
    print("=" * 70)
    print("REQUIRED COMPLEXITY BOUND FOR PROOF TO WORK")
    print("=" * 70)

    print("""
The proof needs:
  1. Hypothesis class H = {circuits of size s(m)}
  2. ERM sample complexity = O(log|H| / ε²)
  3. This must be << m (to fit in poly(log m) bits of info)

Counting argument:
  - Circuits on k inputs with s gates: roughly (k·s)^s circuits
  - log|H| ≈ s · log(k·s)
  - For k = log(m): log|H| ≈ s · log(s·log(m))

For ERM to work with poly(log m) samples:
  - Need: s · log(s·log m) ≤ poly(log m)
  - This requires: s ≤ poly(log m)

So the proof needs: Circuit_Complexity(h_i) ≤ poly(log m)
""")

    print("\nNumerical requirements:")
    for m in [1000, 10000, 100000, 1000000]:
        k = int(math.log2(m))

        # What circuit size s gives poly(log m) sample complexity?
        # Need: s · log(s · k) ≤ c · k^d for some constant c, degree d

        for d in [2, 3, 4]:
            # Target: log|H| ≤ k^d
            # With s gates: log|H| ≈ s · log(k·s)
            # Solve: s · log(k·s) = k^d

            target = k**d
            # Approximate: s ≈ k^d / log(k^d) = k^d / (d·log k)
            s_approx = target / (d * math.log2(k)) if k > 1 else target

            print(f"  m={m:7}, k={k:2}: For degree-{d} poly, need s ≤ {s_approx:.0f} gates")

        # Shannon's worst case
        s_shannon = (2**k) / k
        print(f"  m={m:7}, k={k:2}: Shannon worst-case: s = {s_shannon:.0f} gates")
        print()


def analyze_clause_counting_bound():
    """
    What bound does clause counting give?
    """
    print("=" * 70)
    print("CLAUSE COUNTING ARGUMENT")
    print("=" * 70)

    print("""
At clause density α = O(1):
  - Total clauses: α·m
  - Clauses per variable (average): 3α (each clause has 3 variables)
  - Clauses in O(log m)-neighborhood: O(α · (log m) · 3) = O(log m)

Each clause involving the neighborhood:
  - Is a 3-literal disjunction
  - Can be computed in O(1) gates
  - Contributes O(1) to the circuit

Naive bound:
  - O(log m) clauses × O(1) gates/clause = O(log m) gates
  - This computes WHETHER clauses are satisfied

But: The local decoder needs to compute σ_i, not clause satisfaction!

Refined analysis:
  - σ_i is uniquely determined by the formula + VV constraints
  - Given neighborhood values, propagate constraints
  - For tree-like neighborhoods: O(log m) propagation steps
  - For cyclic neighborhoods: might need more?

QUESTION: Does tree-likeness (from sparsification) guarantee O(log m)?
""")

    print("\nNumerical analysis of clause density effect:")
    for alpha in [1, 2, 4, 8]:
        for m in [1000, 10000, 100000]:
            k = int(math.log2(m))
            total_clauses = alpha * m
            # Expected clauses touching a k-variable neighborhood
            # Each clause involves 3 variables out of m
            # Prob clause touches at least one of k vars: ~ 3k/m
            clauses_in_neighborhood = total_clauses * (3 * k / m)

            print(f"  α={alpha}, m={m:6}, k={k:2}: "
                  f"~{clauses_in_neighborhood:.1f} clauses in neighborhood")


def analyze_tree_like_propagation():
    """
    What does tree-likeness give us for decoder complexity?
    """
    print("\n" + "=" * 70)
    print("TREE-LIKE PROPAGATION ANALYSIS")
    print("=" * 70)

    print("""
Sparsification theorem says: log-radius neighborhoods are tree-like w.h.p.

For tree-structured constraints:
  - Belief propagation converges in O(depth) iterations
  - Each iteration: O(degree) operations per node
  - Total: O(depth × nodes × degree) = O(log m × log m × O(1)) = O(log² m)

This gives: Circuit_Complexity(h_i) ≤ O(log² m) for tree-like regions

IS THIS SUFFICIENT?
  - Need: s ≤ poly(log m) ✓
  - O(log² m) IS poly(log m) ✓
  - So tree-like neighborhoods have BOUNDED complexity!

BUT: What about non-tree-like (cyclic) neighborhoods?
  - These occur with probability → 0 as m → ∞
  - But do they have bounded complexity?

WORST CASE: Cyclic neighborhood
  - Cycles can create long-range dependencies
  - Might need to solve a system of equations
  - Gaussian elimination: O(k³) = O(log³ m) operations

This is STILL poly(log m)! Even cyclic neighborhoods might be okay.
""")

    print("Numerical: Propagation complexity bounds")
    for m in [1000, 10000, 100000, 1000000]:
        k = int(math.log2(m))

        tree_bound = k**2  # O(log² m) for tree-like
        cycle_bound = k**3  # O(log³ m) for cyclic (Gaussian elim)
        shannon_bound = (2**k) / k  # Worst case for arbitrary function

        print(f"  m={m:7}: tree={tree_bound:5}, cycle={cycle_bound:6}, "
              f"shannon={shannon_bound:10.0f}")


def analyze_vv_constraint_effect():
    """
    How do VV constraints affect decoder complexity?
    """
    print("\n" + "=" * 70)
    print("VALIANT-VAZIRANI CONSTRAINT ANALYSIS")
    print("=" * 70)

    print("""
VV isolation adds XOR constraints: Ax = b

Effect on local decoder:
  1. Original SAT: multiple solutions
  2. After VV: unique solution σ
  3. Local decoder must output σ_i specifically

XOR constraints are LINEAR:
  - Can be solved by Gaussian elimination
  - Circuit complexity: O(k³) for k variables
  - For k = O(log m): complexity = O(log³ m)

Combined with SAT propagation:
  - SAT clauses: O(log² m) (tree-like propagation)
  - VV constraints: O(log³ m) (Gaussian elimination)
  - Total: O(log³ m)

This is STILL poly(log m)!

KEY INSIGHT:
  The VV constraints are LINEAR, which have efficient circuits.
  Even though they uniquely determine σ, the computation is bounded.
""")


def overall_assessment():
    """
    What's the overall picture?
    """
    print("\n" + "=" * 70)
    print("OVERALL ASSESSMENT: DECODER COMPLEXITY")
    print("=" * 70)

    print("""
EVIDENCE THAT LOCAL DECODERS HAVE BOUNDED COMPLEXITY:

1. CLAUSE COUNTING: O(log m) clauses in neighborhood
   → Cannot encode arbitrary function (needs 2^k clauses)
   → Local decoder is "simple" by information content

2. TREE-LIKE STRUCTURE: Sparsification gives tree neighborhoods
   → Belief propagation in O(log² m) operations
   → Circuit complexity O(log² m)

3. VV CONSTRAINTS: Linear XOR equations
   → Gaussian elimination in O(log³ m) operations
   → Circuit complexity O(log³ m)

4. COMBINED BOUND: O(log³ m) seems achievable
   → This IS poly(log m) ✓
   → Proof requirement satisfied!

REMAINING CONCERNS:

1. RIGOROUS PROOF: Above arguments are heuristic, not formal
   → Need to prove propagation gives correct decoder
   → Need to handle non-tree-like edge cases

2. ADVERSARIAL FORMULAS: What about worst-case (non-random)?
   → The proof uses random formulas (D_m distribution)
   → Adversarial formulas might have complex decoders
   → But these are measure-zero under D_m

3. CONSTANTS: The O(·) hides constants
   → Need actual constants to verify contradiction holds

CONCLUSION:

There is STRONG EVIDENCE that the conjecture is TRUE:
  Circuit_Complexity(h_i) ≤ O(log³ m) = poly(log m)

If this can be made rigorous, the proof is SAVED.
The hypothesis class expressiveness gap would be closed.

RECOMMENDED NEXT STEP:
  Formally prove that belief propagation + Gaussian elimination
  yields a poly(log m)-size circuit for the local decoder.
""")


def main():
    print("=" * 70)
    print(" DECODER COMPLEXITY ANALYSIS: WOULD PROOF BE SAVED OR BROKEN?")
    print("=" * 70)
    print()
    print("ANSWER: If true (bounded complexity), proof is SAVED")
    print("        If false (unbounded), proof is BROKEN")
    print()

    analyze_required_bound()
    analyze_clause_counting_bound()
    analyze_tree_like_propagation()
    analyze_vv_constraint_effect()
    overall_assessment()


if __name__ == "__main__":
    main()
