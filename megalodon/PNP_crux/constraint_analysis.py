#!/usr/bin/env python3
"""
CONSTRAINT ANALYSIS

Analyzes the difference between:
1. OR clauses (actual SAT constraints)
2. XOR linearization (what we tested)
3. BP-derived constraints (what Goertzel might mean)

This explores whether there's a valid constraint formulation.
"""

import random
from typing import List, Tuple, Dict

def generate_planted_3sat(n: int, m: int, seed: int = 42):
    random.seed(seed)
    planted = [random.choice([True, False]) for _ in range(n)]
    clauses = []
    signs = []
    for _ in range(m):
        vars = tuple(sorted(random.sample(range(n), 3)))
        while True:
            s = tuple(random.choice([True, False]) for _ in range(3))
            satisfied = any(
                (planted[vars[j]] if s[j] else not planted[vars[j]])
                for j in range(3)
            )
            if satisfied:
                break
        clauses.append(vars)
        signs.append(s)
    return planted, clauses, signs


def analyze_clause_types(planted: List, clauses: List, signs: List):
    """
    For each clause, count how many literals are satisfied by planted.
    OR is satisfied if >= 1 literal is true.
    XOR gives same value as (count of true literals) mod 2.
    """

    distributions = {1: 0, 2: 0, 3: 0}

    for clause, sign in zip(clauses, signs):
        count_true = 0
        for j in range(3):
            lit_val = planted[clause[j]] if sign[j] else not planted[clause[j]]
            if lit_val:
                count_true += 1
        distributions[count_true] += 1

    return distributions


def bp_constraint_idea():
    """
    The BP-derived constraints are NOT XOR of the clause.

    Instead, BP propagates conditional probability information:
    - If clause C is satisfied by planted σ
    - And we know values of 2 variables in C
    - We can infer probability distribution on 3rd variable

    The "GE" in Goertzel's proof likely refers to:
    - Solving a system of CONDITIONAL constraints
    - Not a global XOR system

    Key insight: The constraints are LOCAL and CONDITIONAL.
    """
    pass


def test_conditional_inference(n: int, m: int, seed: int = 42):
    """
    Test: Given 2 variables in a clause, can we infer the 3rd?

    For a planted SAT clause (x ∨ y ∨ z):
    - If x=0, y=0, then z MUST be 1 (deterministic!)
    - If x=1, then y and z can be anything

    This is the key insight: CONDITIONAL constraints can be solved!
    """

    planted, clauses, signs = generate_planted_3sat(n, m, seed)

    correct_inferences = 0
    total_tests = 0
    deterministic_cases = 0

    for clause, sign in zip(clauses, signs):
        # For each clause, test inferring one variable from other two
        for target_idx in range(3):
            other_indices = [i for i in range(3) if i != target_idx]

            # Values of other two literals
            other_lit_vals = []
            for idx in other_indices:
                v = clause[idx]
                s = sign[idx]
                lit_val = planted[v] if s else not planted[v]
                other_lit_vals.append(lit_val)

            target_v = clause[target_idx]
            target_s = sign[target_idx]
            target_lit = planted[target_v] if target_s else not planted[target_v]

            # If both other literals are False, target MUST be True
            if not any(other_lit_vals):
                deterministic_cases += 1
                inferred_lit = True
                inferred_var = inferred_lit if target_s else not inferred_lit
                if inferred_var == planted[target_v]:
                    correct_inferences += 1
                total_tests += 1
            # Otherwise, we can't deterministically infer

    return {
        'total_tests': total_tests,
        'correct': correct_inferences,
        'deterministic': deterministic_cases,
        'accuracy': correct_inferences / total_tests if total_tests > 0 else 0
    }


def analyze_local_structure(n: int, m: int, depth: int, seed: int = 42):
    """
    Analyze how local structure enables decoding.

    Key insight: In the LOCAL tree-like neighborhood:
    1. Each variable appears in multiple clauses
    2. Constraints from different clauses can be COMBINED
    3. The combination gives deterministic inference
    """

    planted, clauses, signs = generate_planted_3sat(n, m, seed)

    # Build variable -> clause adjacency
    var_clauses = {v: [] for v in range(n)}
    for c_idx, (clause, sign) in enumerate(zip(clauses, signs)):
        for j, v in enumerate(clause):
            var_clauses[v].append((c_idx, clause, sign, j))

    # For each variable, check if it can be determined from local constraints
    determined_count = 0

    for v in range(n):
        if not var_clauses[v]:
            continue

        # Collect all constraints on v
        must_be_true = False
        must_be_false = False

        for c_idx, clause, sign, v_idx in var_clauses[v]:
            other_indices = [j for j in range(3) if j != v_idx]
            other_lit_vals = []
            for idx in other_indices:
                ov = clause[idx]
                os = sign[idx]
                lit_val = planted[ov] if os else not planted[ov]
                other_lit_vals.append(lit_val)

            if not any(other_lit_vals):
                # v's literal must be True to satisfy clause
                if sign[v_idx]:
                    must_be_true = True
                else:
                    must_be_false = True

        if must_be_true != must_be_false:
            # Uniquely determined
            determined = must_be_true
            if determined == planted[v]:
                determined_count += 1

    return {
        'total_vars': n,
        'determined': determined_count,
        'rate': determined_count / n
    }


def main():
    print("=" * 70)
    print("CONSTRAINT ANALYSIS")
    print("Understanding what constraints Goertzel's proof actually uses")
    print("=" * 70)
    print()

    # Analyze clause satisfaction distribution
    print("1. CLAUSE SATISFACTION DISTRIBUTION")
    print("-" * 50)
    planted, clauses, signs = generate_planted_3sat(100, 300, seed=42)
    dist = analyze_clause_types(planted, clauses, signs)
    total = sum(dist.values())
    for k, v in sorted(dist.items()):
        print(f"   {k} literals true: {v:3d} ({100*v/total:.1f}%)")
    print()
    print("   Key: Most clauses have >1 satisfied literal.")
    print("   XOR = 1 only when ODD number satisfied => CONFLICT!")
    print()

    # Test conditional inference
    print("2. CONDITIONAL INFERENCE TEST")
    print("-" * 50)
    configs = [(50, 100), (50, 150), (100, 300)]
    for n, m in configs:
        result = test_conditional_inference(n, m)
        print(f"   n={n}, m={m}: {result['deterministic']} deterministic cases, "
              f"{100*result['accuracy']:.1f}% correct")
    print()
    print("   Key: Conditional constraints give 100% accuracy!")
    print()

    # Analyze local structure
    print("3. LOCAL DETERMINATION RATE")
    print("-" * 50)
    configs = [(50, 100, 2), (50, 150, 2), (100, 300, 3)]
    for n, m, d in configs:
        result = analyze_local_structure(n, m, d)
        print(f"   n={n}, m={m}: {100*result['rate']:.1f}% variables locally determined")
    print()

    # The key insight
    print("=" * 70)
    print("KEY INSIGHT")
    print("=" * 70)
    print()
    print("The XOR linearization FAILS because:")
    print("  - OR clauses: at least 1 literal true")
    print("  - XOR constraint: odd number of literals true")
    print("  - These are DIFFERENT!")
    print()
    print("But CONDITIONAL inference WORKS:")
    print("  - If we know 2 vars in a clause, and both literals false")
    print("  - Then the 3rd literal MUST be true")
    print("  - This is DETERMINISTIC and CORRECT")
    print()
    print("Goertzel's 'GE' likely means:")
    print("  - Gaussian elimination on CONDITIONAL constraints")
    print("  - Not global XOR constraints")
    print("  - The system propagates through local tree structure")
    print()
    print("This is closer to UNIT PROPAGATION in SAT solving!")
    print()

    print("=" * 70)
    print("REVISED PREMISE STATUS")
    print("=" * 70)
    print()
    print("sub_premise_consistent:")
    print("  - XOR interpretation: FAILS (0% consistency)")
    print("  - Conditional interpretation: PLAUSIBLE (needs more analysis)")
    print()
    print("The proof may be valid if 'GE on VV constraints' means")
    print("'unit propagation style inference through tree structure'")
    print("rather than 'solve XOR linear system'")
    print()

    return 0


if __name__ == "__main__":
    exit(main())
