#!/usr/bin/env python3
"""
CONSISTENCY VERIFICATION

Tests sub_premise_consistent: Are local VV constraint systems consistent?
If not, GE can't find a solution and the decoder construction fails.
"""

import random
from typing import List, Tuple, Dict, Set

def generate_planted_3sat(n: int, m: int, seed: int = 42):
    """Generate a planted 3-SAT instance."""
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


def extract_local_linear_system(var_i: int, clauses: List, signs: List, planted: List, depth: int):
    """
    Extract local linear constraints over GF(2) from the factor graph.

    The VV constraints are linearizations of the clause constraints.
    For a clause (x ⊕ a) ∨ (y ⊕ b) ∨ (z ⊕ c), the XOR relaxation is:
    (x ⊕ a) ⊕ (y ⊕ b) ⊕ (z ⊕ c) = 1 (at least one true, XOR approx)

    This gives: x ⊕ y ⊕ z = 1 ⊕ a ⊕ b ⊕ c
    """

    local_clauses = []
    local_vars = {var_i}
    frontier = {var_i}

    for d in range(depth):
        new_frontier = set()
        for c_idx, clause in enumerate(clauses):
            if any(v in frontier for v in clause):
                if c_idx not in [lc[0] for lc in local_clauses]:
                    local_clauses.append((c_idx, clause, signs[c_idx]))
                    for v in clause:
                        if v not in local_vars:
                            new_frontier.add(v)
                            local_vars.add(v)
        frontier = new_frontier
        if not frontier:
            break

    # Build linear system over GF(2)
    var_list = sorted(local_vars)
    var_idx = {v: i for i, v in enumerate(var_list)}
    n_vars = len(var_list)

    # Each clause gives one linear constraint
    matrix = []  # Each row is (coefficients, rhs)

    for c_idx, clause, sign in local_clauses:
        row = [0] * n_vars
        for v in clause:
            row[var_idx[v]] = 1

        # RHS: XOR of signs XOR 1
        rhs = 1
        for s in sign:
            if not s:  # negated literal
                rhs ^= 1

        matrix.append((row, rhs))

    return {
        'vars': var_list,
        'var_idx': var_idx,
        'matrix': matrix,
        'planted_values': [int(planted[v]) for v in var_list]
    }


def gaussian_elimination_gf2(matrix: List[Tuple[List[int], int]]):
    """
    Perform Gaussian elimination over GF(2).
    Returns (is_consistent, rank, solution_if_any)
    """
    if not matrix:
        return True, 0, []

    n_rows = len(matrix)
    n_cols = len(matrix[0][0])

    # Augmented matrix
    aug = [[matrix[i][0][j] for j in range(n_cols)] + [matrix[i][1]]
           for i in range(n_rows)]

    pivot_row = 0
    pivot_cols = []

    for col in range(n_cols):
        # Find pivot
        found = False
        for row in range(pivot_row, n_rows):
            if aug[row][col] == 1:
                # Swap rows
                aug[pivot_row], aug[row] = aug[row], aug[pivot_row]
                found = True
                break

        if not found:
            continue

        pivot_cols.append(col)

        # Eliminate other rows
        for row in range(n_rows):
            if row != pivot_row and aug[row][col] == 1:
                for c in range(n_cols + 1):
                    aug[row][c] ^= aug[pivot_row][c]

        pivot_row += 1

    # Check consistency: any row with all zeros but RHS = 1?
    rank = pivot_row
    for row in range(rank, n_rows):
        if aug[row][n_cols] == 1:  # 0 = 1, inconsistent
            return False, rank, None

    # System is consistent, find a solution
    solution = [0] * n_cols
    for i, col in enumerate(pivot_cols):
        solution[col] = aug[i][n_cols]

    return True, rank, solution


def check_planted_satisfies(system: Dict) -> bool:
    """Check if planted assignment satisfies the linear system."""
    for row, rhs in system['matrix']:
        xor_sum = 0
        for i, coef in enumerate(row):
            if coef:
                xor_sum ^= system['planted_values'][i]
        if xor_sum != rhs:
            return False
    return True


def test_consistency(n: int, alpha: float, depth: int, num_trials: int = 5):
    """Test if local linear systems are consistent."""

    m = int(alpha * n)

    total_systems = 0
    consistent_count = 0
    planted_satisfies_count = 0
    ge_matches_planted = 0

    for trial in range(num_trials):
        planted, clauses, signs = generate_planted_3sat(n, m, seed=trial * 1000)

        test_vars = random.sample(range(n), min(10, n))

        for var_i in test_vars:
            system = extract_local_linear_system(var_i, clauses, signs, planted, depth)

            if not system['matrix']:
                continue

            total_systems += 1

            # Check planted satisfies
            if check_planted_satisfies(system):
                planted_satisfies_count += 1

            # Run GE
            is_consistent, rank, solution = gaussian_elimination_gf2(system['matrix'])

            if is_consistent:
                consistent_count += 1

                # Check if solution matches planted at center variable
                if solution:
                    center_idx = system['var_idx'][var_i]
                    if solution[center_idx] == system['planted_values'][center_idx]:
                        ge_matches_planted += 1

    return {
        'total': total_systems,
        'consistent': consistent_count,
        'planted_satisfies': planted_satisfies_count,
        'ge_matches_planted': ge_matches_planted,
        'consistency_rate': consistent_count / total_systems if total_systems > 0 else 0,
        'planted_rate': planted_satisfies_count / total_systems if total_systems > 0 else 0,
        'match_rate': ge_matches_planted / consistent_count if consistent_count > 0 else 0
    }


def main():
    print("=" * 60)
    print("CONSISTENCY VERIFICATION")
    print("Testing: Are local VV linear systems consistent?")
    print("=" * 60)
    print()

    configs = [
        (50, 2.0, 2),
        (50, 2.0, 3),
        (50, 3.0, 2),
        (50, 3.0, 3),
        (100, 2.5, 3),
        (100, 3.5, 3),
    ]

    print(f"{'n':>6} {'α':>6} {'depth':>6} {'consist%':>10} {'planted%':>10} {'match%':>10} {'STATUS':>10}")
    print("-" * 70)

    results = []
    for n, alpha, depth in configs:
        result = test_consistency(n, alpha, depth, num_trials=3)

        cons_pct = result['consistency_rate'] * 100
        plant_pct = result['planted_rate'] * 100
        match_pct = result['match_rate'] * 100

        if cons_pct >= 90 and plant_pct >= 80:
            status = "PASS"
        elif cons_pct >= 70:
            status = "WEAK"
        else:
            status = "FAIL"

        results.append((n, alpha, depth, cons_pct, plant_pct, match_pct, status))
        print(f"{n:>6} {alpha:>6.1f} {depth:>6} {cons_pct:>9.1f}% {plant_pct:>9.1f}% {match_pct:>9.1f}% {status:>10}")

    print("-" * 70)
    print()

    fail_count = sum(1 for r in results if r[6] == "FAIL")

    print("=" * 60)
    print("ANALYSIS OF sub_premise_consistent")
    print("=" * 60)
    print()

    if fail_count == 0:
        print("✓ Local linear systems are mostly CONSISTENT")
        print("  sub_premise_consistent appears SOUND")
        print()
        avg_cons = sum(r[3] for r in results) / len(results)
        avg_plant = sum(r[4] for r in results) / len(results)
        print(f"  Average consistency: {avg_cons:.1f}%")
        print(f"  Planted satisfies: {avg_plant:.1f}%")
    else:
        print("✗ Consistency issues detected!")
        print("  sub_premise_consistent is QUESTIONABLE")

    print()
    print("KEY INSIGHT:")
    print("  The XOR linearization of clause constraints is an APPROXIMATION.")
    print("  Real clauses are OR, not XOR. The planted solution may not")
    print("  exactly satisfy the linear system!")
    print()
    print("  This is a POTENTIAL FLAW in the proof if planted_rate < 100%")
    print()

    avg_plant = sum(r[4] for r in results) / len(results)
    if avg_plant < 95:
        print("=" * 60)
        print("⚠ WARNING: PLANTED SOLUTION DOESN'T ALWAYS SATISFY LINEAR SYSTEM")
        print("=" * 60)
        print()
        print("  The XOR linearization is NOT equivalent to the OR clauses.")
        print("  This means GE may find a solution that differs from planted!")
        print()
        print("  This is a SUBTLE GAP in the proof argument.")
        return 1
    else:
        print("Planted solution satisfies linear system: OK")
        return 0


if __name__ == "__main__":
    exit(main())
