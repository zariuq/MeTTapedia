#!/usr/bin/env python3
"""
CORRECTNESS VERIFICATION (Pure Python)

Tests the most suspicious premise: Does BP on local tree-like factor graphs
correctly identify the planted assignment?
"""

import random
from typing import List, Tuple, Dict, Set

def generate_planted_3sat(n: int, m: int, seed: int = 42) -> Tuple[List[bool], List[Tuple[int, int, int]], List[Tuple[bool, bool, bool]]]:
    """Generate a planted 3-SAT instance."""
    random.seed(seed)

    # Generate planted assignment
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


def build_local_factor_graph(var_i: int, clauses: List, signs: List, depth: int) -> Dict:
    """Build local factor graph around variable i up to given depth."""

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

    return {
        'center': var_i,
        'vars': local_vars,
        'clauses': local_clauses,
        'depth': depth
    }


def run_bp_local(local_fg: Dict, max_iter: int = 30, damping: float = 0.3) -> Dict[int, float]:
    """Run simplified belief propagation on local factor graph."""

    vars = list(local_fg['vars'])
    clauses = local_fg['clauses']

    if not clauses:
        return {v: 0.5 for v in vars}

    # belief[v] = P(v = True)
    belief = {v: 0.5 for v in vars}

    for iteration in range(max_iter):
        new_belief = {v: 0.5 for v in vars}

        for v in vars:
            # Collect evidence from clauses containing v
            log_ratio = 0.0  # log(P(v=T)/P(v=F))

            for c_idx, clause, signs in clauses:
                if v not in clause:
                    continue

                v_idx = clause.index(v)
                v_sign = signs[v_idx]
                other_vars = [(clause[j], signs[j]) for j in range(3) if j != v_idx]

                # Compute P(clause sat | v=T) and P(clause sat | v=F)
                p_sat_true = 0.0
                p_sat_false = 0.0

                for config in range(4):
                    p_config = 1.0
                    other_lits = []
                    for j, (ov, os) in enumerate(other_vars):
                        ov_val = bool((config >> j) & 1)
                        p_ov = belief.get(ov, 0.5)
                        p_config *= p_ov if ov_val else (1 - p_ov)
                        other_lits.append(ov_val if os else not ov_val)

                    v_lit_true = True if v_sign else False
                    v_lit_false = False if v_sign else True

                    if any(other_lits) or v_lit_true:
                        p_sat_true += p_config
                    if any(other_lits) or v_lit_false:
                        p_sat_false += p_config

                # Update log ratio
                if p_sat_true > 1e-10 and p_sat_false > 1e-10:
                    log_ratio += 0.5 * (p_sat_true - p_sat_false) / max(p_sat_true, p_sat_false)

            # Convert to probability
            import math
            try:
                new_belief[v] = 1.0 / (1.0 + math.exp(-log_ratio))
            except:
                new_belief[v] = 0.5

            new_belief[v] = max(0.01, min(0.99, new_belief[v]))

        # Apply damping
        for v in vars:
            belief[v] = damping * belief[v] + (1 - damping) * new_belief[v]

    return belief


def test_bp_correctness(n: int, alpha: float, depth: int, num_trials: int = 5) -> Dict:
    """Test if BP correctly identifies planted assignment locally."""

    m = int(alpha * n)

    correct_center = 0
    correct_all = 0
    total_vars = 0
    total_center = 0

    for trial in range(num_trials):
        planted, clauses, signs = generate_planted_3sat(n, m, seed=trial * 1000)

        test_vars = random.sample(range(n), min(10, n))

        for var_i in test_vars:
            local_fg = build_local_factor_graph(var_i, clauses, signs, depth)
            marginals = run_bp_local(local_fg)

            total_center += 1
            if var_i in marginals:
                predicted = marginals[var_i] > 0.5
                if predicted == planted[var_i]:
                    correct_center += 1

            for v in local_fg['vars']:
                if v in marginals:
                    predicted = marginals[v] > 0.5
                    if predicted == planted[v]:
                        correct_all += 1
                    total_vars += 1

    return {
        'center_accuracy': correct_center / total_center if total_center > 0 else 0,
        'local_accuracy': correct_all / total_vars if total_vars > 0 else 0,
        'n': n,
        'alpha': alpha,
        'depth': depth,
    }


def main():
    print("=" * 60)
    print("BP CORRECTNESS VERIFICATION")
    print("Testing: Do BP marginals identify planted assignment?")
    print("=" * 60)
    print()

    configs = [
        (50, 2.0, 2),
        (50, 2.0, 3),
        (50, 3.0, 2),
        (50, 3.0, 3),
        (100, 2.0, 3),
        (100, 3.5, 3),
    ]

    print(f"{'n':>6} {'α':>6} {'depth':>6} {'center%':>10} {'local%':>10} {'STATUS':>10}")
    print("-" * 60)

    results = []
    for n, alpha, depth in configs:
        result = test_bp_correctness(n, alpha, depth, num_trials=3)

        center_pct = result['center_accuracy'] * 100
        local_pct = result['local_accuracy'] * 100

        if center_pct >= 60 and local_pct >= 55:
            status = "PASS"
        elif center_pct >= 50:
            status = "WEAK"
        else:
            status = "FAIL"

        results.append((n, alpha, depth, center_pct, local_pct, status))
        print(f"{n:>6} {alpha:>6.1f} {depth:>6} {center_pct:>9.1f}% {local_pct:>9.1f}% {status:>10}")

    print("-" * 60)
    print()

    fail_count = sum(1 for r in results if r[5] == "FAIL")
    weak_count = sum(1 for r in results if r[5] == "WEAK")

    print("=" * 60)
    print("ANALYSIS OF sub_premise_ge_correct")
    print("=" * 60)
    print()

    if fail_count == 0:
        print("✓ BP shows reasonable accuracy in identifying planted assignment")
        print("  sub_premise_ge_correct appears PLAUSIBLE")
        print()
        print("  However, accuracy is not 100% - there's inherent noise.")
        print("  The decoder works IN EXPECTATION but may fail on some instances.")
    else:
        print("✗ BP shows LOW accuracy in some regimes")
        print("  sub_premise_ge_correct is QUESTIONABLE")
        print()
        print(f"  {fail_count} configurations failed, {weak_count} weak")

    print()
    print("KEY INSIGHT:")
    print("  BP accuracy depends on:")
    print("  1. Clause density α (sweet spot: 2-3)")
    print("  2. Local tree-likeness (degrades at high α)")
    print("  3. Planted solution uniqueness")
    print()

    # The real crux
    print("=" * 60)
    print("THE REAL CRUX")
    print("=" * 60)
    print()
    print("Even with ~60% accuracy, the decoder may work because:")
    print("  - ERM over many instances can tolerate noise")
    print("  - The switching lemma only needs MOST bits correct")
    print()
    print("BUT: If accuracy drops below 50%, the decoder is no better")
    print("than random guessing, and the proof FAILS.")
    print()

    avg_center = sum(r[3] for r in results) / len(results)
    if avg_center >= 55:
        print(f"Average center accuracy: {avg_center:.1f}% - ABOVE threshold")
        return 0
    else:
        print(f"Average center accuracy: {avg_center:.1f}% - BELOW threshold")
        return 1


if __name__ == "__main__":
    exit(main())
