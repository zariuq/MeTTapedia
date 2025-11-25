#!/usr/bin/env python3
"""
Check if Gemini's proposed counterexample can be completed to a valid graph.

The question: Can we add edges within V13 such that:
1. The graph remains triangle-free
2. No 6-independent set exists
3. The coverage property holds (every w in V13 has a neighbor in S5)
"""

import itertools
from typing import Set, Tuple, List

# Define the graph structure
S5 = {0, 1, 2, 3, 4}
V13 = {5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17}

# Edges from S5 to V13 (Gemini's construction)
S5_to_V13_edges = {
    0: {5, 6, 7, 8, 9},
    1: {10, 11, 12, 13, 14},
    2: {15, 16, 17, 5, 6},
    3: {7, 8, 9, 10, 11},
    4: {12, 13, 14, 15, 16},
}

def check_coverage():
    """Verify that every vertex in V13 is adjacent to at least one in S5."""
    covered = set()
    for v in S5:
        covered.update(S5_to_V13_edges[v])
    missing = V13 - covered
    print(f"Coverage check: {len(covered)}/{len(V13)} vertices covered")
    if missing:
        print(f"  Missing: {missing}")
        return False
    return True

def find_common_neighbors(w1, w2):
    """Find vertices in S5 that are adjacent to both w1 and w2."""
    common = set()
    for v in S5:
        if w1 in S5_to_V13_edges[v] and w2 in S5_to_V13_edges[v]:
            common.add(v)
    return common

def find_allowed_edges_in_V13():
    """
    Find which edges can exist in V13 without creating triangles.
    An edge (w1, w2) is allowed iff no vertex in S5 is adjacent to both w1 and w2.
    """
    allowed = set()
    forbidden = set()

    for w1, w2 in itertools.combinations(V13, 2):
        common = find_common_neighbors(w1, w2)
        if common:
            forbidden.add((w1, w2))
        else:
            allowed.add((w1, w2))

    print(f"\nAllowed edges in V13: {len(allowed)}")
    print(f"Forbidden edges in V13: {len(forbidden)}")
    return allowed, forbidden

def build_conflict_graph():
    """
    Build the 'conflict graph' where w1 ~ w2 if they share a common neighbor in S5.
    These vertices CANNOT be connected in V13 (would create triangle).
    """
    conflicts = {w: set() for w in V13}

    for w1, w2 in itertools.combinations(V13, 2):
        common = find_common_neighbors(w1, w2)
        if common:
            conflicts[w1].add(w2)
            conflicts[w2].add(w1)

    return conflicts

def find_max_independent_set_bruteforce(conflicts):
    """
    Find the maximum independent set in the conflict graph.
    This tells us: what's the largest set in V13 with no edges between them?

    If this is >= 6, then we have a 6-indep even if we add ALL allowed edges.
    """
    max_indep = []

    # Try all subsets of V13
    for k in range(len(V13), 0, -1):
        found = False
        for subset in itertools.combinations(V13, k):
            subset_set = set(subset)
            # Check if this is an independent set in the conflict graph
            is_indep = True
            for w1, w2 in itertools.combinations(subset, 2):
                if w2 in conflicts[w1]:
                    is_indep = False
                    break
            if is_indep:
                max_indep = list(subset)
                found = True
                break
        if found:
            break

    return max_indep

def check_independent_set_with_edges(indep_set, v13_edges):
    """Check if indep_set is still independent given v13_edges."""
    for w1, w2 in itertools.combinations(indep_set, 2):
        if (w1, w2) in v13_edges or (w2, w1) in v13_edges:
            return False
    return True

def find_min_edges_to_break_all_6indeps(allowed_edges, conflicts):
    """
    Find the minimum set of edges from V13 that need to be added
    to ensure no 6-independent set exists.
    """
    # Find all 6-subsets that are independent in the conflict graph
    potential_6indeps = []

    for subset in itertools.combinations(V13, 6):
        subset_set = set(subset)
        is_indep_in_conflict = True
        for w1, w2 in itertools.combinations(subset, 2):
            if w2 in conflicts[w1]:
                is_indep_in_conflict = False
                break
        if is_indep_in_conflict:
            potential_6indeps.append(subset)

    print(f"\nPotential 6-indep sets (without V13 edges): {len(potential_6indeps)}")

    if not potential_6indeps:
        print("  No 6-indep sets possible even without V13 edges!")
        return set()

    # For each potential 6-indep, we need at least one edge within it
    # This is a SET COVER problem (NP-hard)
    # For small instances, we can try all subsets

    # Greedy approach: add edges that break the most 6-indeps
    remaining_indeps = list(potential_6indeps)
    selected_edges = set()

    while remaining_indeps:
        # Count how many indeps each allowed edge breaks
        edge_scores = {}
        for edge in allowed_edges:
            if edge in selected_edges:
                continue
            score = 0
            for indep in remaining_indeps:
                if edge[0] in indep and edge[1] in indep:
                    score += 1
            edge_scores[edge] = score

        if not edge_scores or max(edge_scores.values()) == 0:
            print(f"  Cannot break all 6-indeps with allowed edges!")
            print(f"  Remaining unbreakable 6-indeps: {len(remaining_indeps)}")
            return None

        # Pick the edge with the highest score
        best_edge = max(edge_scores, key=edge_scores.get)
        selected_edges.add(best_edge)

        # Remove broken indeps
        remaining_indeps = [
            indep for indep in remaining_indeps
            if not (best_edge[0] in indep and best_edge[1] in indep)
        ]

        print(f"  Added edge {best_edge}, breaks {edge_scores[best_edge]} indeps, {len(remaining_indeps)} remaining")

    return selected_edges

def main():
    print("=" * 80)
    print("CHECKING GEMINI'S COUNTEREXAMPLE")
    print("=" * 80)

    # Step 1: Check coverage
    print("\n[1] Checking coverage...")
    if not check_coverage():
        print("  ❌ Coverage check FAILED")
        return
    print("  ✅ Coverage check PASSED")

    # Step 2: Find allowed edges
    print("\n[2] Finding allowed edges in V13...")
    allowed, forbidden = find_allowed_edges_in_V13()

    # Step 3: Build conflict graph
    print("\n[3] Building conflict graph...")
    conflicts = build_conflict_graph()

    # Print conflict degrees
    print("\nConflict degrees (vertices that CANNOT be connected):")
    for w in sorted(V13):
        print(f"  {w}: {len(conflicts[w])} conflicts")

    # Step 4: Find maximum independent set in conflict graph
    print("\n[4] Finding maximum independent set in conflict graph...")
    print("    (This is the largest set with no edges even if we add ALL allowed edges)")
    max_indep = find_max_independent_set_bruteforce(conflicts)
    print(f"\nMaximum independent set in conflict graph: {len(max_indep)} vertices")
    print(f"  {max_indep}")

    if len(max_indep) >= 6:
        print(f"\n  ⚠️  Max indep >= 6: Even with ALL allowed edges, we have a {len(max_indep)}-indep!")
        print(f"  This means Gemini's counterexample FAILS the no_k_indep condition.")
        print(f"\n  ❌ COUNTEREXAMPLE IS INVALID")
        return

    # Step 5: Try to find edges that prevent all 6-indeps
    print("\n[5] Finding edges to prevent all 6-indep sets...")
    needed_edges = find_min_edges_to_break_all_6indeps(allowed, conflicts)

    if needed_edges is None:
        print("\n  ❌ CANNOT break all 6-indeps with allowed edges")
        print("  Gemini's counterexample is INVALID")
    else:
        print(f"\n  ✅ Found {len(needed_edges)} edges that prevent all 6-indeps:")
        for edge in sorted(needed_edges):
            print(f"    {edge}")
        print("\n  ⚠️  This means Gemini's counterexample COULD BE VALID")
        print("  (But we need to verify triangle-free property carefully)")

if __name__ == "__main__":
    main()
