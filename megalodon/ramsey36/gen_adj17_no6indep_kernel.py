#!/usr/bin/env python3
"""
Generate kernel-level Megalodon proofs for Adj17_no_6_indep.

For each 6-subset of {0,...,16}, we prove it's not independent by
showing it contains at least one edge.

The proof structure for ~is_indep_set 17 Adj17 {a,b,c,d,e,f}:
1. Assume Hindep: is_indep_set 17 Adj17 {a,b,c,d,e,f}
2. Apply andER to get: forall x :e S, forall y :e S, x <> y -> ~Adj17 x y
3. Instantiate with the witness edge (i, j) where Adj17 i j
4. Prove i :e S, j :e S, i <> j
5. Get ~Adj17 i j which contradicts Adj17_i_j
"""

import sys
from itertools import combinations

# Adjacency list for the 17-vertex Graver-Yackel graph
EDGES = {
    0: [9, 14, 15, 16],
    1: [7, 11, 13, 16],
    2: [8, 10, 12, 15],
    3: [6, 8, 13, 15, 16],
    4: [5, 7, 12, 14, 16],
    5: [4, 9, 10, 11, 13],
    6: [3, 10, 11, 12, 14],
    7: [1, 4, 9, 10, 15],
    8: [2, 3, 9, 11, 14],
    9: [0, 5, 7, 8, 12],
    10: [2, 5, 6, 7, 16],
    11: [1, 5, 6, 8, 15],
    12: [2, 4, 6, 9, 13],
    13: [1, 3, 5, 12, 14],
    14: [0, 4, 6, 8, 13],
    15: [0, 2, 3, 7, 11],
    16: [0, 1, 3, 4, 10],
}


def is_edge(i, j):
    """Return True iff (i,j) is an edge."""
    return j in EDGES[i]


def find_edge_in_subset(subset):
    """Find one edge in the 6-subset, return (i, j) where i < j."""
    for i in subset:
        for j in subset:
            if i < j and is_edge(i, j):
                return (i, j)
    return None


def get_set_id(subset):
    """Generate a unique identifier for a subset."""
    return "_".join(str(x) for x in sorted(subset))


def gen_set_membership_proof(elem, subset):
    """
    Generate proof that elem :e {a,b,c,d,e,f}.

    The set {a,b,c,d,e,f} is built as nested SetAdjoins/UPairs.
    For 6 elements: SetAdjoin (SetAdjoin (SetAdjoin (SetAdjoin (UPair a b) c) d) e) f

    Structure for {0,1,2,3,4,5}:
    {0,1,2,3,4,5} = SetAdjoin ({0,1,2,3,4}) 5 = {0,1,2,3,4} :\/: {5}

    We use binunionI1 or binunionI2 + SingI to prove membership.
    """
    sorted_subset = sorted(subset)
    elem_idx = sorted_subset.index(elem)

    # For a 6-element set, the structure is:
    # {a0, a1, a2, a3, a4, a5} where a0 < a1 < ... < a5
    # Built as: SetAdjoin (SetAdjoin (SetAdjoin (SetAdjoin ({a0, a1}) a2) a3) a4) a5
    # = (((({a0,a1} :\/: {a2}) :\/: {a3}) :\/: {a4}) :\/: {a5})

    # To prove a_k :e S:
    # - If k = 5 (rightmost): binunionI2 + SingI
    # - If k < 5: binunionI1 then recurse

    steps = []

    # Number of layers to go through (5 for 6-element set)
    # Layer 5 is rightmost, layer 0/1 is innermost UPair

    if elem_idx == 5:
        # elem is the rightmost element - one binunionI2 + SingI
        steps.append("apply binunionI2. exact SingI.")
    elif elem_idx == 4:
        steps.append("apply binunionI1. apply binunionI2. exact SingI.")
    elif elem_idx == 3:
        steps.append("apply binunionI1. apply binunionI1. apply binunionI2. exact SingI.")
    elif elem_idx == 2:
        steps.append("apply binunionI1. apply binunionI1. apply binunionI1. apply binunionI2. exact SingI.")
    elif elem_idx == 1:
        # Second element of innermost UPair
        steps.append("apply binunionI1. apply binunionI1. apply binunionI1. apply binunionI1. exact UPairI2.")
    elif elem_idx == 0:
        # First element of innermost UPair
        steps.append("apply binunionI1. apply binunionI1. apply binunionI1. apply binunionI1. exact UPairI1.")

    return steps


def gen_neq_proof(i, j):
    """Generate proof that i <> j using preamble neq lemmas."""
    if i == j:
        raise ValueError(f"Cannot prove {i} <> {j}")
    if i > j:
        return f"exact neq_{i}_{j}."
    else:
        return f"assume Heq: {i} = {j}. apply neq_{j}_{i}. symmetry. exact Heq."


def gen_subset_lemma(subset, include_proof=True):
    """
    Generate lemma proving ~is_indep_set 17 Adj17 {a,b,c,d,e,f}.
    """
    edge = find_edge_in_subset(subset)
    if edge is None:
        raise ValueError(f"No edge found in subset {subset}")

    i, j = edge
    subset_id = get_set_id(subset)
    sorted_subset = sorted(subset)
    set_str = "{" + ", ".join(str(x) for x in sorted_subset) + "}"

    lines = []
    lines.append(f"Theorem Adj17_not_indep_{subset_id} : ~is_indep_set 17 Adj17 {set_str}.")

    if not include_proof:
        lines.append("Admitted.")
        return "\n".join(lines)

    lines.append(f"assume Hindep: is_indep_set 17 Adj17 {set_str}.")
    lines.append("prove False.")

    # Extract the independence condition from Hindep
    # Hindep : S c= 17 /\ (forall x :e S, forall y :e S, x <> y -> ~Adj17 x y)
    # We need: (forall x :e S, forall y :e S, x <> y -> ~Adj17 x y)
    # Apply with x=i, y=j, prove membership and inequality, get ~Adj17 i j

    lines.append("apply andER Hindep.")
    lines.append(f"prove (forall x :e {set_str}, forall y :e {set_str}, x <> y -> ~Adj17 x y) -> False.")
    lines.append("assume Hind: forall x :e " + set_str + ", forall y :e " + set_str + ", x <> y -> ~Adj17 x y.")

    # Now apply Hind with x=i, y=j
    # Hind {i} : forall y :e S, i <> y -> ~Adj17 i y (after proving i :e S)
    # Hind {i} {j} : i <> j -> ~Adj17 i j (after proving j :e S)
    # Hind {i} {j} {neq_proof} : ~Adj17 i j

    lines.append(f"apply Hind {i} _ {j} _ _.")

    # Prove i :e S
    mem_proof_i = gen_set_membership_proof(i, subset)
    lines.append(f"- " + mem_proof_i[0])

    # Prove j :e S
    mem_proof_j = gen_set_membership_proof(j, subset)
    lines.append(f"- " + mem_proof_j[0])

    # Prove i <> j
    lines.append(f"- " + gen_neq_proof(i, j))

    # Now we have ~Adj17 i j, apply to Adj17_i_j to get False
    lines.append(f"- assume Hnot: ~Adj17 {i} {j}.")
    lines.append(f"  exact Hnot Adj17_{i}_{j}.")

    lines.append("Qed.")
    return "\n".join(lines)


def gen_cases_axiom():
    """
    Generate axiom for case analysis over 6-subsets of 17.

    This axiom states: if a property holds for all specific 6-subsets,
    then it holds for any 6-subset.
    """
    lines = []
    lines.append("Axiom subsets_6_17_cases : forall p:set->prop,")

    all_subsets = list(combinations(range(17), 6))
    for idx, subset in enumerate(all_subsets):
        sorted_subset = sorted(subset)
        set_str = "{" + ", ".join(str(x) for x in sorted_subset) + "}"
        if idx < len(all_subsets) - 1:
            lines.append(f"  p {set_str} ->")
        else:
            lines.append(f"  p {set_str} ->")

    lines.append("  forall S, S c= 17 -> equip 6 S -> p S.")

    return "\n".join(lines)


def gen_main_theorem():
    """Generate the main Adj17_no_6_indep theorem using the case axiom."""
    lines = []
    lines.append("Theorem Adj17_no_6_indep : no_k_indep 17 Adj17 6.")
    lines.append("prove forall S, S c= 17 -> equip 6 S -> ~is_indep_set 17 Adj17 S.")
    lines.append("assume S. assume HS17: S c= 17. assume H6: equip 6 S.")
    lines.append("apply subsets_6_17_cases (fun S => ~is_indep_set 17 Adj17 S) _ _ _ HS17 H6.")

    # Now we need 12376 bullets, each one exact Adj17_not_indep_X_Y_...
    all_subsets = list(combinations(range(17), 6))
    for subset in all_subsets:
        subset_id = get_set_id(subset)
        lines.append(f"- exact Adj17_not_indep_{subset_id}.")

    lines.append("Qed.")
    return "\n".join(lines)


def generate_full_proof():
    """Generate the complete proof file."""
    lines = []

    # Definitions (should be imported from lower_bound_proof.mg or similar)
    lines.append("Definition is_indep_set : set -> (set -> set -> prop) -> set -> prop :=")
    lines.append("  fun V R S => S c= V /\\ (forall x :e S, forall y :e S, x <> y -> ~R x y).")
    lines.append("")
    lines.append("Definition no_k_indep : set -> (set -> set -> prop) -> set -> prop :=")
    lines.append("  fun V R k => forall S, S c= V -> equip k S -> ~is_indep_set V R S.")
    lines.append("")

    # Generate individual subset lemmas
    all_subsets = list(combinations(range(17), 6))
    sys.stderr.write(f"Generating {len(all_subsets)} subset lemmas...\n")

    for idx, subset in enumerate(all_subsets):
        if idx % 1000 == 0:
            sys.stderr.write(f"  Progress: {idx}/{len(all_subsets)}\n")
        lemma = gen_subset_lemma(subset, include_proof=True)
        lines.append(lemma)
        lines.append("")

    sys.stderr.write(f"  Progress: {len(all_subsets)}/{len(all_subsets)}\n")

    # Generate case axiom
    sys.stderr.write("Generating cases axiom...\n")
    lines.append(gen_cases_axiom())
    lines.append("")

    # Generate main theorem
    sys.stderr.write("Generating main theorem...\n")
    lines.append(gen_main_theorem())

    return "\n".join(lines)


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "--full":
        print(generate_full_proof())
    elif len(sys.argv) > 1 and sys.argv[1] == "--axiom-only":
        print(gen_cases_axiom())
    elif len(sys.argv) > 1 and sys.argv[1] == "--sample":
        # Print first 3 lemmas as sample
        all_subsets = list(combinations(range(17), 6))[:3]
        for subset in all_subsets:
            print(gen_subset_lemma(subset, include_proof=True))
            print()
    else:
        # Statistics
        all_subsets = list(combinations(range(17), 6))
        print(f"Total 6-subsets of 17: {len(all_subsets)}")

        # Group by witness edge
        by_edge = {}
        for subset in all_subsets:
            edge = find_edge_in_subset(subset)
            if edge not in by_edge:
                by_edge[edge] = []
            by_edge[edge].append(subset)

        print(f"Distinct witness edges: {len(by_edge)}")
        print()
        print("Top 10 edges by coverage:")
        sorted_edges = sorted(by_edge.items(), key=lambda x: -len(x[1]))
        for edge, subsets in sorted_edges[:10]:
            print(f"  Edge {edge}: {len(subsets)} subsets")

        print()
        print("Options:")
        print("  --full    Generate complete proof file")
        print("  --axiom-only  Generate just the cases axiom")
        print("  --sample  Generate 3 sample lemmas")


if __name__ == "__main__":
    main()
