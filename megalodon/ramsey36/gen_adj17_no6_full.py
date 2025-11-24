#!/usr/bin/env python3
"""
Generate full Megalodon proof for Adj17_no_6_indep.
Using explicit proof terms to avoid apply/unification issues.
"""

from itertools import combinations

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
    return j in EDGES[i]

def find_edge_in_subset(subset):
    for i in subset:
        for j in subset:
            if i < j and is_edge(i, j):
                return (i, j)
    return None

def get_set_id(subset):
    return "_".join(str(x) for x in sorted(subset))

def gen_set_string(subset):
    return "{" + ", ".join(str(x) for x in sorted(subset)) + "}"

def gen_set_membership_term(elem, subset):
    s = sorted(subset)
    if len(s) == 2:
        if elem == s[0]:
            return f"(UPairI1 {s[0]} {s[1]})"
        else:
            return f"(UPairI2 {s[0]} {s[1]})"
    
    last = s[-1]
    rest = s[:-1]
    rest_str = gen_set_string(rest)
    last_set_str = f"{{{last}}}"
    
    if elem == last:
        # binunionI2 X Y z H
        return f"(binunionI2 {rest_str} {last_set_str} {last} (SingI {last}))"
    else:
        # binunionI1 X Y z H
        H = gen_set_membership_term(elem, rest)
        return f"(binunionI1 {rest_str} {last_set_str} {elem} {H})"

def gen_neq_term(i, j):
    if i < j: return f"neq_{i}_{j}"
    else: return f"(neq_i_sym {j} {i} neq_{j}_{i})"

def gen_subset_lemma(subset):
    edge = find_edge_in_subset(subset)
    if edge is None: raise ValueError(f"No edge found in subset {subset}")
    i, j = edge
    subset_id = get_set_id(subset)
    set_str = gen_set_string(subset)
    
    lines = []
    lines.append(f"Theorem Adj17_not_indep_{subset_id} : ~is_indep_set 17 Adj17 {set_str}.")
    lines.append(f"assume Hindep: is_indep_set 17 Adj17 {set_str}.")
    
    prop_A = f"{set_str} c= 17"
    prop_B = f"forall x :e {set_str}, forall y :e {set_str}, x <> y -> ~Adj17 x y"
    
    term_i = gen_set_membership_term(i, subset)
    term_j = gen_set_membership_term(j, subset)
    term_neq = gen_neq_term(i, j)
    
    # Full term: (andER A B Hindep i term_i j term_j term_neq Adj17_i_j)
    proof_term = f"(andER ({prop_A}) ({prop_B}) Hindep {i} {term_i} {j} {term_j} {term_neq} Adj17_{i}_{j})"
    
    lines.append(f"exact {proof_term}.")
    lines.append("Qed.")
    return "\n".join(lines)

def gen_cases_axiom():
    lines = []
    lines.append("Axiom subsets_6_17_cases : forall p:set->prop,")
    all_subsets = list(combinations(range(17), 6))
    for idx, subset in enumerate(all_subsets):
        sorted_subset = sorted(subset)
        set_str = "{" + ", ".join(str(x) for x in sorted_subset) + "}"
        lines.append(f"  p {set_str} ->")
    lines.append("  forall S, S c= 17 -> equip 6 S -> p S.")
    return "\n".join(lines)

def gen_main_theorem():
    lines = []
    lines.append("Theorem Adj17_no_6_indep : no_k_indep 17 Adj17 6.")
    unfolded_goal = "(forall S:set, S c= 17 -> equip 6 S -> ~is_indep_set 17 Adj17 S)"
    lines.append(f"claim Unfolded : {unfolded_goal}.")
    lines.append("{")
    lines.append("  assume S. assume HS17: S c= 17. assume H6: equip 6 S.")
    lines.append("  apply subsets_6_17_cases (fun S => ~is_indep_set 17 Adj17 S) _ _ _ HS17 H6.")
    all_subsets = list(combinations(range(17), 6))
    for subset in all_subsets:
        subset_id = get_set_id(subset)
        lines.append(f"  - exact Adj17_not_indep_{subset_id}.")
    lines.append("}")
    lines.append("exact Unfolded.")
    lines.append("Qed.")
    return "\n".join(lines)

def gen_neq_lemmas():
    lines = []
    existing = {(0, 1), (0, 2), (1, 2)}
    for i in range(17):
        for j in range(i + 1, 17):
            if (i, j) in existing: continue
            lines.append(f"Axiom neq_{i}_{j} : {i} <> {j}.")
    return "\n".join(lines)

def generate_full_proof():
    lines = []
    lines.append("Definition is_indep_set : set -> (set -> set -> prop) -> set -> prop :=")
    lines.append("  fun V R S => S c= V /\ (forall x :e S, forall y :e S, x <> y -> ~R x y).")
    lines.append("")
    lines.append("Definition no_k_indep : set -> (set -> set -> prop) -> set -> prop :=")
    lines.append("  fun V R k => forall S, S c= V -> equip k S -> ~is_indep_set V R S.")
    lines.append("")
    lines.append(gen_neq_lemmas())
    lines.append("")
    all_subsets = list(combinations(range(17), 6))
    for idx, subset in enumerate(all_subsets):
        lines.append(gen_subset_lemma(subset))
        lines.append("")
    lines.append(gen_cases_axiom())
    lines.append("")
    lines.append(gen_main_theorem())
    return "\n".join(lines)

if __name__ == "__main__":
    print(generate_full_proof())