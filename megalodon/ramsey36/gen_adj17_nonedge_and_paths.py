#!/usr/bin/env python3
"""
Generate kernel-level Megalodon proofs for the 17-vertex Graver–Yackel graph.

Outputs:
  1. Non-edge refutations: ~Adj17 i j for all 190 ordered non-edges.
  2. Two-edge path lemmas: Adj17 i j -> Adj17 j k -> ~Adj17 i k for
     every path i–j–k whose endpoints are a non-edge (316 lemmas).

The generated proofs match the Adj17 definition in adj17_with_sym.mg and the
3-disjunct OR-elimination pattern demonstrated in test_simple_or3.mg.

Usage:
    python3 gen_adj17_nonedge_and_paths.py > adj17_generated_proofs.mg
    ./bin/megalodon -I preamble.mgs adj17_with_sym.mg adj17_generated_proofs.mg

Adjust the get_neq_lemma helper if your inequality lemmas are oriented
otherwise than "neq_a_b".
"""

# ---------------------------------------------------------------------------
# Graph data (must match Adj17 definition)
# ---------------------------------------------------------------------------

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

VERTICES = list(range(17))


def is_edge(i, j):
    """Return True iff (i,j) is an edge according to EDGES."""
    return j in EDGES[i]


# ---------------------------------------------------------------------------
# Inequality lemma names
# ---------------------------------------------------------------------------

def get_neq_lemma(a, b):
    """Return (lemma_name, orientation_matches_eq?).

    The bundled neq_lemmas.mg supplies neq_{n}_{m} lemmas with the **larger
    numeral first** (e.g., neq_14_1 instead of neq_1_14). To avoid missing
    lemmas we always pick that orientation and track whether it already matches
    the assumed equality direction.
    """

    if a >= b:
        return f"neq_{a}_{b}", True
    return f"neq_{b}_{a}", False


# ---------------------------------------------------------------------------
# Utilities for structured Megalodon proofs
# ---------------------------------------------------------------------------

BULLETS = ["-", "+", "*"]  # reused cyclically at different nesting levels


def gen_eq_contra(x, y, eq_name, indent=""):
    """Discharge an impossible equality using the oriented neq_* lemma.

    If the lemma orientation matches the assumption, we apply it directly.
    Otherwise, we synthesize the symmetric equality via rewriting and feed
    that to the available lemma.
    """

    lemma, oriented = get_neq_lemma(x, y)
    if oriented:
        return [f"{indent}exact {lemma} {eq_name}."]

    return [
        f"{indent}have Hsym: {max(x, y)} = {min(x, y)}.",
        f"{indent}  rewrite {eq_name}.",
        f"{indent}  reflexivity.",
        f"{indent}exact {lemma} Hsym.",
    ]


# ---------------------------------------------------------------------------
# Inner disjunction over j's neighbors (for i = idx case)
# ---------------------------------------------------------------------------

def gen_inner_j_or_elim(vertex_j, neighbors, indent="", level=0):
    """
    Generate elimination of a left-associative disjunction

      (j = n0 \/ j = n1 \/ ... \/ j = nk)

    encoded as (((j=n0 \/ j=n1) \/ ...) \/ j=nk).

    We assume we are *after* writing:

      assume Hj.
      apply Hj.

    So Hj has type "that disjunction", and we now produce branches.
    """
    lines = []
    bullet = BULLETS[level % len(BULLETS)]

    if len(neighbors) == 1:
        n = neighbors[0]
        # Base case: j = n -> False
        lines.append(f"{indent}{bullet} assume Heq: {vertex_j} = {n}.")
        lines.extend(gen_eq_contra(vertex_j, n, "Heq", indent + "  "))
        return lines

    # Recursive case: split into left (all but last) and right (last)
    left = neighbors[:-1]
    right = neighbors[-1]

    # Left: nested disjunction of all but last neighbor
    lines.append(f"{indent}{bullet} assume Hleft.")
    lines.append(f"{indent}  apply Hleft.")
    lines.extend(gen_inner_j_or_elim(vertex_j, left, indent + "  ", level + 1))

    # Right: final neighbor
    lines.append(f"{indent}{bullet} assume Heq: {vertex_j} = {right}.")
    lines.extend(gen_eq_contra(vertex_j, right, "Heq", indent + "  "))

    return lines


# ---------------------------------------------------------------------------
# Single outer disjunct (i = idx /\ (j in neighbors))
# ---------------------------------------------------------------------------

def generate_disjunct_proof(vertex_i, vertex_j, idx, indent=""):
    """
    Given one disjunct of Adj17:

      (vertex_i = idx /\ (vertex_j = n1 \/ ... \/ vertex_j = nk))

    produce code (under "apply Hd_idx.") that derives False in all cases.
    """
    neighbors = EDGES[idx]
    lines = []

    # Conjunction elimination: first "i = idx", then "j in neighbors"
    lines.append(f"{indent}assume Heq_i: {vertex_i} = {idx}.")
    lines.append(f"{indent}assume Hj.")

    if vertex_i == idx:
        # First conjunct could be true; we must refute the inner disjunction
        lines.append(f"{indent}apply Hj.")
        lines.extend(gen_inner_j_or_elim(vertex_j, neighbors, indent, level=0))
    else:
        # i <> idx, so "vertex_i = idx" already contradicts inequality
        lines.extend(gen_eq_contra(vertex_i, idx, "Heq_i", indent))

    return lines


# ---------------------------------------------------------------------------
# Outer disjunction over 17 disjuncts (Adj17 definition)
# ---------------------------------------------------------------------------

def gen_outer_or_elim(vertex_i, vertex_j, disjunct_indices, indent="", level=0):
    """
    Eliminate the left-associative OR over all 17 disjuncts in Adj17.

    Called immediately after:

      assume H: Adj17 i j.
      prove False.
      apply H.

    so H has the full disjunction type.
    """
    lines = []
    bullet = BULLETS[level % len(BULLETS)]

    if len(disjunct_indices) == 1:
        idx = disjunct_indices[0]
        # Last disjunct is a single conjunction
        lines.append(f"{indent}assume Hd{idx}.")
        lines.append(f"{indent}apply Hd{idx}.")
        lines.extend(generate_disjunct_proof(vertex_i, vertex_j, idx, indent))
        return lines

    # Split into nested left disjunction and last disjunct
    left = disjunct_indices[:-1]
    right = disjunct_indices[-1]

    # Left branch: nested disjunction of all but last
    lines.append(f"{indent}{bullet} assume Hleft.")
    lines.append(f"{indent}  apply Hleft.")
    lines.extend(gen_outer_or_elim(vertex_i, vertex_j, left, indent + "  ", level + 1))

    # Right branch: final disjunct
    lines.append(f"{indent}{bullet} assume Hd{right}.")
    lines.append(f"{indent}  apply Hd{right}.")
    lines.extend(generate_disjunct_proof(vertex_i, vertex_j, right, indent + "  "))

    return lines


# ---------------------------------------------------------------------------
# ~Adj17 i j for all non-edges
# ---------------------------------------------------------------------------

def generate_not_adj_proof(i, j):
    """
    Generate a full Megalodon proof of:

      Theorem Adj17_not_i_j : ~Adj17 i j.
    """
    if i == j:
        return None
    if is_edge(i, j):
        return None  # can't prove ~Adj17 i j for an actual edge

    lines = []
    lines.append(f"Theorem Adj17_not_{i}_{j} : ~Adj17 {i} {j}.")
    lines.append(f"assume H: Adj17 {i} {j}.")
    lines.append("prove False.")
    lines.append("apply H.")
    lines.extend(gen_outer_or_elim(i, j, list(range(17)), indent="", level=0))
    lines.append("Qed.")
    lines.append("")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Two-edge path lemmas: Adj17 i j -> Adj17 j k -> ~Adj17 i k
# ---------------------------------------------------------------------------

def generate_path_triangle_free_lemma(i, j, k):
    """
    For a path i - j - k with i != k and (i,k) a non-edge, generate:

      Theorem Adj17_triangle_free_i_j_k :
        Adj17 i j -> Adj17 j k -> ~Adj17 i k.

    Proof just uses the corresponding ~Adj17_i_k lemma.
    """
    if not is_edge(i, j):
        return None
    if not is_edge(j, k):
        return None
    if i == k:
        return None
    if is_edge(i, k):
        # If this ever triggers, the graph isn't triangle-free.
        raise ValueError(f"Triangle detected on vertices {i}, {j}, {k}")
    # (i,k) is a non-edge, so Adj17_not_i_k should exist
    lines = []
    lines.append(f"Theorem Adj17_triangle_free_{i}_{j}_{k} :")
    lines.append(f"  Adj17 {i} {j} -> Adj17 {j} {k} -> ~Adj17 {i} {k}.")
    lines.append(f"assume H1: Adj17 {i} {j}.")
    lines.append(f"assume H2: Adj17 {j} {k}.")
    lines.append(f"assume H3: Adj17 {i} {k}.")
    lines.append(f"exact (Adj17_not_{i}_{k} H3).")
    lines.append("Qed.")
    lines.append("")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    all_chunks = []

    # 1. Non-edge proofs
    nonedge_count = 0
    for i in VERTICES:
        for j in VERTICES:
            proof = generate_not_adj_proof(i, j)
            if proof is not None:
                all_chunks.append(proof)
                nonedge_count += 1

    # 2. Two-edge path lemmas
    path_count = 0
    seen_paths = set()
    for i in VERTICES:
        for j in EDGES[i]:
            for k in EDGES[j]:
                key = (i, j, k)
                if key in seen_paths:
                    continue
                lemma = generate_path_triangle_free_lemma(i, j, k)
                if lemma is not None:
                    seen_paths.add(key)
                    all_chunks.append(lemma)
                    path_count += 1

    print(f"(* Generated {nonedge_count} non-edge proofs and "
          f"{path_count} path lemmas for Adj17. *)")
    print("")
    for chunk in all_chunks:
        print(chunk)


if __name__ == "__main__":
    main()
