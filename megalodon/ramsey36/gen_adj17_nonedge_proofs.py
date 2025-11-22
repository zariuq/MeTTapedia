#!/usr/bin/env python3
"""
Generate Megalodon proofs for:
  1. ~Adj17 i j for all 190 non-edges (i != j, not edge(i,j))
  2. Path lemmas: Adj17 i j -> Adj17 j k -> ~Adj17 i k
     for all two-edge paths i - j - k with (i,k) a non-edge.

Based on the Adj17 definition in adj17_with_sym.mg and the working
3-disjunct negation pattern from test_simple_or3.mg.

The Adj17 definition is a left-associative 17-way disjunction:
  ((((P0 \/ P1) \/ P2) \/ ...) \/ P16)
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
# Inequality lemma proof steps
# ---------------------------------------------------------------------------

def get_neq_lemma_direct(a, b, eq_hyp):
    """
    Return the proof step to contradict eq_hyp : a = b.

    The preamble has neq_X_Y where X > Y.
    """
    if a == b:
        raise ValueError(f"Cannot contradict a = a for {a}")
    if a > b:
        return f"exact neq_{a}_{b} {eq_hyp}."
    else:
        return f"apply neq_{b}_{a}. symmetry. exact {eq_hyp}."


# ---------------------------------------------------------------------------
# Helper: Generate formulas
# ---------------------------------------------------------------------------

def gen_neighbor_disj(v, j_var):
    """Generate (j = n1 \/ j = n2 \/ ... \/ j = nk) for neighbors of v."""
    neighbors = EDGES[v]
    return " \\/ ".join(f"{j_var} = {n}" for n in neighbors)


def gen_vertex_clause(v, i_val, j_val):
    """Generate the clause for vertex v: (i = v /\ (j = n1 \/ ... \/ j = nk))."""
    neighbor_disj = gen_neighbor_disj(v, str(j_val))
    return f"({i_val} = {v} /\\ ({neighbor_disj}))"


# ---------------------------------------------------------------------------
# Non-edge proof: ~Adj17 i j
# ---------------------------------------------------------------------------

def gen_not_adj_proof(vertex_i, vertex_j, include_self_loops=False):
    """
    Generate proof of ~Adj17 vertex_i vertex_j where (vertex_i, vertex_j) is not an edge.

    With include_self_loops=True, also generates proofs for vertex_i == vertex_j.
    """
    if vertex_i == vertex_j and not include_self_loops:
        return None
    if is_edge(vertex_i, vertex_j):
        return None

    lines = []
    lines.append(f"Theorem Adj17_not_{vertex_i}_{vertex_j} : ~Adj17 {vertex_i} {vertex_j}.")
    lines.append(f"assume H: Adj17 {vertex_i} {vertex_j}.")
    lines.append("prove False.")
    lines.append("apply H.")

    # Generate proof for left-associative disjunction
    lines.extend(gen_outer_or_elim(vertex_i, vertex_j, list(range(17)), 0))

    lines.append("Qed.")
    return "\n".join(lines)


def gen_outer_or_elim(vertex_i, vertex_j, disjunct_indices, depth):
    """
    Generate elimination of the left-associative outer disjunction.

    The structure is (((P0 \/ P1) \/ P2) ... \/ P16)
    """
    lines = []
    indent = "  " * depth

    if len(disjunct_indices) == 1:
        # Base case: single disjunct - it's a conjunction
        idx = disjunct_indices[0]
        clause = gen_vertex_clause(idx, vertex_i, vertex_j)
        lines.append(f"{indent}- assume H_v{idx}: {clause}.")
        lines.append(f"{indent}  apply H_v{idx}.")
        lines.extend(gen_conjunction_proof(vertex_i, vertex_j, idx, depth + 1))
        return lines

    # Split into left (all but last) and right (last)
    left = disjunct_indices[:-1]
    right = disjunct_indices[-1]

    # Left branch
    if len(left) == 1:
        # Single element left - it's a conjunction, not a disjunction
        idx = left[0]
        clause = gen_vertex_clause(idx, vertex_i, vertex_j)
        lines.append(f"{indent}- assume H_v{idx}: {clause}.")
        lines.append(f"{indent}  apply H_v{idx}.")
        lines.extend(gen_conjunction_proof(vertex_i, vertex_j, idx, depth + 1))
    else:
        # Multiple elements - nested disjunction
        lines.append(f"{indent}- assume Hleft.")
        lines.append(f"{indent}  apply Hleft.")
        lines.extend(gen_outer_or_elim(vertex_i, vertex_j, left, depth + 1))

    # Right branch: single conjunction
    clause = gen_vertex_clause(right, vertex_i, vertex_j)
    lines.append(f"{indent}- assume H_v{right}: {clause}.")
    lines.append(f"{indent}  apply H_v{right}.")
    lines.extend(gen_conjunction_proof(vertex_i, vertex_j, right, depth + 1))

    return lines


def gen_conjunction_proof(vertex_i, vertex_j, idx, depth):
    """
    Generate proof for a conjunction: (vertex_i = idx /\ (vertex_j in neighbors(idx)))

    After apply, we get two assumptions via assume.
    """
    lines = []
    indent = "  " * depth
    neighbors = EDGES[idx]

    lines.append(f"{indent}assume Heq_i: {vertex_i} = {idx}.")

    if vertex_i != idx:
        # Contradiction: vertex_i = idx is false
        lines.append(f"{indent}assume _.")
        lines.append(f"{indent}{get_neq_lemma_direct(vertex_i, idx, 'Heq_i')}")
    else:
        # vertex_i == idx, so we need to refute each neighbor equality
        neighbor_disj = gen_neighbor_disj(idx, str(vertex_j))
        lines.append(f"{indent}assume Hj: {neighbor_disj}.")
        lines.append(f"{indent}apply Hj.")
        lines.extend(gen_neighbor_or_elim(vertex_j, neighbors, depth))

    return lines


def gen_neighbor_or_elim(vertex_j, neighbors, depth):
    """
    Generate elimination of the neighbor disjunction.
    vertex_j is not in neighbors, so each case leads to contradiction.
    """
    lines = []
    indent = "  " * depth

    if len(neighbors) == 1:
        n = neighbors[0]
        lines.append(f"{indent}- assume Heq: {vertex_j} = {n}.")
        lines.append(f"{indent}  {get_neq_lemma_direct(vertex_j, n, 'Heq')}")
        return lines

    # Split: left = all but last, right = last
    left = neighbors[:-1]
    right = neighbors[-1]

    # Left branch
    if len(left) == 1:
        # Single element left - just handle the equality directly
        n = left[0]
        lines.append(f"{indent}- assume Heq: {vertex_j} = {n}.")
        lines.append(f"{indent}  {get_neq_lemma_direct(vertex_j, n, 'Heq')}")
    else:
        # Multiple elements - disjunction
        left_disj = " \\/ ".join(f"{vertex_j} = {n}" for n in left)
        lines.append(f"{indent}- assume Hjl: {left_disj}.")
        lines.append(f"{indent}  apply Hjl.")
        lines.extend(gen_neighbor_or_elim(vertex_j, left, depth + 1))

    # Right branch
    lines.append(f"{indent}- assume Heq: {vertex_j} = {right}.")
    lines.append(f"{indent}  {get_neq_lemma_direct(vertex_j, right, 'Heq')}")

    return lines


# ---------------------------------------------------------------------------
# Path lemmas: Adj17 i j -> Adj17 j k -> ~Adj17 i k
# ---------------------------------------------------------------------------

def gen_path_lemma(i, j, k):
    """
    For a path i - j - k with (i,k) a non-edge, generate:
      Theorem Adj17_path_{i}_{j}_{k} : Adj17 {i} {j} -> Adj17 {j} {k} -> ~Adj17 {i} {k}.

    Proof uses the corresponding Adj17_not_{i}_{k} lemma.
    """
    if not is_edge(i, j):
        return None
    if not is_edge(j, k):
        return None
    if i == k:
        return None
    if is_edge(i, k):
        # Triangle found - this shouldn't happen in a triangle-free graph
        raise ValueError(f"Triangle detected: {i}-{j}-{k}")

    lines = []
    lines.append(f"Theorem Adj17_path_{i}_{j}_{k} : Adj17 {i} {j} -> Adj17 {j} {k} -> ~Adj17 {i} {k}.")
    lines.append(f"assume H1: Adj17 {i} {j}.")
    lines.append(f"assume H2: Adj17 {j} {k}.")
    lines.append(f"exact Adj17_not_{i}_{k}.")
    lines.append("Qed.")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

import sys

def main():
    include_self_loops = "--with-self-loops" in sys.argv

    all_chunks = []

    # No comments in output - Megalodon Mizar mode doesn't support (* *) syntax

    # 0. Self-loop proofs (if requested)
    selfloop_count = 0
    if include_self_loops:
        for i in VERTICES:
            proof = gen_not_adj_proof(i, i, include_self_loops=True)
            if proof is not None:
                all_chunks.append(proof)
                selfloop_count += 1

    # 1. Non-edge proofs
    nonedge_count = 0
    for i in VERTICES:
        for j in VERTICES:
            proof = gen_not_adj_proof(i, j)
            if proof is not None:
                all_chunks.append(proof)
                nonedge_count += 1

    # 2. Path lemmas
    path_count = 0
    seen_paths = set()
    for i in VERTICES:
        for j in EDGES[i]:
            for k in EDGES[j]:
                key = (i, j, k)
                if key in seen_paths:
                    continue
                lemma = gen_path_lemma(i, j, k)
                if lemma is not None:
                    seen_paths.add(key)
                    all_chunks.append(lemma)
                    path_count += 1

    # Print summary to stderr, not stdout
    if include_self_loops:
        sys.stderr.write(f"Generated {selfloop_count} self-loop proofs, {nonedge_count} non-edge proofs, and {path_count} path lemmas\n")
    else:
        sys.stderr.write(f"Generated {nonedge_count} non-edge proofs and {path_count} path lemmas\n")

    for chunk in all_chunks:
        print(chunk)
        print("")


if __name__ == "__main__":
    main()
