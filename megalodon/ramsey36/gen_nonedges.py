#!/usr/bin/env python3
"""Generate Megalodon proofs for ~Adj17 x z (non-edges).

For each non-edge (x,z), we prove ~Adj17 x z by:
1. Assume Adj17 x z
2. This gives a big disjunction of 17 cases
3. Each case is (i = x /\ something about z)
4. For i != x: immediate contradiction
5. For i = x: z must be a neighbor of x, but z is not a neighbor (non-edge)
"""

EDGES = [
    (0, 9), (0, 14), (0, 15), (0, 16),
    (1, 7), (1, 11), (1, 13), (1, 16),
    (2, 8), (2, 10), (2, 12), (2, 15),
    (3, 6), (3, 8), (3, 13), (3, 15), (3, 16),
    (4, 5), (4, 7), (4, 12), (4, 14), (4, 16),
    (5, 4), (5, 9), (5, 10), (5, 11), (5, 13),
    (6, 3), (6, 10), (6, 11), (6, 12), (6, 14),
    (7, 1), (7, 4), (7, 9), (7, 10), (7, 15),
    (8, 2), (8, 3), (8, 9), (8, 11), (8, 14),
    (9, 0), (9, 5), (9, 7), (9, 8), (9, 12),
    (10, 2), (10, 5), (10, 6), (10, 7), (10, 16),
    (11, 1), (11, 5), (11, 6), (11, 8), (11, 15),
    (12, 2), (12, 4), (12, 6), (12, 9), (12, 13),
    (13, 1), (13, 3), (13, 5), (13, 12), (13, 14),
    (14, 0), (14, 4), (14, 6), (14, 8), (14, 13),
    (15, 0), (15, 2), (15, 3), (15, 7), (15, 11),
    (16, 0), (16, 1), (16, 3), (16, 4), (16, 10),
]
EDGE_SET = set(EDGES)

def is_edge(i, j):
    return (i, j) in EDGE_SET

def neighbors(v):
    """Get all vertices z where (v, z) is an edge."""
    return sorted([j for (i, j) in EDGES if i == v])

# The structure of Adj17's right-hand side
ADJ17_RHS = []
for v in range(17):
    neighs = neighbors(v)
    ADJ17_RHS.append((v, neighs))

def gen_expanded_adj17(x, z):
    """Generate the expanded form of Adj17 x z."""
    parts = []
    for v in range(17):
        neighs = neighbors(v)
        if neighs:
            j_part = " \\/ ".join(f"{z} = {n}" for n in neighs)
            parts.append(f"({x} = {v} /\\ ({j_part}))")
    return " \\/ ".join(parts)

def count_or_depth(n):
    """Number of orIL needed to reach the n-th disjunct (0-indexed, leftmost)."""
    # For left-associative \/: ((((D0 \/ D1) \/ D2) \/ D3) ... \/ D16)
    # To reach D0: 16 orIL
    # To reach D1: 15 orIL then orIR
    # To reach Dk: (16-k) orIL then orIR (except D0)
    return 16 - n

def gen_nonedge_proof(x, z):
    """Generate proof of ~Adj17 x z for a non-edge."""
    lines = []
    lemma_name = f"Adj17_not_{x}_{z}"
    lines.append(f"Theorem {lemma_name} : ~Adj17 {x} {z}.")
    lines.append(f"assume H: Adj17 {x} {z}.")
    lines.append("prove False.")
    lines.append(f"(* Adj17 {x} {z} expands to a 17-way disjunction *)")
    lines.append("apply H.")

    # 17 cases for the disjunction
    for i in range(17):
        neighs = neighbors(i)
        lines.append(f"- (* Case i = {i} *)")
        if not neighs:
            lines.append(f"  (* Vertex {i} has no outgoing edges - vacuously false *)")
            lines.append(f"  assume Hcase: {x} = {i} /\\ False.")
            lines.append("  apply andER Hcase.")
        elif i != x:
            # i != x, so the first conjunct x = i is false
            lines.append(f"  assume Hcase: {x} = {i} /\\ _.")
            lines.append(f"  (* {x} != {i}, contradiction *)")
            lines.append("  apply andEL Hcase.")
            lines.append(f"  assume Heq: {x} = {i}.")
            lines.append(f"  (* {x} = {i} is false, need neq axiom *)")
            lines.append(f"  Admitted. (* TODO: derive False from {x} = {i} *)")
        else:
            # i = x, so the second conjunct says z is a neighbor of x
            # But z is NOT a neighbor (since this is a non-edge)
            j_part = " \\/ ".join(f"{z} = {n}" for n in neighs)
            lines.append(f"  assume Hcase: {x} = {i} /\\ ({j_part}).")
            lines.append(f"  (* z = {z} is not in {{{','.join(map(str, neighs))}}} *)")
            lines.append("  apply andER Hcase.")
            lines.append(f"  assume Hjcases: {j_part}.")
            lines.append("  apply Hjcases.")
            for n in neighs:
                lines.append(f"  - (* z = {n} but z = {z} *)")
                lines.append(f"    assume Heq: {z} = {n}.")
                lines.append(f"    (* {z} != {n}, contradiction *)")
                lines.append(f"    Admitted. (* TODO: derive False from {z} = {n} *)")

    lines.append("Qed.")
    return "\n".join(lines)

def main():
    # Find all non-edges
    non_edges = []
    for x in range(17):
        for z in range(17):
            if x != z and not is_edge(x, z):
                non_edges.append((x, z))

    print(f"(* Total non-edges: {len(non_edges)} *)")
    print(f"(* Total edges: {len(EDGES)} *)")
    print()

    # Generate just a sample proof
    print("(* Sample non-edge proof: ~Adj17 0 1 *)")
    print(gen_nonedge_proof(0, 1))

if __name__ == "__main__":
    main()
