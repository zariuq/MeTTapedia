#!/usr/bin/env python3
"""Generate Megalodon proofs for ~Adj17 i j (non-edges)."""

# The Graver-Yackel 17-vertex graph edges (directed, both directions)
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

# Build adjacency set for quick lookup
ADJ_SET = set()
for i, neighbors in EDGES.items():
    for j in neighbors:
        ADJ_SET.add((i, j))

def is_edge(i, j):
    return (i, j) in ADJ_SET

def get_neq_lemma(a, b):
    """Get the inequality lemma name for a <> b (i.e., a = b -> False)."""
    return f"neq_{a}_{b}"

def generate_disjunct_proof(vertex_i, vertex_j, disjunct_idx, indent):
    """Generate proof for a single disjunct being false.

    Disjunct form: (vertex_i = idx /\ (vertex_j = n1 \/ vertex_j = n2 \/ ...))
    """
    idx = disjunct_idx
    neighbors = EDGES[idx]
    lines = []

    # First conjunct: vertex_i = idx
    if vertex_i == idx:
        # First conjunct is true, need to refute second conjunct (the inner disjunction)
        lines.append(f"{indent}assume Heq_i: {vertex_i} = {idx}.")

        # Inner disjunction: vertex_j = n1 \/ vertex_j = n2 \/ ...
        # This is also left-associative
        num_neighbors = len(neighbors)

        if num_neighbors == 4:
            # Structure: ((n0 \/ n1) \/ n2) \/ n3
            lines.append(f"{indent}assume Hj.")
            lines.append(f"{indent}apply Hj.")

            # Level 1: ((n0 \/ n1) \/ n2) vs n3
            lines.append(f"{indent}- assume Hj1.")
            lines.append(f"{indent}  apply Hj1.")
            # Level 2: (n0 \/ n1) vs n2
            lines.append(f"{indent}  + assume Hj2.")
            lines.append(f"{indent}    apply Hj2.")
            # Level 3: n0 vs n1
            lines.append(f"{indent}    * assume Heq: {vertex_j} = {neighbors[0]}.")
            lines.append(f"{indent}      exact {get_neq_lemma(vertex_j, neighbors[0])} Heq.")
            lines.append(f"{indent}    * assume Heq: {vertex_j} = {neighbors[1]}.")
            lines.append(f"{indent}      exact {get_neq_lemma(vertex_j, neighbors[1])} Heq.")
            # Back to level 2: n2
            lines.append(f"{indent}  + assume Heq: {vertex_j} = {neighbors[2]}.")
            lines.append(f"{indent}    exact {get_neq_lemma(vertex_j, neighbors[2])} Heq.")
            # Back to level 1: n3
            lines.append(f"{indent}- assume Heq: {vertex_j} = {neighbors[3]}.")
            lines.append(f"{indent}  exact {get_neq_lemma(vertex_j, neighbors[3])} Heq.")

        elif num_neighbors == 5:
            # Structure: (((n0 \/ n1) \/ n2) \/ n3) \/ n4
            lines.append(f"{indent}assume Hj.")
            lines.append(f"{indent}apply Hj.")

            # Level 1: (((n0 \/ n1) \/ n2) \/ n3) vs n4
            lines.append(f"{indent}- assume Hj1.")
            lines.append(f"{indent}  apply Hj1.")
            # Level 2: ((n0 \/ n1) \/ n2) vs n3
            lines.append(f"{indent}  + assume Hj2.")
            lines.append(f"{indent}    apply Hj2.")
            # Level 3: (n0 \/ n1) vs n2
            lines.append(f"{indent}    * assume Hj3.")
            lines.append(f"{indent}      apply Hj3.")
            # Level 4: n0 vs n1
            lines.append(f"{indent}      @ assume Heq: {vertex_j} = {neighbors[0]}.")
            lines.append(f"{indent}        exact {get_neq_lemma(vertex_j, neighbors[0])} Heq.")
            lines.append(f"{indent}      @ assume Heq: {vertex_j} = {neighbors[1]}.")
            lines.append(f"{indent}        exact {get_neq_lemma(vertex_j, neighbors[1])} Heq.")
            # Back to level 3: n2
            lines.append(f"{indent}    * assume Heq: {vertex_j} = {neighbors[2]}.")
            lines.append(f"{indent}      exact {get_neq_lemma(vertex_j, neighbors[2])} Heq.")
            # Back to level 2: n3
            lines.append(f"{indent}  + assume Heq: {vertex_j} = {neighbors[3]}.")
            lines.append(f"{indent}    exact {get_neq_lemma(vertex_j, neighbors[3])} Heq.")
            # Back to level 1: n4
            lines.append(f"{indent}- assume Heq: {vertex_j} = {neighbors[4]}.")
            lines.append(f"{indent}  exact {get_neq_lemma(vertex_j, neighbors[4])} Heq.")
        else:
            raise ValueError(f"Unexpected number of neighbors: {num_neighbors}")

    else:
        # First conjunct is false: vertex_i <> idx
        lines.append(f"{indent}assume Heq_i: {vertex_i} = {idx}.")
        lines.append(f"{indent}assume _.")
        lines.append(f"{indent}exact {get_neq_lemma(vertex_i, idx)} Heq_i.")

    return lines

def generate_not_adj_proof(i, j):
    """Generate a complete proof of ~Adj17 i j."""
    if is_edge(i, j):
        return None  # Can't prove ~Adj17 for an edge

    lines = []
    lines.append(f"Theorem Adj17_not_{i}_{j} : ~Adj17 {i} {j}.")
    lines.append(f"assume H: Adj17 {i} {j}.")
    lines.append("prove False.")
    lines.append("apply H.")

    # 17 disjuncts, left-associative: ((((... \/ D14) \/ D15) \/ D16)
    # After apply H: 16 nested levels of bullets
    # - First bullet: (((... \/ D14) \/ D15) -> False
    # - Last bullet: D16 -> False

    # We'll use a recursive structure with bullet characters
    # Megalodon supports: - + * @ (maybe more?)

    bullet_chars = ['-', '+', '*', '@', '#', '$', '%', '^', '&', '!', '~', '`', ':', ';', '<', '>']

    # Generate the nested structure
    # For 17 disjuncts (indices 0-16), we have 16 binary or operations
    # The tree structure is:
    #   ((((((((((((((((D0 \/ D1) \/ D2) \/ D3) \/ D4) \/ D5) \/ D6) \/ D7) \/ D8) \/ D9) \/ D10) \/ D11) \/ D12) \/ D13) \/ D14) \/ D15) \/ D16

    def gen_or_elim(level, disjunct_indices, indent):
        """Generate proof for eliminating a left-associative disjunction."""
        result = []

        if len(disjunct_indices) == 1:
            # Base case: single disjunct (a conjunction)
            idx = disjunct_indices[0]
            result.append(f"{indent}assume Hd{idx}.")
            result.append(f"{indent}apply Hd{idx}.")
            result.extend(generate_disjunct_proof(i, j, idx, indent))
            return result

        # Recursive case: split into left (all but last) and right (last)
        left_indices = disjunct_indices[:-1]
        right_idx = disjunct_indices[-1]

        bullet = bullet_chars[level % len(bullet_chars)]

        # Left branch (the nested disjunction)
        result.append(f"{indent}{bullet} assume Hleft.")
        result.append(f"{indent}  apply Hleft.")
        result.extend(gen_or_elim(level + 1, left_indices, indent + "  "))

        # Right branch (single disjunct)
        result.append(f"{indent}{bullet} assume Hd{right_idx}.")
        result.append(f"{indent}  apply Hd{right_idx}.")
        result.extend(generate_disjunct_proof(i, j, right_idx, indent + "  "))

        return result

    lines.extend(gen_or_elim(0, list(range(17)), ""))
    lines.append("Qed.")
    lines.append("")

    return "\n".join(lines)

def main():
    # Generate all non-edge proofs
    all_proofs = []
    count = 0

    for i in range(17):
        for j in range(17):
            if i != j and not is_edge(i, j):
                proof = generate_not_adj_proof(i, j)
                if proof:
                    all_proofs.append(proof)
                    count += 1

    print(f"(* Generated {count} non-edge proofs *)")
    print("")
    for proof in all_proofs:
        print(proof)

if __name__ == "__main__":
    main()
