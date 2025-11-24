#!/usr/bin/env python3
"""Generate Megalodon proof for Adj17_sym."""

# Adjacency list for the 17-vertex Graver-Yackel graph
# adj[i] = list of neighbors of vertex i
adj = {
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

def count_orIL_for_vertex(target_vertex):
    """Count how many orIL applications to reach vertex target_vertex's clause.
    The definition has 17 disjuncts (vertices 0-16), left-associative.
    To reach vertex k, we need (16-k) orIL applications, then orIR (or orIL if k=0)."""
    return 16 - target_vertex

def count_orIL_for_neighbor(neighbors, target_neighbor):
    """Count orIL applications within a vertex's neighbor list."""
    # neighbors is sorted, we want to reach target_neighbor
    # The disjunction is left-associative
    idx = neighbors.index(target_neighbor)
    n = len(neighbors)
    return n - 1 - idx

def generate_edge_proof(i, j):
    """Generate proof that Adj17 j i holds, given we know Adj17 i j."""
    # Find where j appears in adj[i] and where i appears in adj[j]
    neighbors_i = adj[i]
    neighbors_j = adj[j]

    # To prove Adj17 j i, we need to navigate to vertex j's clause
    # then to neighbor i within j's neighbor list

    orIL_vertex = count_orIL_for_vertex(j)
    orIL_neighbor = count_orIL_for_neighbor(neighbors_j, i)

    lines = []
    lines.append(f"    (* Edge {i}->{j}, prove {j}->{i} *)")
    lines.append(f"    prove Adj17 {j} {i}.")

    # Generate orIL applications to reach vertex j's clause
    if orIL_vertex > 0:
        orIL_str = "apply orIL. " * orIL_vertex
        lines.append(f"    {orIL_str.strip()}")

    # Now apply orIR to select the correct clause (unless it's vertex 16)
    if j < 16:
        lines.append(f"    apply orIR.")

    lines.append(f"    apply andI.")
    lines.append(f"    * reflexivity.")

    # Generate orIL applications for neighbor selection
    if orIL_neighbor > 0:
        orIL_str = "apply orIL. " * orIL_neighbor
        lines.append(f"    * {orIL_str.strip()}")
        # Check if we need orIR at the end
        if neighbors_j.index(i) < len(neighbors_j) - 1:
            lines.append(f"      apply orIR. reflexivity.")
        else:
            lines.append(f"      reflexivity.")
    else:
        # First neighbor, just orIL... wait, leftmost is actually rightmost due to left-assoc
        # Actually for a list like [a,b,c,d], the disjunction is ((a \/ b) \/ c) \/ d
        # So d is first (0 orIL), c needs 1 orIL then orIR, etc.
        # Let me reconsider...
        lines.append(f"    * reflexivity.")

    return "\n".join(lines)

def generate_full_proof():
    """Generate the complete Adj17_sym proof."""
    lines = []
    lines.append("Theorem Adj17_sym : forall i j, Adj17 i j -> Adj17 j i.")
    lines.append("let i j.")
    lines.append("assume H: Adj17 i j.")
    lines.append("prove Adj17 j i.")
    lines.append("apply H.")

    for vertex in range(17):
        neighbors = adj[vertex]
        n_neighbors = len(neighbors)

        lines.append(f"- (* Case i = {vertex} *)")
        lines.append(f"  assume H{vertex}: {vertex} = {vertex} /\\ (...).")
        lines.append(f"  apply H{vertex}. assume Hi. assume Hj.")

        # Handle each neighbor
        lines.append(f"  apply Hj.")

        for idx, neighbor in enumerate(neighbors):
            bullet = "+" if n_neighbors > 1 else ""
            lines.append(f"  {bullet} assume Hj{neighbor}: j = {neighbor}.")
            lines.append(f"    rewrite Hi. rewrite Hj{neighbor}.")
            lines.append(generate_edge_proof(vertex, neighbor))

    lines.append("Qed.")
    return "\n".join(lines)

# Actually, let me generate a simpler version - one theorem per edge
def generate_individual_edge_theorems():
    """Generate individual theorems for each directed edge."""
    lines = []

    for i in range(17):
        for j in adj[i]:
            # Theorem proving Adj17 i j
            lines.append(f"Theorem Adj17_{i}_{j} : Adj17 {i} {j}.")

            # Navigate to vertex i's clause
            orIL_count = 16 - i
            if orIL_count > 0:
                lines.append("apply orIL. " * orIL_count + "apply orIR." if i < 16 else "apply orIL. " * orIL_count)
            elif i == 16:
                pass  # Last clause, no navigation needed
            else:
                lines.append("apply orIR.")

            lines.append("apply andI.")
            lines.append("- reflexivity.")

            # Navigate to neighbor j within i's neighbor list
            neighbors = adj[i]
            idx = neighbors.index(j)
            n = len(neighbors)
            orIL_neighbor = n - 1 - idx

            if orIL_neighbor > 0:
                nav = "apply orIL. " * orIL_neighbor
                if idx < n - 1:
                    lines.append(f"- {nav}apply orIR. reflexivity.")
                else:
                    lines.append(f"- {nav}reflexivity.")
            else:
                lines.append("- reflexivity.")

            lines.append("Qed.")
            lines.append("")

    return "\n".join(lines)

if __name__ == "__main__":
    print("(* Generated edge theorems for Adj17 *)")
    print()

    # Just print the first few edges as a test
    for i in range(3):  # First 3 vertices
        for j in adj[i]:
            print(f"(* Edge {i} -> {j} *)")

            # The full Adj17 definition has 17 disjuncts, left-associative
            # ((((P0 \/ P1) \/ P2) \/ ...) \/ P16)
            # To get Pi: apply orIL (16-i) times, then if i<16 apply orIR

            orIL_v = 16 - i

            print(f"Theorem Adj17_{i}_{j} : Adj17 {i} {j}.")
            print(f"prove ({i} = {i} /\\ ...) \\/ ...")  # Just show structure

            nav = ""
            for _ in range(orIL_v):
                nav += "apply orIL. "
            if i < 16:
                nav += "apply orIR."
            print(nav if nav else "(* at clause 16 *)")

            print("apply andI.")
            print("- reflexivity.")

            # For neighbors, same logic
            neighbors = adj[i]
            idx = neighbors.index(j)
            n = len(neighbors)
            orIL_n = n - 1 - idx

            nav_n = ""
            for _ in range(orIL_n):
                nav_n += "apply orIL. "
            if idx < n - 1:
                nav_n += "apply orIR. "
            nav_n += "reflexivity."
            print(f"- {nav_n}")

            print("Qed.")
            print()
