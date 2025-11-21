#!/usr/bin/env python3
"""Generate Megalodon proofs for Adj17 edge theorems and Adj17_sym.

The Adj17 definition is a 17-way left-associative disjunction:
  ((((P0 \/ P1) \/ P2) \/ ...) \/ P16)

To reach clause for vertex k:
- If k < 16: apply orIL (16-k) times, then orIR
- If k = 16: apply orIR directly (rightmost disjunct)

Each vertex clause has form: (i = k /\ (j = n1 \/ j = n2 \/ ...))
The neighbor disjunction is also left-associative.
"""

# Adjacency list for the 17-vertex Graver-Yackel graph
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

def gen_expanded_def(i, j):
    """Generate the fully expanded Adj17 definition with i,j substituted."""
    return gen_partial_def(list(range(17)), i_var=i, j_var=j)

def gen_vertex_clause(v, i_var="i", j_var="j"):
    """Generate the clause for a single vertex v."""
    neighbors = adj[v]
    neighbor_disj = " \/ ".join(f"{j_var} = {n}" for n in neighbors)
    return f"({i_var} = {v} /\ ({neighbor_disj}))"

def gen_partial_def(vertices, i_var="i", j_var="j"):
    """Generate the disjunction for a subset of vertices."""
    clauses = [gen_vertex_clause(v, i_var, j_var) for v in vertices]
    return " \/\n    ".join(clauses)

def gen_vertex_navigation(vertex):
    """Generate orIL/orIR to navigate to vertex's clause."""
    if vertex == 16:
        return "apply orIR."
    elif vertex == 0:
        return "apply orIL. " * 16
    else:
        n_orIL = 16 - vertex
        return "apply orIL. " * n_orIL + "apply orIR."

def gen_neighbor_navigation(neighbors, target):
    """Generate orIL/orIR to navigate to target neighbor in list."""
    n = len(neighbors)
    idx = neighbors.index(target)
    n_orIL = n - 1 - idx

    if n_orIL == 0:
        return "apply orIR. reflexivity."
    elif idx == 0:
        return "apply orIL. " * n_orIL + "reflexivity."
    else:
        return "apply orIL. " * n_orIL + "apply orIR. reflexivity."

def gen_edge_theorem(i, j):
    """Generate a complete theorem proving Adj17 i j."""
    lines = []
    lines.append(f"Theorem Adj17_{i}_{j} : Adj17 {i} {j}.")
    lines.append(f"prove {gen_expanded_def(i, j)}.")
    lines.append(gen_vertex_navigation(i))
    lines.append("apply andI.")
    lines.append("- reflexivity.")
    lines.append(f"- {gen_neighbor_navigation(adj[i], j)}")
    lines.append("Qed.")
    return "\n".join(lines)

def gen_all_edge_theorems():
    """Generate all 68 directed edge theorems."""
    theorems = []
    for i in range(17):
        for j in adj[i]:
            theorems.append(gen_edge_theorem(i, j))
    return "\n\n".join(theorems)

def indent(text, prefix="  "):
    """Indent a block of text."""
    return "\n".join(prefix + line for line in text.splitlines())

def gen_recursive_neighbor_step(neighbors, v, hyp_name):
    """Recursively generate proof steps for neighbor disjunction."""
    lines = []
    
    # LEFT BRANCH
    left_subset = neighbors[:-1]
    left_pat = " \/ ".join(f"j = {n}" for n in left_subset)
    lines.append(f"- assume HL: {left_pat}.")
    
    if len(left_subset) > 1:
        lines.append(f"  apply HL.")
        lines.append(indent(gen_recursive_neighbor_step(left_subset, v, "HL"), "  "))
    else:
        # Base case: Left is a single neighbor
        n = left_subset[0]
        lines.append(f"  rewrite Hi. rewrite HL.")
        lines.append(f"  exact Adj17_{n}_{v}.")
        
    # RIGHT BRANCH
    right_n = neighbors[-1]
    lines.append(f"- assume HR: j = {right_n}.")
    lines.append(f"  rewrite Hi. rewrite HR.")
    lines.append(f"  exact Adj17_{right_n}_{v}.")
    
    return "\n".join(lines)

def gen_vertex_case_body(v, hyp_name):
    """Generate the body of the proof for a specific vertex case."""
    lines = []
    lines.append(f"apply {hyp_name}.")
    lines.append(f"assume Hi: i = {v}.")
    neighbor_disj = " \/ ".join(f"j = {n}" for n in adj[v])
    lines.append(f"assume H_neighbors: {neighbor_disj}.")
    lines.append(f"apply H_neighbors.")
    lines.append(gen_recursive_neighbor_step(adj[v], v, "H_neighbors"))
    return "\n".join(lines)

def gen_recursive_vertex_step(vertices):
    """Recursively generate proof steps for vertex disjunction."""
    k = vertices[-1]
    left_subset = vertices[:-1]
    lines = []
    
    # LEFT BRANCH
    left_def = gen_partial_def(left_subset)
    lines.append(f"- assume HL: {left_def}.")
    
    if len(left_subset) > 1:
        lines.append(f"  apply HL.")
        lines.append(indent(gen_recursive_vertex_step(left_subset), "  "))
    else:
        # Base case: Vertex 0
        lines.append(indent(gen_vertex_case_body(left_subset[0], "HL"), "  "))

    # RIGHT BRANCH
    right_def = gen_vertex_clause(k)
    lines.append(f"- assume HR: {right_def}.")
    lines.append(indent(gen_vertex_case_body(k, "HR"), "  "))

    return "\n".join(lines)

def gen_adj17_sym():
    """Generate Adj17_sym using recursive disjunction elimination."""
    lines = []
    lines.append("Theorem Adj17_sym : forall i j : set, Adj17 i j -> Adj17 j i.")
    lines.append("let i j.")
    lines.append("assume H: Adj17 i j.")
    lines.append("prove Adj17 j i.")
    lines.append("apply H.")
    
    vertices = list(range(17))
    lines.append(gen_recursive_vertex_step(vertices))
    
    lines.append("Qed.")
    return "\n".join(lines)

def main():
    print(gen_all_edge_theorems())
    print("\n")
    print(gen_adj17_sym())

if __name__ == "__main__":
    main()