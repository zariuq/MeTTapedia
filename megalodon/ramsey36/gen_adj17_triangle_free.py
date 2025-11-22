#!/usr/bin/env python3
"""
Generate kernel-level Megalodon proof for Adj17_triangle_free.

The theorem states:
  triangle_free 17 Adj17
  = forall x :e 17, forall y :e 17, forall z :e 17,
      Adj17 x y -> Adj17 y z -> Adj17 x z -> False

This requires 17^3 = 4913 cases, but most are trivial because at least
one of the three edges doesn't exist.

For each triple (x,y,z):
- If Adj17 x y is false: we have assumption H1: Adj17 x y which contradicts Adj17_not_x_y
- If Adj17 y z is false: we have assumption H2: Adj17 y z which contradicts Adj17_not_y_z
- If Adj17 x z is false: we have assumption H3: Adj17 x z which contradicts Adj17_not_x_z
- If all three are edges: this is a triangle, impossible in the graph

The proof structure uses cases_17 (to be defined or use ordinal reasoning)
for case splitting on x, y, z values.
"""

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

VERTICES = list(range(17))


def is_edge(i, j):
    """Return True iff (i,j) is an edge."""
    return j in EDGES[i]


def generate_case_proof(x, y, z):
    """
    Generate proof for a single (x,y,z) case.

    We're proving: Adj17 x y -> Adj17 y z -> Adj17 x z -> False
    """
    lines = []

    # Check which "edges" exist
    xy_edge = is_edge(x, y)
    yz_edge = is_edge(y, z)
    xz_edge = is_edge(x, z)

    if x == y:
        # If x = y, then Adj17 x y is the same as Adj17 x x which should be false
        # (no self-loops). Use the non-edge proof.
        lines.append(f"    exact Adj17_not_{x}_{y} H1.")
    elif y == z:
        lines.append(f"    exact Adj17_not_{y}_{z} H2.")
    elif x == z:
        lines.append(f"    exact Adj17_not_{x}_{z} H3.")
    elif not xy_edge:
        # H1: Adj17 x y contradicts Adj17_not_x_y
        lines.append(f"    exact Adj17_not_{x}_{y} H1.")
    elif not yz_edge:
        # H2: Adj17 y z contradicts Adj17_not_y_z
        lines.append(f"    exact Adj17_not_{y}_{z} H2.")
    elif not xz_edge:
        # H3: Adj17 x z contradicts Adj17_not_x_z
        lines.append(f"    exact Adj17_not_{x}_{z} H3.")
    else:
        # All three are edges - this is a triangle!
        # This should never happen in the Graver-Yackel graph
        raise ValueError(f"Triangle detected: {x}-{y}-{z}")

    return lines


def gen_inner_z_cases(x, y):
    """Generate the proof for all z cases given fixed x, y."""
    lines = []

    # For z :e 17, we need cases_17 or explicit z = 0, z = 1, ..., z = 16
    # Since cases_17 isn't in preamble, we'll use explicit bullets

    for z in range(17):
        if z == 0:
            # First case doesn't need bullet for innermost
            pass
        lines.append(f"  + assume Hz: z = {z}.")
        lines.append(f"    rewrite Hz in H1 H2 H3.")
        lines.extend(generate_case_proof(x, y, z))

    return lines


def gen_inner_y_cases(x):
    """Generate the proof for all y cases given fixed x."""
    lines = []

    for y in range(17):
        lines.append(f" - assume Hy: y = {y}.")
        lines.append(f"   rewrite Hy in H1 H2.")
        lines.append(f"   apply cases_17 z.")
        lines.extend(gen_inner_z_cases(x, y))

    return lines


def generate_triangle_free_proof():
    """Generate the full proof of Adj17_triangle_free."""
    lines = []

    # First, define cases_17 if needed
    lines.append("(* Case analysis axiom for 17 elements *)")
    lines.append("Axiom cases_17: forall i :e 17, forall p:set->prop,")
    lines.append("  p 0 -> p 1 -> p 2 -> p 3 -> p 4 -> p 5 -> p 6 -> p 7 -> p 8 ->")
    lines.append("  p 9 -> p 10 -> p 11 -> p 12 -> p 13 -> p 14 -> p 15 -> p 16 -> p i.")
    lines.append("")

    lines.append("Theorem Adj17_triangle_free : triangle_free 17 Adj17.")
    lines.append("let x. assume Hx: x :e 17.")
    lines.append("let y. assume Hy_mem: y :e 17.")
    lines.append("let z. assume Hz_mem: z :e 17.")
    lines.append("assume H1: Adj17 x y.")
    lines.append("assume H2: Adj17 y z.")
    lines.append("assume H3: Adj17 x z.")
    lines.append("prove False.")
    lines.append("")
    lines.append("(* Case analysis on x *)")
    lines.append("apply cases_17 x Hx (fun x => Adj17 x y -> Adj17 y z -> Adj17 x z -> False).")

    # This approach is complex. Let me try a simpler one using direct case splits.
    # Actually, the proof would be too complex. Let me think of a better approach.

    return lines


def main():
    # Print statistics
    non_edges = 0
    edges = 0
    for i in range(17):
        for j in range(17):
            if i == j:
                continue
            if is_edge(i, j):
                edges += 1
            else:
                non_edges += 1

    print(f"(* Graph statistics: *)")
    print(f"(* - 17 vertices *)")
    print(f"(* - {edges} directed edges ({edges//2} undirected) *)")
    print(f"(* - {non_edges} directed non-edges *)")
    print()

    # Check for triangles
    triangles = []
    for x in range(17):
        for y in range(17):
            if x == y:
                continue
            if not is_edge(x, y):
                continue
            for z in range(17):
                if z == x or z == y:
                    continue
                if is_edge(y, z) and is_edge(x, z):
                    triangles.append((x, y, z))

    if triangles:
        print(f"(* WARNING: {len(triangles)} triangles found! *)")
        for t in triangles[:10]:
            print(f"(*   Triangle: {t} *)")
    else:
        print(f"(* Graph is triangle-free (verified) *)")
    print()

    # The proof structure is too complex for this approach
    # Let me try a different approach - prove it directly using the path lemmas

    print("(* Adj17_triangle_free proof structure *)")
    print("(* This theorem requires 17^3 case analysis *)")
    print("(* For each case (x,y,z), we use the appropriate non-edge lemma *)")
    print()

    # Show which non-edge lemma each case would use
    print("(* Case analysis summary: *)")
    cases_by_type = {"H1_contradiction": 0, "H2_contradiction": 0, "H3_contradiction": 0, "self_loop": 0}
    for x in range(17):
        for y in range(17):
            for z in range(17):
                if x == y or y == z or x == z:
                    cases_by_type["self_loop"] += 1
                elif not is_edge(x, y):
                    cases_by_type["H1_contradiction"] += 1
                elif not is_edge(y, z):
                    cases_by_type["H2_contradiction"] += 1
                elif not is_edge(x, z):
                    cases_by_type["H3_contradiction"] += 1
                else:
                    print(f"ERROR: Triangle {x}-{y}-{z}")

    print(f"(* - Self-loop cases (x=y or y=z or x=z): {cases_by_type['self_loop']} *)")
    print(f"(* - H1 contradiction (x-y not edge): {cases_by_type['H1_contradiction']} *)")
    print(f"(* - H2 contradiction (y-z not edge): {cases_by_type['H2_contradiction']} *)")
    print(f"(* - H3 contradiction (x-z not edge): {cases_by_type['H3_contradiction']} *)")


if __name__ == "__main__":
    main()
