#!/usr/bin/env python3
"""
Generate a fully expanded Megalodon proof of `Adj17_triangle_free` using
mechanical case analysis over the left-associative disjunction in `Adj17`.

What this script emits:
1) The `Adj17` and `triangle_free` definitions (copied from ramsey36_mizar.mg)
2) Non-edge lemmas `Adj17_not_i_j` for every non-edge (including loops)
3) Case lemmas `Adj17_cases_i` that destruct `Adj17 i j` into a small disjunction
4) The full proof of `Adj17_triangle_free : triangle_free 17 Adj17`
   using only the above lemmas (316 two-edge paths).

Run it directly to write `adj17_triangle_free_auto.mg` next to this script:
    python gen_adj17_reconstruct_alt.py

The generated file is self-contained except for the standard Mizar preamble
and `neq_lemmas.mg` (for 10-16 inequalities). Compile with:
    ./bin/megalodon -mizar \
      -I examples/mizar/PfgMizarNov2020Preamble.mgs \
      -I ramsey36/neq_lemmas.mg \
      ramsey36/adj17_triangle_free_auto.mg
"""

from pathlib import Path
from textwrap import indent

# Adjacency list for the 17-vertex Graver–Yackel graph
ADJ = {
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

EDGE_SET = {(i, j) for i, js in ADJ.items() for j in js}


def left_or(exprs):
    """Left-associative disjunction of a list of strings."""
    return " \\/ ".join(exprs)


def or_intro_steps(length, index):
    """
    Steps (`apply orIL.` / `apply orIR.`) needed to introduce the disjunct at
    `index` in a left-associated `length`-ary disjunction.
    """
    steps = []
    k = length
    idx = index
    while k > 1:
        if idx == k - 1:
            steps.append("apply orIR.")
            break
        steps.append("apply orIL.")
        k -= 1
    return steps


def neq_call(a, b, hyp):
    """Call the available neq lemma, orienting as (max,min)."""
    x, y = (a, b) if a >= b else (b, a)
    return f"exact neq_{x}_{y} {hyp}."


def gen_adj_definition():
    lines = [
        "Definition triangle_free : set -> (set -> set -> prop) -> prop :=",
        "  fun V R => forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.",
        "",
        "Definition Adj17 : set -> set -> prop :=",
        "  fun i j =>",
    ]
    clause_lines = []
    for i in range(17):
        neighbors = " \\/ ".join(f"j = {n}" for n in ADJ[i])
        clause_lines.append(f"    (i = {i} /\\ ({neighbors}))")
    # Left-associative by simple joining
    lines.append(" \\/\n".join(clause_lines) + ".")
    return "\n".join(lines)


def gen_nonedge_lemma(i, j):
    """~Adj17 i j proof by case split on the definition."""
    lines = []
    lines.append(f"Theorem Adj17_not_{i}_{j} : ~Adj17 {i} {j}.")
    lines.append(f"assume H: Adj17 {i} {j}.")
    lines.append("prove False.")
    lines.append("apply H.")
    for k in range(17):
        j_disj = left_or([f"{j} = {n}" for n in ADJ[k]])
        lines.append(f"- assume Hcase: {i} = {k} /\\ ({j_disj}).")
        if k == i:
            lines.append("  apply andER Hcase.")
            lines.append(f"  assume Hjcases: {j_disj}.")
            lines.append("  apply Hjcases.")
            for n in ADJ[k]:
                lines.append(f"  + assume Heq: {j} = {n}.")
                lines.append(f"    {neq_call(j, n, 'Heq')}")
        else:
            lines.append("  apply andEL Hcase.")
            lines.append(f"  assume Heq: {i} = {k}.")
            lines.append(f"  {neq_call(i, k, 'Heq')}")
    lines.append("Qed.")
    return "\n".join(lines)


def gen_all_nonedge_lemmas():
    lemmas = []
    for i in range(17):
        for j in range(17):
            if (i, j) in EDGE_SET:
                continue
            lemmas.append(gen_nonedge_lemma(i, j))
    return "\n\n".join(lemmas)


def gen_cases_lemma(i):
    """Adj17_cases_i : Adj17 i j -> j is one of the 4-5 neighbors."""
    neighbors = ADJ[i]
    goal_disj = left_or([f"j = {n}" for n in neighbors])
    lines = []
    lines.append(f"Theorem Adj17_cases_{i} : forall j, Adj17 {i} j -> {goal_disj}.")
    lines.append("let j.")
    lines.append(f"assume H: Adj17 {i} j.")
    lines.append("apply H.")
    for k in range(17):
        j_disj = left_or([f"j = {n}" for n in ADJ[k]])
        lines.append(f"- assume Hcase: {i} = {k} /\\ ({j_disj}).")
        if k == i:
            lines.append("  apply andER Hcase.")
            lines.append(f"  assume Hjcases: {j_disj}.")
            lines.append("  apply Hjcases.")
            for idx, n in enumerate(neighbors):
                steps = or_intro_steps(len(neighbors), idx)
                lines.append(f"  + assume Heq: j = {n}.")
                for step in steps:
                    lines.append(f"    {step}")
                lines.append("    exact Heq.")
        else:
            lines.append("  apply andEL Hcase.")
            lines.append(f"  assume Heq: {i} = {k}.")
            lines.append("  apply FalseE.")
            lines.append(f"  {neq_call(i, k, 'Heq')}")
    lines.append("Qed.")
    return "\n".join(lines)


def gen_all_cases_lemmas():
    return "\n\n".join(gen_cases_lemma(i) for i in range(17))


def compute_triangle_paths():
    """List of (x, y, z) with x->y, y->z edges; ensure x-z is NOT an edge."""
    paths = []
    for x in range(17):
        for y in ADJ[x]:
            for z in ADJ[y]:
                if (x, z) in EDGE_SET:
                    raise ValueError(f"Triangle detected: {x}-{y}-{z}")
                paths.append((x, y, z))
    return paths


def gen_triangle_free():
    paths = compute_triangle_paths()
    lines = []
    lines.append("Theorem Adj17_triangle_free : triangle_free 17 Adj17.")
    lines.append("prove forall x :e 17, forall y :e 17, forall z :e 17, Adj17 x y -> Adj17 y z -> Adj17 x z -> False.")
    lines.append("let x. assume Hx: x :e 17.")
    lines.append("let y. assume Hy: y :e 17.")
    lines.append("let z. assume Hz: z :e 17.")
    lines.append("assume Hxy: Adj17 x y.")
    lines.append("assume Hyz: Adj17 y z.")
    lines.append("assume Hxz: Adj17 x z.")
    lines.append("apply Hxy.")

    for x in range(17):
        y_disj = left_or([f"y = {n}" for n in ADJ[x]])
        lines.append(f"- assume Hxy_case: x = {x} /\\ ({y_disj}).")
        lines.append("  apply Hxy_case.")
        lines.append(f"  assume Hx_eq: x = {x}.")
        lines.append(f"  assume Hy_cases: {y_disj}.")
        lines.append("  apply Hy_cases.")
        for y in ADJ[x]:
            lines.append(f"  - assume Hy_eq: y = {y}.")
            lines.append(f"    rewrite Hx_eq in Hxz.")
            lines.append(f"    rewrite Hy_eq in Hyz.")
            lines.append(f"    apply Adj17_cases_{y} in Hyz.")
            lines.append("    apply Hyz.")
            for z in ADJ[y]:
                if (x, z) in EDGE_SET:
                    raise ValueError(f"Triangle would exist at {x}-{y}-{z}")
                lines.append(f"    - assume Hz_eq: z = {z}.")
                lines.append(f"      rewrite Hz_eq in Hxz.")
                lines.append(f"      apply Adj17_not_{x}_{z}.")
                lines.append("      exact Hxz.")
    lines.append("Qed.")
    lines.append(f"(* Proof branches: {len(paths)} two-edge paths *)")
    return "\n".join(lines)


def main():
    out_path = Path(__file__).with_name("adj17_triangle_free_auto.mg")
    parts = [
        "(* Auto-generated by gen_adj17_reconstruct_alt.py *)",
        gen_adj_definition(),
        gen_all_nonedge_lemmas(),
        gen_all_cases_lemmas(),
        gen_triangle_free(),
    ]
    out_path.write_text("\n\n".join(parts))
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
