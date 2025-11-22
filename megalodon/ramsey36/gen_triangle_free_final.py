#!/usr/bin/env python3
"""Generate the final Adj17_triangle_free proof using cases_17."""

def generate_triangle_free_proof():
    """Generate the proof that wires together all tf_x_y_z lemmas."""
    lines = []

    lines.append("Theorem Adj17_triangle_free : triangle_free 17 Adj17.")
    lines.append("prove forall x :e 17, forall y :e 17, forall z :e 17, Adj17 x y -> Adj17 y z -> Adj17 x z -> False.")
    lines.append("let x. assume Hx: x :e 17.")
    lines.append("apply cases_17 x Hx (fun x => forall y :e 17, forall z :e 17, Adj17 x y -> Adj17 y z -> Adj17 x z -> False).")

    # For each x = 0..16
    for x in range(17):
        lines.append(f"- prove forall y :e 17, forall z :e 17, Adj17 {x} y -> Adj17 y z -> Adj17 {x} z -> False.")
        lines.append(f"  let y. assume Hy: y :e 17.")
        lines.append(f"  apply cases_17 y Hy (fun y => forall z :e 17, Adj17 {x} y -> Adj17 y z -> Adj17 {x} z -> False).")

        # For each y = 0..16
        for y in range(17):
            lines.append(f"  - prove forall z :e 17, Adj17 {x} {y} -> Adj17 {y} z -> Adj17 {x} z -> False.")
            lines.append(f"    let z. assume Hz: z :e 17.")
            lines.append(f"    apply cases_17 z Hz (fun z => Adj17 {x} {y} -> Adj17 {y} z -> Adj17 {x} z -> False).")

            # For each z = 0..16
            for z in range(17):
                lines.append(f"    - exact tf_{x}_{y}_{z}.")

    lines.append("Qed.")
    return "\n".join(lines)

if __name__ == "__main__":
    proof = generate_triangle_free_proof()
    print(proof)
