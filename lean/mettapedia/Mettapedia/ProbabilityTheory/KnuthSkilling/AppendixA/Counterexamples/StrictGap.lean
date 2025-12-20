import Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Core.Induction.ThetaPrime

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Counterexamples

open Classical KnuthSkillingAlgebra

variable {α : Type*} [KnuthSkillingAlgebra α]

/-!
# Sanity check: Δ=1 gap vs `ZQuantized`

This file is a *consistency check* about a common proof pattern that shows up in the B-empty
discussion (K&S Appendix A.3.4).

If you simultaneously have:
- `hZQ : ZQuantized F R δ` for some `δ > 0`, and
- a strict μ-increase `mu F r_old_y < mu F r_old_x`,

then the gap in Θ is at least one δ-step (`zquantized_gap_ge_delta`).

So, for Δ=1, any attempt to prove a strict upper bound of the form:
`Θx - Θy < δ`
for the *same* `δ` immediately contradicts the ZQuantized lower bound.

This does **not** refute K&S Appendix A by itself; it just forces you to be careful about which
δ is used for which quantization/approximation argument.
-/

theorem delta_one_gap_contradiction
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d)
    (hZQ : ZQuantized F R (chooseδ hk R d hd))
    (r_old_x r_old_y : Multi k)
    (h_mu : mu F r_old_y < mu F r_old_x)
    (h_gap_lt : R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
        R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ < chooseδ hk R d hd) :
    False := by
  have hδ_pos : 0 < chooseδ hk R d hd := delta_pos hk R IH H d hd
  have h_ge : chooseδ hk R d hd ≤
      R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
        R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ :=
    zquantized_gap_ge_delta hδ_pos hZQ r_old_x r_old_y h_mu
  linarith

end Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Counterexamples
