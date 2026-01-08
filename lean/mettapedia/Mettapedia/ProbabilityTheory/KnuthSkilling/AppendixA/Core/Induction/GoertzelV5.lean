import Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Core.Induction.Goertzel
import Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Core.SeparationImpliesCommutative

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA

open Classical KnuthSkillingAlgebra

variable {α : Type*} [KnuthSkillingAlgebra α]

/-!
## Goertzel v5 in the refactored Core/Induction pipeline

Goertzel v5 (`literature/Foundations-of-inference-new-proofs_v5.pdf`) proposes replacing the
separate assumptions “commutativity” + “Archimedean” by a single strengthening axiom
`KSSeparation`.

In this Lean codebase:
- The *Archimedean* part is already bundled into `KnuthSkillingAlgebra` (see `.../Basic.lean`).
- The remaining hard content is the conjecture that `KSSeparation` forces commutativity; this is
  recorded (sorry-free) as the Prop `Core.SeparationImpliesCommutative`.

This file provides a tiny convenience wrapper: using the v5 theorem
`Core.separationImpliesCommutative_of_KSSeparation`, the existing Goertzel v4-style extension lemma
can be used without adding commutativity as an extra axiom.
-/

/-- Goertzel v5-style wrapper: `KSSeparation` supplies commutativity, and the B-empty extension
step then needs only `KSSeparationStrict` (for the strict C-side). -/
theorem extend_grid_rep_with_atom_of_KSSeparation_of_KSSeparationStrict
    {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F) (hk : 0 < k)
    {d : α} (hd : ident < d)
    (IH : GridBridge F) (H : GridComm F)
    [KSSeparation α] [KSSeparationStrict α] :
      ∃ (F' : AtomFamily α (k + 1)),
      (∀ i : Fin k, F'.atoms ⟨i, Nat.lt_succ_of_lt i.is_lt⟩ = F.atoms i) ∧
      F'.atoms ⟨k, Nat.lt_succ_self k⟩ = d ∧
      ∃ (R' : MultiGridRep F'),
        (∀ r_old : Multi k, ∀ t : ℕ,
          R'.Θ_grid ⟨mu F' (joinMulti r_old t), mu_mem_kGrid F' (joinMulti r_old t)⟩ =
          R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (t : ℝ) * chooseδ hk R d hd) := by
  have hop_comm : ∀ x y : α, op x y = op y x :=
    Core.separationImpliesCommutative_of_KSSeparation (α := α)
  exact
    extend_grid_rep_with_atom_of_op_comm_of_KSSeparationStrict (α := α) (k := k) (F := F) (R := R)
      (hk := hk) (d := d) (hd := hd) (IH := IH) (H := H) (hcomm := hop_comm)

end Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA
