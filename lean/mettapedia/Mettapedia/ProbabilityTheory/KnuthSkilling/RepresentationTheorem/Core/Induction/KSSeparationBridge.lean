import Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.Core.Induction.Goertzel
import Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.Core.SeparationImpliesCommutative

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem

open Classical
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra
open SandwichSeparation.SeparationToArchimedean

variable {α : Type*} [KnuthSkillingAlgebra α] [KSSeparation α]

/-!
## Bridging: using `KSSeparation` to supply commutativity

Goertzel’s separation note (`literature/Foundations-of-inference-new-proofs_*.pdf`) proposes replacing
the separate assumptions “commutativity” + “Archimedean” by a single strengthening axiom
`KSSeparation`.

In this Lean codebase:
- The *Archimedean* part is already bundled into `KnuthSkillingAlgebra` (see `.../Basic.lean`).
- The remaining hard content is showing that `KSSeparation` forces commutativity; this is now
  proven (sorry-free) in `.../Separation/SandwichSeparation.lean` and re-exported via the theorem
  `Core.op_comm_of_KSSeparation`.

This file provides a tiny convenience wrapper: using
`Core.separationImpliesCommutative_of_KSSeparation`, the existing extension lemma
can be used without adding commutativity as an extra axiom.
-/

/-- Wrapper: `KSSeparation` supplies commutativity, and the B-empty extension
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

end Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem
