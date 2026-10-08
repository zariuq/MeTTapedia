import Mettapedia.GSLT.Core.ContextualTypeReindexing

/-!
# Cartesian factorization of display substitutions

A substitution between display contexts whose projections commute with a
supplied base arrow factors uniquely through the selected comprehension lift.
The factor is constructed from the actual reading of the target generic
variable. Existence and computation accompany the previously available
cancellation theorem.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualDisplayCartesianFactor

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder

universe u v w w'
variable {C : Cwf.{u, v, w, w'}} {Γ Δ : C.Ctx}
  {A : TypeOver C Γ} {B : TypeOver C Δ}

/-- The supplied target-variable readout, retyped by the actual projection
square. This cast retains the original section. -/
def factorTerm (base : C.Sub Γ Δ)
    (arrow : C.Sub (C.ext Γ A.val) (C.ext Δ B.val))
    (over : C.compS (C.wk B.val) arrow = C.compS base (C.wk A.val)) :
    C.Tm (C.ext Γ A.val) (C.tySub (C.tySub B.val base) (C.wk A.val)) :=
  cast (by rw [← C.tySub_comp, over, C.tySub_comp]) (C.tmSub (C.vz B.val) arrow)

theorem factorTerm_readout (base : C.Sub Γ Δ)
    (arrow : C.Sub (C.ext Γ A.val) (C.ext Δ B.val))
    (over : C.compS (C.wk B.val) arrow = C.compS base (C.wk A.val)) :
    HEq (factorTerm base arrow over) (C.tmSub (C.vz B.val) arrow) := cast_heq _ _

/-- The actual display map into the reindexed target family. -/
def factor (base : C.Sub Γ Δ)
    (arrow : C.Sub (C.ext Γ A.val) (C.ext Δ B.val))
    (over : C.compS (C.wk B.val) arrow = C.compS base (C.wk A.val)) :
    A ⟶ TypeOver.reindexObject base B :=
  TypeOver.ofTerm (factorTerm base arrow over)

/-- Following the factor by the selected cartesian lift recovers the
complete supplied substitution. -/
theorem factor_composes (base : C.Sub Γ Δ)
    (arrow : C.Sub (C.ext Γ A.val) (C.ext Δ B.val))
    (over : C.compS (C.wk B.val) arrow = C.compS base (C.wk A.val)) :
    C.compS (TypeOver.extensionSubstitution base B.val)
      (factor base arrow over).substitution = arrow := by
  apply TypeOver.substitution_ext
  · calc
      C.compS (C.wk B.val)
          (C.compS (TypeOver.extensionSubstitution base B.val)
            (factor base arrow over).substitution) =
          C.compS (C.compS (C.wk B.val) (TypeOver.extensionSubstitution base B.val))
            (factor base arrow over).substitution := (C.comp_assoc _ _ _).symm
      _ = C.compS (C.compS base (C.wk (C.tySub B.val base)))
          (factor base arrow over).substitution := by rw [TypeOver.wk_extensionSubstitution]
      _ = C.compS base (C.compS (C.wk (C.tySub B.val base))
          (factor base arrow over).substitution) := C.comp_assoc _ _ _
      _ = C.compS base (C.wk A.val) := by rw [(factor base arrow over).over]
      _ = C.compS (C.wk B.val) arrow := over.symm
  · have readTypes :
        C.tySub (C.tySub B.val (C.wk B.val))
          (TypeOver.extensionSubstitution base B.val) =
        C.tySub (C.tySub B.val base) (C.wk (C.tySub B.val base)) := by
      rw [← C.tySub_comp, TypeOver.wk_extensionSubstitution, C.tySub_comp]
    exact (TypeOver.tmSub_comp_heq (C.vz B.val)
      (TypeOver.extensionSubstitution base B.val) (factor base arrow over).substitution).trans
      ((TypeOver.tmSub_heq readTypes (TypeOver.vz_extensionSubstitution base B.val)
        (factor base arrow over).substitution).trans
        ((TypeOver.vz_ofTerm_heq (factorTerm base arrow over)).trans
          (factorTerm_readout base arrow over)))

/-- The computation equation determines the display factor uniquely. -/
theorem factor_unique (base : C.Sub Γ Δ)
    (arrow : C.Sub (C.ext Γ A.val) (C.ext Δ B.val))
    (over : C.compS (C.wk B.val) arrow = C.compS base (C.wk A.val))
    (other : A ⟶ TypeOver.reindexObject base B)
    (computed : C.compS (TypeOver.extensionSubstitution base B.val)
      other.substitution = arrow) : other = factor base arrow over :=
  TypeOver.extensionSubstitution_cancel base
    (computed.trans (factor_composes base arrow over).symm)

/-- Any display factorization must satisfy the actual projection square.
This is a necessary admission condition, independent of the construction. -/
theorem factorization_implies_over (base : C.Sub Γ Δ)
    (arrow : C.Sub (C.ext Γ A.val) (C.ext Δ B.val))
    (candidate : A ⟶ TypeOver.reindexObject base B)
    (computed : C.compS (TypeOver.extensionSubstitution base B.val)
      candidate.substitution = arrow) :
    C.compS (C.wk B.val) arrow = C.compS base (C.wk A.val) := by
  rw [← computed]
  calc
    _ = C.compS (C.compS (C.wk B.val) (TypeOver.extensionSubstitution base B.val))
        candidate.substitution := (C.comp_assoc _ _ _).symm
    _ = C.compS (C.compS base (C.wk (C.tySub B.val base))) candidate.substitution :=
      congrArg (fun substitution => C.compS substitution candidate.substitution)
        (TypeOver.wk_extensionSubstitution base B.val)
    _ = C.compS base (C.compS (C.wk (C.tySub B.val base)) candidate.substitution) :=
      C.comp_assoc _ _ _
    _ = C.compS base (C.wk A.val) := congrArg (C.compS base) candidate.over

end Mettapedia.TypeTheory.ContextualDisplayCartesianFactor
