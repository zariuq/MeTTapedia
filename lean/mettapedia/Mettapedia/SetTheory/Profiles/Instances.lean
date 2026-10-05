import Mettapedia.SetTheory.Profiles.Foundation
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ZFSet

/-!
# Membership induction in existing carriers

Mathlib's `ZFSet` satisfies membership induction. The well-founded hypersets
are exactly those `ZFSet`s, by `wellFoundedPartEquivZFSet`, and membership
induction transports along that equivalence. The hyperset carrier has Aczel's
Quine atom `Ω = {Ω}`, so membership induction fails there.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles

universe u

open Mettapedia.TypeTheory.MaterialSets.Hypersets

/-- Mathlib's sets satisfy membership induction. -/
theorem zfSet_memInduction : HasMemInduction (S := ZFSet.{u}) (· ∈ ·) :=
  fun _ step x => ZFSet.inductionOn x step

/-- Membership in the well-founded part agrees with membership of the
corresponding `ZFSet`s. -/
theorem wellFoundedPart_mem_iff_zfSet {x y : WellFoundedPart.{u}} :
    x.1 ∈ y.1 ↔ HSet.wellFoundedPartEquivZFSet x ∈ HSet.wellFoundedPartEquivZFSet y :=
  HSet.wellFoundedPartEquivZFSet_mem_iff.symm

/-- The well-founded hypersets satisfy membership induction. -/
theorem wellFoundedPart_memInduction :
    HasMemInduction (fun (x y : WellFoundedPart.{u}) => x.1 ∈ y.1) := by
  intro motive step w
  let e := HSet.wellFoundedPartEquivZFSet.{u}
  have transported : ∀ a : ZFSet.{u}, motive (e.symm a) := fun a =>
    ZFSet.inductionOn a fun a ih => by
      apply step (e.symm a)
      intro y hy
      have eqY : e.symm (e y) = y := Equiv.symm_apply_apply e y
      have hym : e y ∈ a :=
        (HSet.mem_wellFoundedPartEquivZFSet_symm_iff (x := e y) (y := a)).mp
          (eqY.symm ▸ hy)
      exact eqY ▸ ih (e y) hym
  exact Equiv.symm_apply_apply e w ▸ transported (e w)

/-- The hyperset carrier has a Quine atom. -/
theorem hset_hasQuineAtom : HasQuineAtom (S := HSet.{u}) (· ∈ ·) :=
  ⟨HSet.quineAtom, fun _ => HSet.mem_quineAtom⟩

/-- Aczel's atom belongs to itself. -/
theorem hset_quineAtom_mem_self : HSet.quineAtom.{u} ∈ HSet.quineAtom :=
  HSet.quineAtom_mem_self

/-- Aczel's atom is not well-founded. -/
theorem hset_quineAtom_not_wellFounded : ¬ HSet.quineAtom.{u}.WF :=
  HSet.not_wf_quineAtom

/-- Membership induction fails for hypersets. -/
theorem hset_refutes_memInduction : ¬ HasMemInduction (S := HSet.{u}) (· ∈ ·) :=
  quineAtom_refutes_induction hset_hasQuineAtom

end Mettapedia.SetTheory.Profiles
