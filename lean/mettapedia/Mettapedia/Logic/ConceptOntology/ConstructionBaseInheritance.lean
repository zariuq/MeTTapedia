import Mettapedia.Logic.ExtensionalIntensionalDivergence

/-!
# Construction-Base Inheritance Bridge

This module repackages the existing inheritance credal-width layer in the same
`That’s All` / `Open World` vocabulary used by the construction-base API.

It introduces no new semantics:

* `inheritanceThatsAll` means the inheritance credal width has collapsed to `0`,
* `inheritanceOpenWorld` means the inheritance credal width is still positive.
-/

namespace Mettapedia.Logic.ConceptOntology

open Mettapedia.Logic

universe u v w z

section InheritanceOT

variable {Carrier : Type u} {Obj : Type v} {Attr : Type w} {Gate : Type z}
variable [Fintype Gate] [Nonempty Gate] [Fintype Obj] [Fintype Attr]

/-- Credal inheritance "that's all": every admissible gate assigns the same full
inheritance strength, so the inheritance interval has collapsed to width `0`. -/
def inheritanceThatsAll
    (J : Gate → AbstractInheritance.Interpretation Carrier Obj Attr)
    (sub super : Carrier) : Prop :=
  Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceCredalWidth J sub super = 0

/-- Credal inheritance open-world: the gate family still leaves positive
inheritance width, so the judgment remains genuinely imprecise. -/
def inheritanceOpenWorld
    (J : Gate → AbstractInheritance.Interpretation Carrier Obj Attr)
    (sub super : Carrier) : Prop :=
  0 < Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceCredalWidth J sub super

omit [Fintype Obj] [Fintype Attr] in
theorem inheritanceThatsAll_iff_inheritanceCredalWidth_eq_zero
    (J : Gate → AbstractInheritance.Interpretation Carrier Obj Attr)
    (sub super : Carrier) :
    inheritanceThatsAll J sub super ↔
      Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceCredalWidth J sub super = 0 := by
  rfl

omit [Fintype Obj] [Fintype Attr] in
theorem inheritanceThatsAll_iff_all_gates_agree
    (J : Gate → AbstractInheritance.Interpretation Carrier Obj Attr)
    (sub super : Carrier) :
    inheritanceThatsAll J sub super ↔
      ∀ g h : Gate, Mettapedia.Logic.ExtensionalIntensionalDivergence.fullInheritanceStrength (J g) sub super =
        Mettapedia.Logic.ExtensionalIntensionalDivergence.fullInheritanceStrength (J h) sub super := by
  simpa [inheritanceThatsAll] using
    (Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceCredalWidth_eq_zero_iff J sub super)

omit [Fintype Obj] [Fintype Attr] in
theorem inheritanceOpenWorld_iff_not_inheritanceThatsAll
    (J : Gate → AbstractInheritance.Interpretation Carrier Obj Attr)
    (sub super : Carrier) :
    inheritanceOpenWorld J sub super ↔ ¬ inheritanceThatsAll J sub super := by
  constructor
  · intro hOpen hAll
    unfold inheritanceOpenWorld at hOpen
    unfold inheritanceThatsAll at hAll
    simp [hAll] at hOpen
  · intro hNot
    have hnonneg : 0 ≤ Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceCredalWidth J sub super :=
      Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceCredalWidth_nonneg J sub super
    have hne :
        Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceCredalWidth J sub super ≠ 0 := by
      intro hZero
      exact hNot (by simpa [inheritanceThatsAll] using hZero)
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)

omit [Fintype Obj] [Fintype Attr] in
theorem inheritanceOpenWorld_iff_not_all_gates_agree
    (J : Gate → AbstractInheritance.Interpretation Carrier Obj Attr)
    (sub super : Carrier) :
    inheritanceOpenWorld J sub super ↔
      ¬ ∀ g h : Gate, Mettapedia.Logic.ExtensionalIntensionalDivergence.fullInheritanceStrength (J g) sub super =
          Mettapedia.Logic.ExtensionalIntensionalDivergence.fullInheritanceStrength (J h) sub super := by
  constructor
  · intro hOpen hAgree
    have hAll : inheritanceThatsAll J sub super :=
      (inheritanceThatsAll_iff_all_gates_agree (J := J) (sub := sub) (super := super)).2 hAgree
    exact (inheritanceOpenWorld_iff_not_inheritanceThatsAll (J := J) (sub := sub) (super := super)).1 hOpen hAll
  · intro hNotAgree
    have hNotAll : ¬ inheritanceThatsAll J sub super := by
      intro hAll
      exact hNotAgree
        ((inheritanceThatsAll_iff_all_gates_agree (J := J) (sub := sub) (super := super)).1 hAll)
    exact (inheritanceOpenWorld_iff_not_inheritanceThatsAll (J := J) (sub := sub) (super := super)).2 hNotAll

end InheritanceOT

end Mettapedia.Logic.ConceptOntology
