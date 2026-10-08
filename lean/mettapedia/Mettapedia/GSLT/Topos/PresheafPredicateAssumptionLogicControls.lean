import Mettapedia.GSLT.Topos.PresheafPredicateAssumptionLogic
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Satisfying contexts and image coverage controls

A Boolean assumption holds in its selected context but fails at an
unrestricted false input. An actual pair section supplies an existential
witness. A map omitting false shows why image elimination must retain its
coverage premise.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.PresheafPredicateAssumptionLogicControls

open _root_.CategoryTheory PresheafPredicateAssumptionLogic

abbrev World := Discrete (PUnit.{1})
abbrev booleans : World ⥤ Type := (Functor.const _).obj Bool
abbrev pairs : World ⥤ Type := (Functor.const _).obj (Bool × Bool)
abbrev spot : World := Discrete.mk PUnit.unit

def trueOnly : Subfunctor booleans where
  obj _ := {value | value = true}
  map _ := by intro value member; exact member

def secondTrue : Subfunctor pairs where
  obj _ := {value | value.2 = true}
  map _ := by intro value member; exact member

def firstProjection : pairs ⟶ booleans where
  app _ := TypeCat.ofHom Prod.fst
  naturality := by intros; rfl

def suppliedPair : booleans ⟶ pairs where
  app _ := TypeCat.ofHom fun value => (value, true)
  naturality := by intros; rfl

def alwaysTrue : booleans ⟶ booleans where
  app _ := TypeCat.ofHom fun _ => true
  naturality := by intros; rfl

theorem selected_assumption_holds : trueOnly.preimage trueOnly.ι = ⊤ :=
  assumption_holds trueOnly

theorem conditional_implication_holds : himpPointwise trueOnly trueOnly = ⊤ :=
  implication_top trueOnly trueOnly selected_assumption_holds

theorem unrestricted_false_excluded : false ∉ trueOnly.obj spot := Bool.false_ne_true

theorem selected_truth_does_not_establish_global_truth : trueOnly ≠ ⊤ := by
  intro equal
  have impossible : false ∈ trueOnly.obj spot := equal.symm ▸ trivial
  exact unrestricted_false_excluded impossible

theorem supplied_pair_projects : suppliedPair ≫ firstProjection = 𝟙 booleans := by
  ext world value
  rfl

theorem supplied_pair_satisfies : secondTrue.preimage suppliedPair = ⊤ := by
  ext world value
  constructor
  · intro _
    trivial
  · intro _
    rfl

theorem supplied_witness_establishes_existential : secondTrue.image firstProjection = ⊤ :=
  existential_section firstProjection secondTrue suppliedPair
    supplied_pair_projects supplied_pair_satisfies

theorem every_supplied_image_satisfies : trueOnly.preimage alwaysTrue = ⊤ := by
  ext world value
  constructor
  · intro _
    trivial
  · intro _
    rfl

theorem omitted_input_prevents_coverage : Subfunctor.range alwaysTrue ≠ ⊤ := by
  intro equal
  have impossible : false ∈ (Subfunctor.range alwaysTrue).obj spot := equal.symm ▸ trivial
  rcases impossible with ⟨argument, equation⟩
  exact (by decide : true ≠ false) equation

theorem image_truth_alone_does_not_give_unrestricted_truth :
    trueOnly.preimage alwaysTrue = ⊤ ∧ trueOnly ≠ ⊤ :=
  ⟨every_supplied_image_satisfies, selected_truth_does_not_establish_global_truth⟩

end Mettapedia.GSLT.Topos.PresheafPredicateAssumptionLogicControls
