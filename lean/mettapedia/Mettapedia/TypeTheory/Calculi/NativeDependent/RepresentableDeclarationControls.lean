import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableDeclarationSubstitution
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Types.Basic

/-!
# Nonconstant functions and proper generalized predicates

The categorical join retains Boolean negation at both inputs, earns its
actual double-negation composite, and rejects its identification with the
identity. A proper representable predicate quantifies over every supplied
argument. Generated substitution reverses its two point tests exactly, and
a failed point prevents every generated entailment derivation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableDeclarations.Controls

open _root_.CategoryTheory Opposite

noncomputable section

abbrev Base := AsSmall.{0} (Type)
abbrev boolObject : Base := ⟨Bool⟩
abbrev unitObject : Base := ⟨PUnit⟩

def negation : boolObject ⟶ boolObject := ⟨↾Bool.not⟩
def point (value : Bool) : unitObject ⟶ boolObject := ⟨↾fun _ => value⟩

theorem negation_involutive : negation ≫ negation = 𝟙 boolObject := by
  apply ULift.ext
  apply ConcreteCategory.hom_ext
  intro value
  cases value <;> rfl

theorem negation_not_identity : negation ≠ 𝟙 boolObject := by
  intro same
  have read := congrArg (fun arrow : boolObject ⟶ boolObject => arrow.down false) same
  exact Bool.false_ne_true read.symm

theorem source_identity_is_an_actual_quotient_identity :
    (originalFunctor (C := Base)).map (𝟙 boolObject) =
      𝟙 ((originalFunctor (C := Base)).obj boolObject) :=
  (originalFunctor (C := Base)).map_id boolObject

theorem distinct_source_functions_remain_distinct :
    (originalFunctor (C := Base)).map negation ≠
      𝟙 ((originalFunctor (C := Base)).obj boolObject) := by
  rw [← (originalFunctor (C := Base)).map_id boolObject]
  intro same
  exact negation_not_identity ((originalFunctor (C := Base)).map_injective same)

theorem generated_double_negation :
    (originalFunctor (C := Base)).map negation ≫ (originalFunctor (C := Base)).map negation =
      𝟙 ((originalFunctor (C := Base)).obj boolObject) := by
  rw [← (originalFunctor (C := Base)).map_comp, negation_involutive]
  exact source_identity_is_an_actual_quotient_identity

theorem complete_both_input_readout (value : Bool) :
    (objectName boolObject).app (op unitObject)
      ((conservedReadout.map ((originalFunctor (C := Base)).map negation)).app (op unitObject)
        ((objectNameInverse boolObject).app (op unitObject) (point value))) = point (Bool.not value) := by
  rw [originalFunctor_generalized_readout]
  rfl

theorem generated_equality_cannot_hide_negation :
    ¬Nonempty (Derivation (signature Base) (.termEq (objectContext boolObject)
      (arrowTerm negation (.var 0)) (arrowTerm (𝟙 boolObject) (.var 0)) (objectType boolObject 1))) := by
  rw [generated_arrow_equality_iff]
  exact negation_not_identity

def allTrue : Subfunctor (yoneda.obj boolObject) where
  obj world := {argument | ∀ value : ULift.down world.unop, argument.down value = true}
  map := by
    intro first second before argument accepted value
    exact accepted (before.unop.down value)

theorem positive_point : point true ∈ allTrue.obj (op unitObject) := fun _ => rfl

theorem negative_point : point false ∉ allTrue.obj (op unitObject) := by
  intro accepted
  exact Bool.false_ne_true (accepted PUnit.unit)

theorem proper_predicate : allTrue ≠ ⊤ := by
  intro same
  have accepted : point false ∈ (⊤ : Subfunctor (yoneda.obj boolObject)).obj (op unitObject) :=
    Set.mem_univ _
  rw [← same] at accepted
  exact negative_point accepted

theorem present_truth_is_preserved_by_every_future {world future : Base}
    (argument : world ⟶ boolObject) (accepted : argument ∈ allTrue.obj (op world))
    (before : future ⟶ world) : before ≫ argument ∈ allTrue.obj (op future) :=
  allTrue.map before.op accepted

theorem variable_argument_fails_the_whole_predicate :
    (𝟙 boolObject) ∉ allTrue.obj (op boolObject) := by
  intro accepted
  exact Bool.false_ne_true (accepted false)

theorem a_future_point_can_satisfy_the_predicate :
    point true ≫ (𝟙 boolObject) ∈ allTrue.obj (op unitObject) := by
  rw [Category.comp_id]
  exact positive_point

theorem substituted_predicate_reads_both_points (value : Bool) :
    (objectNameInverse boolObject).app (op unitObject) (point value) ∈
      ((allTrue.preimage (yoneda.map negation)).preimage (objectName boolObject)).obj
        (op unitObject) ↔ Bool.not value = true := by
  change (∀ _ : PUnit, Bool.not value = true) ↔ Bool.not value = true
  exact ⟨fun accepted => accepted PUnit.unit, fun accepted _ => accepted⟩

theorem actual_generated_predicate_substitution :
    (model Base).evaluatePredicate (objectScope boolObject)
      ((predicateTerm allTrue (.var 0)).substitute (originalArrow negation).substitution) =
        some ((allTrue.preimage (yoneda.map negation)).preimage (objectName boolObject)) :=
  complete_original_predicate_substitution negation allTrue

theorem failed_point_rules_out_all_generated_entailments :
    ¬Nonempty (Derivation (signature Base) (.entails (objectContext boolObject)
      (predicateTerm allTrue (.var 0)))) :=
  failed_test_prevents_generated_entailment allTrue (point false) negative_point

theorem all_dependent_rules_still_cannot_identify_the_proper_predicate_with_truth :
    ¬Nonempty (Derivation (signature Base) (.predicateEq (objectContext boolObject)
      (predicateTerm allTrue (.var 0)) (predicateTerm (⊤ : Subfunctor (yoneda.obj boolObject)) (.var 0)))) := by
  rw [generated_predicate_equality_iff]
  exact proper_predicate

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableDeclarations.Controls
