import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableGuardedFamilies
import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableDeclarationControls

/-!
# Varying native fibres with complete natural-number witnesses

The original Boolean predicate guards an independently supplied natural
number. Accepted arguments retain every supplied value, while rejected
arguments have no inhabitants. Restriction retains the complete generalized
value, and the actual generated substitution by negation reverses admission.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableDeclarations.GuardedControls

open _root_.CategoryTheory Opposite
open ContextualModelTelescopes NativeLocalTypeFormers
open Controls

noncomputable section

abbrev naturalObject : Base := ⟨Nat⟩

def naturalPoint (value : Nat) : unitObject ⟶ naturalObject := ⟨↾fun _ => value⟩

def argument (value : Bool) : (objectScope boolObject).1.obj (op unitObject) :=
  (objectNameInverse boolObject).app (op unitObject) (point value)

abbrev guardedFamily := GuardedObject.typeMeaning naturalObject allTrue

def generatedFormation :
    Derivation (signature Base) (.type (objectContext boolObject)
      (GuardedObject.typeCode naturalObject allTrue)) :=
  GuardedObject.typeFormed naturalObject allTrue

theorem independently_authored_type_reads_the_actual_native_family :
    (model Base).evaluateType (objectScope boolObject)
      (GuardedObject.typeCode naturalObject allTrue) = some guardedFamily :=
  GuardedObject.type_read naturalObject allTrue

def positiveValue (value : Nat) : guardedFamily.decoded.obj ⟨op unitObject, argument true⟩ :=
  GuardedObject.suppliedInhabitant naturalObject allTrue (op unitObject)
    (argument true) (naturalPoint value) positive_point

theorem positive_value_retains_its_complete_arrow (value : Nat) :
    (GuardedObject.fibreEquiv naturalObject allTrue (op unitObject) (argument true)
      (positiveValue value)).val = naturalPoint value :=
  GuardedObject.suppliedInhabitant_complete_readout naturalObject allTrue
    (op unitObject) (argument true) (naturalPoint value) positive_point

theorem positive_value_reads_the_supplied_number (value : Nat) :
    (GuardedObject.fibreEquiv naturalObject allTrue (op unitObject) (argument true)
      (positiveValue value)).val.down PUnit.unit = value := by
  rw [positive_value_retains_its_complete_arrow]
  rfl

theorem distinct_numbers_retain_distinct_native_witnesses {first second : Nat}
    (different : first ≠ second) : positiveValue first ≠ positiveValue second := by
  intro same
  have read := congrArg (fun value =>
    (GuardedObject.fibreEquiv naturalObject allTrue (op unitObject) (argument true)
      value).val.down PUnit.unit) same
  rw [positive_value_reads_the_supplied_number, positive_value_reads_the_supplied_number] at read
  exact different read

theorem nine_and_twelve_remain_distinct : positiveValue 9 ≠ positiveValue 12 :=
  distinct_numbers_retain_distinct_native_witnesses (by decide)

theorem positive_fibre_is_inhabited :
    Nonempty (guardedFamily.decoded.obj ⟨op unitObject, argument true⟩) :=
  ⟨positiveValue 9⟩

theorem negative_fibre_is_empty :
    IsEmpty (guardedFamily.decoded.obj ⟨op unitObject, argument false⟩) :=
  GuardedObject.failed_argument_has_no_inhabitant naturalObject allTrue
    (op unitObject) (argument false) negative_point

theorem the_two_native_fibres_are_different :
    guardedFamily.decoded.obj ⟨op unitObject, argument true⟩ ≠
      guardedFamily.decoded.obj ⟨op unitObject, argument false⟩ := by
  intro same
  exact negative_fibre_is_empty.false (same ▸ positiveValue 9)

theorem restriction_retains_the_whole_number_arrow {world future : Baseᵒᵖ}
    (before : world ⟶ future) (acceptedArgument : (objectScope boolObject).1.obj world)
    (value : guardedFamily.decoded.obj ⟨world, acceptedArgument⟩) :
    (GuardedObject.fibreEquiv naturalObject allTrue future
      ((objectScope boolObject).1.map before acceptedArgument)
      (guardedFamily.decoded.map ⟨before, rfl⟩ value)).val =
        before.unop ≫ (GuardedObject.fibreEquiv naturalObject allTrue world acceptedArgument value).val :=
  GuardedObject.restriction_retains_inhabitant naturalObject allTrue before acceptedArgument value

theorem actual_generated_negation_substitution :
    (model Base).evaluateType (objectScope boolObject)
      ((GuardedObject.typeCode naturalObject allTrue).substitute
        (originalArrow negation).substitution) =
      some (guardedFamily.reindex (originalPresheafArrow negation)) :=
  GuardedObject.original_substitution negation allTrue

theorem substituted_false_argument_is_accepted :
    (objectName boolObject).app (op unitObject)
      ((originalPresheafArrow negation).app (op unitObject) (argument false)) ∈
        allTrue.obj (op unitObject) := by
  change (∀ _ : PUnit, Bool.not false = true)
  intro value
  rfl

theorem substituted_true_argument_is_rejected :
    (objectName boolObject).app (op unitObject)
      ((originalPresheafArrow negation).app (op unitObject) (argument true)) ∉
        allTrue.obj (op unitObject) := by
  change ¬(∀ _ : PUnit, Bool.not true = true)
  intro accepted
  exact Bool.false_ne_true (accepted PUnit.unit)

theorem substituted_false_fibre_is_inhabited :
    Nonempty ((guardedFamily.reindex (originalPresheafArrow negation)).decoded.obj
      ⟨op unitObject, argument false⟩) :=
  ⟨GuardedObject.suppliedInhabitant naturalObject allTrue (op unitObject)
    ((originalPresheafArrow negation).app (op unitObject) (argument false))
    (naturalPoint 12) substituted_false_argument_is_accepted⟩

theorem substituted_true_fibre_is_empty :
    IsEmpty ((guardedFamily.reindex (originalPresheafArrow negation)).decoded.obj
      ⟨op unitObject, argument true⟩) :=
  GuardedObject.failed_argument_has_no_inhabitant naturalObject allTrue (op unitObject)
    ((originalPresheafArrow negation).app (op unitObject) (argument true))
    substituted_true_argument_is_rejected

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableDeclarations.GuardedControls
