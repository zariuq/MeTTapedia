import Mettapedia.CategoryTheory.RelativeClosedSyntaxInterpretationClosed
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Monoidal.Closed.Types

/-!
# Complete native witnesses of finite-limit and closed interpretation

An independently declared identity and Boolean negation are interpreted over
a small discrete base. The actual canonical exponential comparison retains
both supplied arguments of negation. Equalizing identity with itself retains
the supplied Boolean, whereas equalizing identity with negation has no native
inhabitant. These are readouts of the earned quotient functor, not supplied
preservation laws.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedInterpretationPreservationControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open Mettapedia.CategoryTheory.RelativeClosedSyntax.GeneratedCategory
open Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation

abbrev Base := Discrete Unit

abbrev names : Symbols where
  ObjectName := Unit
  ArrowName := Bool
  EquationName := Empty

def signature : Signature (C := Base) (symbols := names) where
  objectRank _ := 0
  arrowRank _ := 1
  source _ := .name ()
  target _ := .name ()
  source_before _ := by simp only [ObjectCode.before]; decide
  target_before _ := by simp only [ObjectCode.before]; decide
  equationRank origin := origin.elim
  equationSource origin := origin.elim
  equationTarget origin := origin.elim
  left origin := origin.elim
  right origin := origin.elim
  equation_before origin := origin.elim

def negate : Bool ⟶ Bool := TypeCat.ofHom Bool.not

def meanings : Assignment Base names Type where
  base := (Functor.const Base).obj PUnit
  object _ := Bool
  arrow name := ⟨Bool, Bool, if name then negate else 𝟙 Bool⟩

theorem realized : Realization signature meanings where
  source _ := rfl
  target _ := rfl
  equation origin := origin.elim

abbrev dataObject : Object signature :=
  ⟨.name (), ⟨.objectName (signature := signature) ()⟩⟩

def namedRaw (name : Bool) : RawHom dataObject dataObject :=
  ⟨.name name, ⟨by
    change Derivation signature (.arrow (.name ()) (.name ()) (.name name))
    exact .arrowName (signature := signature) name dataObject.formed.some dataObject.formed.some⟩⟩

def declared (name : Bool) : dataObject ⟶ dataObject := classOf (namedRaw name)

abbrev interpreted : Object signature ⥤ Type := functor meanings realized

theorem actual_identity : interpreted.map (declared false) = 𝟙 Bool :=
  rawArrowValue_unique meanings realized (namedRaw false) (𝟙 Bool) rfl

theorem actual_negation : interpreted.map (declared true) = negate :=
  rawArrowValue_unique meanings realized (namedRaw true) negate rfl

theorem interpretation_is_lex : PreservesFiniteLimits interpreted := inferInstance

theorem interpretation_is_closed : MonoidalClosedFunctor interpreted := inferInstance

def comparisonReadout : (Bool ⟶ Bool) ⟶ (Bool ⟶ Bool) :=
  eqToHom (functor_exponential_object meanings realized dataObject dataObject).symm ≫
    (expComparison interpreted dataObject).natTrans.app dataObject

set_option backward.isDefEq.respectTransparency false in
theorem comparisonReadout_identity : comparisonReadout = 𝟙 (Bool ⟶ Bool) := by
  unfold comparisonReadout interpreted
  rw [functor_expComparison]
  simp only [eqToHom_refl]
  exact Category.id_comp _

theorem actual_function_and_both_arguments_retained :
    comparisonReadout negate false = true ∧ comparisonReadout negate true = false := by
  rw [comparisonReadout_identity]
  exact ⟨rfl, rfl⟩

theorem constant_argument_replacement_rejected :
    comparisonReadout negate false ≠ comparisonReadout negate true := by
  rw [actual_function_and_both_arguments_retained.1,
    actual_function_and_both_arguments_retained.2]
  exact Bool.false_ne_true.symm

def retainedEqualizer : Object signature := equalizerObject (declared false) (declared false)

def retainedValue (value : Bool) : interpreted.obj retainedEqualizer :=
  interpreted.map (equalizerLift (declared false) (declared false) (𝟙 dataObject) rfl) value

theorem equalizer_retains_supplied_value (value : Bool) :
    interpreted.map (equalizerInclusion (declared false) (declared false))
      (retainedValue value) = value := by
  have complete := interpreted.map_comp
    (equalizerLift (declared false) (declared false) (𝟙 dataObject) rfl)
    (equalizerInclusion (declared false) (declared false))
  have factored := congrArg interpreted.map
    (equalizerLift_inclusion (declared false) (declared false) (𝟙 dataObject) rfl)
  exact congrArg (fun arrow : Bool ⟶ Bool => arrow value)
    (complete.symm.trans (factored.trans (interpreted.map_id dataObject)))

theorem distinct_equalizer_witnesses : retainedValue false ≠ retainedValue true := by
  intro same
  have supplied := congrArg
    (interpreted.map (equalizerInclusion (declared false) (declared false))) same
  rw [equalizer_retains_supplied_value, equalizer_retains_supplied_value] at supplied
  exact Bool.false_ne_true supplied

theorem identity_negation_equalizer_has_no_value :
    IsEmpty (interpreted.obj (equalizerObject (declared false) (declared true))) := by
  refine ⟨fun value => ?_⟩
  have condition := congrArg interpreted.map
    (equalizer_condition (declared false) (declared true))
  rw [interpreted.map_comp, interpreted.map_comp, actual_identity, actual_negation] at condition
  have impossible := congrArg (fun arrow => arrow value) condition
  change interpreted.map (equalizerInclusion (declared false) (declared true)) value =
    Bool.not (interpreted.map (equalizerInclusion (declared false) (declared true)) value) at impossible
  cases read : interpreted.map (equalizerInclusion (declared false) (declared true)) value <;>
    simp only [read, Bool.not_false, Bool.not_true] at impossible <;> cases impossible

end Mettapedia.GSLT.Core.RelativeClosedInterpretationPreservationControls
