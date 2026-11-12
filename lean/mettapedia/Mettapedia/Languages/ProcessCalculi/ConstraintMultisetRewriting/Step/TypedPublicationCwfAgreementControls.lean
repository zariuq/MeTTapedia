import Mettapedia.TypeTheory.ContextualPredicateFamilies
import Mettapedia.TypeTheory.ContextualTypedPublication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeUniverseFrames
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.ExactTransitions

/-!
# A generic CwF does not make all type observations descend

In the predicate-family CwF, including its chosen terminal context, all existing judged values have identical
readings at false and true. The requested predicate b = true distinguishes
those readings. Both are principal answers of the empty equation store in
the values-only frame, and satisfy the library's initial-solution notion
up to that agreement. Thus the CwF laws alone do not license reducing this
type-sensitive check to a principal representative.

The syntactic publication proof uses universe-coded types, and the actual
set-family model separates substitutions by a context-valued term. Neither
qualification follows from the bare CwF interface.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.CwfAgreementControls

open Mettapedia.TypeTheory
open ContextualTypedPublication

abbrev model := ContextualPredicateFamilies.modelWithTerminal.{0}.toCwf
abbrev frame := NativeUniverse.cwfFrames model

def falseReading : model.Sub Unit Bool := fun _ => false
def trueReading : model.Sub Unit Bool := fun _ => true

theorem all_readings_agree {source target : Type} (first second : model.Sub source target) :
    UnificationWithLevels.Agree frame first second := by
  rintro ⟨predicate, term⟩
  exact ContextualPredicateFamilies.judged_readings_agree predicate term first second

def requested : View model Bool :=
  ⟨(fun _ => True), (fun _ => ⟨True.intro⟩), (fun point => point = true)⟩

theorem true_reading_is_licensed : requested.At trueReading := by
  funext point
  exact propext ⟨fun _ => rfl, fun _ => True.intro⟩

theorem false_reading_is_not_licensed : ¬ requested.At falseReading := by
  intro licensed
  have same : True = (false = true) := congrFun licensed ()
  have impossible := Eq.mp same True.intro
  cases impossible

theorem constant_is_principal (value : Bool) :
    frame.Principal ([] : EquationStore (NativeUniverse.Judged model Bool)) (fun _ : Unit => value) := by
  refine ⟨Frames.models_nil _, ?_⟩
  intro observer substitution _
  exact ⟨(fun _ => ()), all_readings_agree substitution _⟩

theorem constant_is_initial (value : Bool) :
    UnificationWithLevels.InitialSolution frame
      ([] : EquationStore (NativeUniverse.Judged model Bool)) (fun _ : Unit => value) :=
  UnificationWithLevels.Principal.initial (constant_is_principal value)
    (fun {_} first second _ => all_readings_agree first second)

theorem principal_type_observation_depends_on_representative :
    frame.Principal ([] : EquationStore (NativeUniverse.Judged model Bool)) falseReading ∧
    frame.Principal ([] : EquationStore (NativeUniverse.Judged model Bool)) trueReading ∧
    UnificationWithLevels.Agree frame falseReading trueReading ∧
    requested.At trueReading ∧ ¬ requested.At falseReading :=
  ⟨constant_is_principal false, constant_is_principal true, all_readings_agree _ _,
    true_reading_is_licensed, false_reading_is_not_licensed⟩

theorem initiality_does_not_supply_missing_type_observations :
    UnificationWithLevels.InitialSolution frame
      ([] : EquationStore (NativeUniverse.Judged model Bool)) falseReading ∧
    UnificationWithLevels.InitialSolution frame
      ([] : EquationStore (NativeUniverse.Judged model Bool)) trueReading ∧
    requested.At trueReading ∧ ¬ requested.At falseReading :=
  ⟨constant_is_initial false, constant_is_initial true,
    true_reading_is_licensed, false_reading_is_not_licensed⟩

/-- The missing information is visible through the actual comprehension
fibre: a licensed reading has a lift into the requested predicate. -/
theorem requested_license_iff_comprehension_lift {observer : Type}
    (reading : model.Sub observer Bool) :
    requested.At reading ↔
      ∃ lift : model.Sub observer (model.ext Bool requested.requested),
        model.compS (model.wk requested.requested) lift = reading := by
  constructor
  · intro licensed
    refine ⟨(fun point => ⟨reading point, Eq.mp (congrFun licensed point) True.intro⟩), rfl⟩
  · rintro ⟨lift, overBase⟩
    funext point
    have atPoint := congrFun overBase point
    have holds := (lift point).property
    change (lift point).val = reading point at atPoint
    change (lift point).val = true at holds
    exact propext ⟨fun _ => atPoint.symm.trans holds, fun _ => True.intro⟩

theorem comprehension_lifting_distinguishes_the_readings :
    (∃ lift : model.Sub Unit (model.ext Bool requested.requested),
      model.compS (model.wk requested.requested) lift = trueReading) ∧
    ¬ (∃ lift : model.Sub Unit (model.ext Bool requested.requested),
      model.compS (model.wk requested.requested) lift = falseReading) :=
  ⟨(requested_license_iff_comprehension_lift trueReading).mp true_reading_is_licensed,
    fun lift => false_reading_is_not_licensed
      ((requested_license_iff_comprehension_lift falseReading).mpr lift)⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.CwfAgreementControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.CwfAgreementControls.principal_type_observation_depends_on_representative
