import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLAdmissionModel
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLPreparationEncodingControls

/-! # Loaded-event controls in constructed models

The existing evaluator's equal-endpoint alternatives remain distinct under
the loaded event predicate. A refusing profile has no event but retains the
same preparation. A separate empty candidate fibre produces no events.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLAdmissionModelControls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Step.Evaluation.Controls
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Controls (Store frame)
open HOLPreparationEncoding HOLPreparedEffectEncoding
open HOLAdmissionCoding HOLAdmissionEventSpecialization

abbrev FrameCode (model : HOL.HenkinModel.{0,0,1} AtomicTy Symbol) :=
  HOLFrameCoding.Coding model Unit (fun _ => Bool) (fun _ _ => Bool → Bool)

theorem constructed_controls (other : TypeFamilySemantics.OperatorFamilies.{0})
    (prior : TypeFamilySemantics.Assignment.{0}) :
    ∃ (actual : HOL.HenkinModel.{0,0,1} AtomicTy Symbol) (frames : FrameCode actual)
      (occurrences : HOLOccurrenceCoding.Coding actual Nat)
      (events : Coding actual Store (fun _ => Bool) (Witness alternatives.effectCore)),
      HOLAdmissionModel.Agreement alternatives.effectCore actual frames occurrences events ∧
      ∃ first second : HOLAdmissionEventSpecialization.EventPacket actual events (next alternatives.effectCore)
        (permits alternatives.effectCore alternatives.eventAdmission) [] [(true,false)],
        first ≠ second ∧
        (∀ target, ¬Nonempty (HOLAdmissionEventSpecialization.EventPacket actual events (next alternatives.effectCore)
          (permits alternatives.effectCore (fun _ _ => False)) [] target)) ∧
        ∃ p t, (actual.constDen HOLLoadedPreparedEvent.symbol (preparationValue actual events)
          (resultValue actual events (next alternatives.effectCore)) (events.states.symm (some []))
          (events.firings.symm (encodeFiring Store (fun _ => Bool) (s := []) true)) p t).down := by
  obtain ⟨actual,frames,occurrences,events,agreement⟩ :=
    HOLAdmissionModel.constructed_agreement alternatives.effectCore other prior
  obtain ⟨equivalence⟩ := agreement.admission alternatives.eventAdmission [] [(true,false)]
  refine ⟨actual,frames,occurrences,events,agreement,
    equivalence (HOLPreparationEncodingControls.branchEvent true),
    equivalence (HOLPreparationEncodingControls.branchEvent false), ?_, ?_, ?_⟩
  · intro same
    have original := equivalence.injective same
    exact Bool.noConfusion (congrArg (fun event => event.firing) original)
  · intro target
    obtain ⟨refused⟩ := agreement.admission (fun _ _ => False) [] target
    rintro ⟨packet⟩
    exact (refused.symm packet).permitted
  · exact (agreement.preparation [] true).mpr initially_permitted.1

def noCandidates : Step frame Nat Store (fun _ => Empty) := program.reindex (fun impossible => nomatch impossible)

theorem empty_candidate_model (other : TypeFamilySemantics.OperatorFamilies.{0})
    (prior : TypeFamilySemantics.Assignment.{0}) :
    ∃ (actual : HOL.HenkinModel.{0,0,1} AtomicTy Symbol) (frames : FrameCode actual)
      (occurrences : HOLOccurrenceCoding.Coding actual Nat)
      (events : Coding actual Store (fun _ => Empty) (Witness noCandidates.effectCore)),
      HOLAdmissionModel.Agreement noCandidates.effectCore actual frames occurrences events ∧
      ∀ target, ¬Nonempty (HOLAdmissionEventSpecialization.EventPacket actual events (next noCandidates.effectCore)
        (permits noCandidates.effectCore noCandidates.eventAdmission) [] target) := by
  obtain ⟨actual,frames,occurrences,events,agreement⟩ :=
    HOLAdmissionModel.constructed_agreement noCandidates.effectCore other prior
  refine ⟨actual,frames,occurrences,events,agreement,?_⟩
  intro target
  obtain ⟨equivalence⟩ := agreement.admission noCandidates.eventAdmission [] target
  rintro ⟨packet⟩
  exact Empty.elim (equivalence.symm packet).firing

#print axioms constructed_controls
#print axioms empty_candidate_model

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLAdmissionModelControls
