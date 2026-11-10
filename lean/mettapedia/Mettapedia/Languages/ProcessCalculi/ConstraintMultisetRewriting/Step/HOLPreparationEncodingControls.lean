import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLPreparedEffectEncoding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventEvaluationControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProfileControls

/-! # Empty preparations, retained choices and refused event packets

The controls use the existing store-changing evaluator alternatives. Their
equal endpoints do not collapse their event packets. A restricted admission
profile has no packet even though its preparation remains available.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLPreparationEncodingControls

open HOLPreparationEncoding HOLPreparedEffectEncoding
open Step.Evaluation.Controls
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Controls (Store)

theorem empty_fibre :
    Nonempty (RawWitnesses Bool (fun _ => Unit) (fun _ _ => Empty)) ∧
    ¬∃ raw, prepares Bool (fun _ => Unit) (fun _ _ => Empty) (some false)
      (encodeFiring Bool (fun _ => Unit) (s := false) ()) raw := by
  refine ⟨⟨none⟩, ?_⟩
  intro existsRaw
  obtain ⟨impossible⟩ := (witness_exists_iff Bool (fun _ => Unit) (fun _ _ => Empty) (s := false) ()).mp existsRaw
  exact Empty.elim impossible

theorem preparation_choices_distinct :
    encodeWitness Bool (fun _ => Unit) (fun _ _ => Bool) (s := false) () false ≠
      encodeWitness Bool (fun _ => Unit) (fun _ _ => Bool) (s := false) () true := by
  intro same
  exact Bool.noConfusion (encodeWitness_injective Bool (fun _ => Unit) (fun _ _ => Bool) (s := false) () same)

def branchEvent (label : Bool) :
    alternatives.effectCore.Event alternatives.eventAdmission ([] : Store) [(true,false)] :=
  alternatives.event label initially_permitted

theorem same_endpoints_distinct_packets :
    toPacket alternatives.effectCore (branchEvent true) ≠ toPacket alternatives.effectCore (branchEvent false) := by
  intro same
  have events := (eventEquiv alternatives.effectCore alternatives.eventAdmission [] [(true,false)]).injective same
  have labels := congrArg (fun event => event.firing) events
  exact Bool.noConfusion labels

theorem refused_has_no_packet (target : EquationStore (AdmissionObservationCover.Controls.World → Bool)) :
    ¬Nonempty (EventPacket ProfileControls.denied.effectCore ProfileControls.denied.eventAdmission
      EffectStoreControls.duplicated target) := by
  rintro ⟨packet⟩
  exact (ofPacket ProfileControls.denied.effectCore packet).permitted.2

theorem refused_still_has_preparation :
    ∃ raw, prepares _ _ (Witness ProfileControls.denied.effectCore) (some EffectStoreControls.duplicated)
      (encodeFiring _ _ (s := EffectStoreControls.duplicated) ()) raw :=
  (preparation_exists_iff ProfileControls.denied.effectCore ()).mpr ProfileControls.refused_but_prepared.1

#print axioms empty_fibre
#print axioms same_endpoints_distinct_packets
#print axioms refused_has_no_packet

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLPreparationEncodingControls
