import Mettapedia.OSLF.Syntax.RhoCommunicationSchema

/-!
# Rule multiplicity in the Chapter 7 rho graph

A proposition-valued reduction relation remembers that an edge exists.  A
presented operational graph can additionally distinguish two authored rule
occurrences with the same source and target.  Duplicating COMM leaves the
extensional relation unchanged but gives distinct retained event witnesses.
This is the information boundary for a subobject-valued classifying account.
-/

namespace Mettapedia.OSLF.Binding.RhoSchema

set_option autoImplicit false

/-- Two occurrences of the same unconditional communication rule. -/
def duplicatedCommunication : UnpositionedPresentation sig :=
  { rho.toUnpositioned with
    rules := [comm.unpositioned, comm.unpositioned] }

/-- Duplicating a rule does not add a new endpoint pair. -/
theorem duplicatedCommunication_steps_iff
    {s : Srt} {source target : Term sig [] s} :
    duplicatedCommunication.StepModE source target ↔
      rho.toUnpositioned.StepModE source target := by
  constructor
  · rintro ⟨index, firing⟩
    fin_cases index
    · exact ⟨⟨0, by decide⟩, firing⟩
    · exact ⟨⟨0, by decide⟩, firing⟩
  · rintro ⟨index, firing⟩
    fin_cases index
    exact ⟨⟨0, by decide⟩, firing⟩

/-- The first copy of the source-order communication event. -/
def firstCommunicationEvent :
    (duplicatedCommunication.stepEvidenceAt Srt.pr).Evidence
      (parT commInput commOutput) commTarget :=
  ⟨⟨0, by decide⟩, rhoCommunicationEvidence.2⟩

/-- The second copy has the same endpoints and firing data. -/
def secondCommunicationEvent :
    (duplicatedCommunication.stepEvidenceAt Srt.pr).Evidence
      (parT commInput commOutput) commTarget :=
  ⟨⟨1, by decide⟩, rhoCommunicationEvidence.2⟩

/-- The authored rule index keeps the two events apart. -/
theorem communication_events_distinct :
    firstCommunicationEvent ≠ secondCommunicationEvent := by
  intro equality
  have indexEquality := congrArg Sigma.fst equality
  have impossible : (0 : Fin 2) = 1 := indexEquality
  cases impossible

/-- Both retained events erase to the same extensional edge. -/
theorem firstCommunicationEvent_erases :
    (duplicatedCommunication.toExtensionalGSLTAt Srt.pr).Step
      (parT commInput commOutput) commTarget :=
  (duplicatedCommunication.stepEvidenceAt Srt.pr).erase firstCommunicationEvent

theorem secondCommunicationEvent_erases :
    (duplicatedCommunication.toExtensionalGSLTAt Srt.pr).Step
      (parT commInput commOutput) commTarget :=
  (duplicatedCommunication.stepEvidenceAt Srt.pr).erase secondCommunicationEvent

end Mettapedia.OSLF.Binding.RhoSchema
