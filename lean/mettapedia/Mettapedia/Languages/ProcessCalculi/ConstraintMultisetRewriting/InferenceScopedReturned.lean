import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedActivation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidReturned
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceTraceClassifying

/-!
# Actual scoped solver returns supply the original installed inference firing

The checked source ID and ordered arguments activate the original inference
rule. Its scoped values are encoded structurally in the general contextual
calculus. A concrete completed solver return then supplies an ordinary
selected firing with that same source ID, inputs and ordered physical reads.
The already established proof-relevant judgment projection applies directly.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedReturned

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open ContextualFrameUpdate
open InferenceSchemaKernel (Value locatedAction)
open InferenceRequestExecution (Occurrence label payload system)
open ScopedInferenceValues (Ready base encode)
open InferenceSelectedFirings
open InferenceJudgmentBoards

variable {Local Shared : Type}
  (locals : Local → MetaArity base) (captures : Shared → MetaArity base)

def legacyBefore (state : Configuration Ready Occurrence) : Configuration Value Occurrence :=
  OccurrenceRelabeling.configuration Subtype.val state

def legacyAfter (state : Configuration Ready Occurrence) (readyRule : RuleInstance Ready)
    (selection : Selection Occurrence) : Configuration Value Occurrence :=
  selection.result label (readyRule.map Subtype.val) (legacyBefore state)

variable [DecidableEq Local] [DecidableEq Shared]
  [∀ result, DecidableEq (base.Op result)]

def selected (definition : ValidatedCalculusLanguageDef) (id : RuleId) (arguments : List Pattern)
    (readyRule : RuleInstance Ready)
    (activated : InferenceScopedActivation.activate definition id arguments = some readyRule)
    (readyLabel : Occurrence → Ready) (state : Configuration Ready Occurrence)
    (extra : EquationStore (Term (signature base captures) [] ()))
    (fuel : Nat) (occupied : Finset Nat) (selection : Selection Occurrence)
    (update : Update (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals captures occupied selection
        (ContextualRigidActivation.rule locals captures encode readyRule)
        (ContextualRigidActivation.rows locals captures encode readyLabel)
        (ContextualRigidActivation.withFrame captures encode extra state))))
    (returned : ContextualTransportedActivation.FromRun locals captures fuel occupied selection
      (ContextualRigidActivation.rule locals captures encode readyRule)
      (ContextualRigidActivation.rows locals captures encode readyLabel)
      (ContextualRigidActivation.withFrame captures encode extra state)
      (ContextualRigidActivation.outputs locals captures encode readyLabel) update)
    (readback : ∀ occurrence, occurrence ∈ state.present ∨ occurrence ∈ selection.made →
      (readyLabel occurrence).val = label occurrence) :
    SelectedFiring definition true (legacyBefore state) (legacyAfter state readyRule selection) := by
  have free : readyRule.checks = [] := by
    obtain ⟨raw, sourceComputed, exactRule, free⟩ :=
      InferenceScopedActivation.origin definition id arguments activated
    exact free
  have decoded := ContextualRigidActivation.ordinary_valid_of_returned locals captures encode
    ScopedInferenceValues.encode_injective locatedAction Subtype.val free update returned
  have freeLegacy : (readyRule.map Subtype.val).checks = [] := by
    simp only [RuleInstance.map, free, List.map_nil]
  have qualified : selection.Valid locatedAction label (readyRule.map Subtype.val) (legacyBefore state) :=
    OccurrenceRelabeling.valid_label_congr locatedAction (Subtype.val ∘ readyLabel) label
      (readyRule.map Subtype.val) freeLegacy selection (legacyBefore state) decoded
      (fun occurrence member => readback occurrence (Or.inl
        (returned.valid.admitted.occurrences.taken_subset (by simpa [Selection.commit] using member))))
      (fun occurrence member => readback occurrence (Or.inl
        (returned.valid.admitted.occurrences.kept_subset (by simpa [Selection.commit] using member))))
      (fun occurrence member => readback occurrence (Or.inr member))
  refine
    { source := .inl id
      installed := ?_
      inputs := .inl arguments
      rule := readyRule.map Subtype.val
      computed := ?_
      picked := selection
      qualified := qualified
      formed := by intro occurrence made; rfl
      destination := rfl }
  · obtain ⟨raw, sourceComputed, _, _⟩ :=
      InferenceScopedActivation.origin definition id arguments activated
    obtain ⟨sourceRule, _, _, lookup, _, _⟩ :=
      InferenceSchemaActivation.origin definition id arguments sourceComputed
    refine List.mem_map.mpr ⟨sourceRule, List.mem_of_find?_eq_some lookup, ?_⟩
    have identity : sourceRule.id = id := by simpa using List.find?_some lookup
    exact congrArg Sum.inl identity
  · change (InferenceSchemaActivation.activate definition id arguments).map InferenceSchemaKernel.locate = _
    obtain ⟨raw, sourceComputed, exactRule, _⟩ :=
      InferenceScopedActivation.origin definition id arguments activated
    rw [sourceComputed]
    exact congrArg some exactRule.symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedReturned
