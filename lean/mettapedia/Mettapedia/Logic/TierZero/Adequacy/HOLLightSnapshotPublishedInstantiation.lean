import Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotAdmissionCompleteness

/-!
# Every later admitted instance of an actual coupled protected publication

The certificate retains the actual computed source operation, physical read
selection and observed protected output. Its independent source judgment is
extracted once. Later substitution uses only the original local inference
and formation operations, and its finite command actually installs into the
same data-resident catalog. No original run or proof graph is replayed.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotPublishedInstantiation

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open InferenceSchemaActivation (Tm action)
open HOLLightSnapshotData HOLLightSnapshotAdmission HOLLightSnapshotActivation
open HOLLightSnapshotRegistrySemantics HOLLightSnapshotSemantics HOLLightSnapshotPublication
open HOLLightSnapshotAdmissionCompleteness
open HOLLightContextLicensing

universe uO
variable {O : Type uO} [DecidableEq O]

structure Publication (root : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (fallback : TheoryContext) (location : O → Location) (payload : O → Tm) where
  snapshot : Snapshot
  valid : Valid root policy fallback snapshot
  beforeId : Nat
  data : Data
  cache : Array Theorem
  prepared : Prepared
  computed : prepare policy snapshot beforeId data cache = some prepared
  world : Configuration Value O
  picked : Selection O
  qualified : picked.Valid locatedAction (fun occurrence => (location occurrence, payload occurrence))
    (installRule snapshot beforeId data cache prepared) world
  assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0
  solved : locatedAction.Models assignment (picked.problem (fun occurrence => (location occurrence, payload occurrence))
    (installRule snapshot beforeId data cache prepared) world)
  incoming : ∀ sourceContext, context snapshot beforeId = some sourceContext → ∀ occurrence ∈ picked.read,
    location occurrence = judgments → ∀ fact,
      action.apply assignment (payload occurrence) = HOLLightContextActivation.theoremPayload beforeId fact →
        TheoryDerives policy sourceContext fact
  occurrence : O
  made : occurrence ∈ picked.made
  protectedHere : location occurrence = judgments
  contextId : Nat
  fact : Theorem
  observed : action.apply assignment (payload occurrence) = HOLLightContextActivation.theoremPayload contextId fact

namespace Publication

variable {root : TheoryContext} {policy : AxiomPolicy} [DecidablePred policy]
    {fallback : TheoryContext} {location : O → Location} {payload : O → Tm}
    (publication : Publication root policy fallback location payload)

def sourceContext : TheoryContext := publication.prepared.output.context

private theorem checked_output_source : Licensed root policy publication.sourceContext ∧
    (∀ fact ∈ publication.prepared.output.theorems, TheoryDerives policy publication.sourceContext fact) ∧
    context publication.prepared.snapshot publication.prepared.after = some publication.sourceContext := by
  apply physical_installation_extracts_source root policy publication.snapshot publication.beforeId publication.data publication.cache
    publication.computed location payload publication.qualified publication.assignment publication.solved
  · intro sourceContext known
    obtain ⟨_, _, _, _, _, _, _, available, _, _, _, _⟩ :=
      prepare_origin policy publication.snapshot publication.beforeId publication.data publication.cache publication.computed
    exact licensed_context root policy fallback publication.snapshot publication.valid.registry publication.beforeId sourceContext known available
  · exact publication.incoming

theorem justified : TheoryDerives policy publication.sourceContext publication.fact := by
  have member := (actual_judgment_output_is_exact location payload publication.snapshot publication.beforeId publication.data publication.cache
    publication.prepared publication.qualified publication.assignment publication.occurrence publication.made publication.protectedHere
    publication.contextId publication.fact publication.observed).2
  exact publication.checked_output_source.2.1 publication.fact member

theorem licensed : Licensed root policy publication.sourceContext := publication.checked_output_source.1

theorem context_exact : context publication.prepared.snapshot publication.contextId = some publication.sourceContext := by
  have same := (actual_judgment_output_is_exact location payload publication.snapshot publication.beforeId publication.data publication.cache
    publication.prepared publication.qualified publication.assignment publication.occurrence publication.made publication.protectedHere
    publication.contextId publication.fact publication.observed).1
  exact same ▸ publication.checked_output_source.2.2

theorem context_available : (publication.prepared.snapshot.store.lookup (.inl publication.contextId)).isSome = true := by
  have same := (actual_judgment_output_is_exact location payload publication.snapshot publication.beforeId publication.data publication.cache
    publication.prepared publication.qualified publication.assignment publication.occurrence publication.made publication.protectedHere
    publication.contextId publication.fact publication.observed).1
  exact same ▸ prepared_after_available policy publication.snapshot publication.beforeId publication.data publication.cache publication.computed

theorem every_type_instance (maplets : List (Ty × Ty)) (out : Theorem)
    (checked : (InferenceRequest.instType maplets publication.fact).check = some out)
    (argumentsFormed : InferenceFormation.Formed publication.sourceContext.signature (.instType maplets publication.fact))
    (outputFormed : TheoremFormed publication.sourceContext.signature out) :
    TheoryDerives policy publication.sourceContext out := by
  refine .inference ((InferenceRequest.check_eq_some_iff _ _).mp checked) argumentsFormed ?_ outputFormed
  intro premise member
  have same : premise = publication.fact := by simpa [InferenceRequest.premises] using member
  exact same ▸ publication.justified

theorem every_term_instance (maplets : List SourceSubstitution.TermMaplet) (out : Theorem)
    (checked : (InferenceRequest.inst maplets publication.fact).check = some out)
    (argumentsFormed : InferenceFormation.Formed publication.sourceContext.signature (.inst maplets publication.fact))
    (outputFormed : TheoremFormed publication.sourceContext.signature out) :
    TheoryDerives policy publication.sourceContext out := by
  refine .inference ((InferenceRequest.check_eq_some_iff _ _).mp checked) argumentsFormed ?_ outputFormed
  intro premise member
  have same : premise = publication.fact := by simpa [InferenceRequest.premises] using member
  exact same ▸ publication.justified

theorem type_instance_preserves_axioms (maplets : List (Ty × Ty)) (out : Theorem)
    (checked : (InferenceRequest.instType maplets publication.fact).check = some out) : out.axioms = publication.fact.axioms :=
  ((InferenceRequest.check_eq_some_iff _ _).mp checked).1

theorem term_instance_preserves_axioms (maplets : List SourceSubstitution.TermMaplet) (out : Theorem)
    (checked : (InferenceRequest.inst maplets publication.fact).check = some out) : out.axioms = publication.fact.axioms := by
  obtain ⟨_, _, source⟩ := (InferenceRequest.check_eq_some_iff _ _).mp checked
  exact source.1

theorem type_instance_hypotheses_empty_iff (maplets : List (Ty × Ty)) (out : Theorem)
    (checked : (InferenceRequest.instType maplets publication.fact).check = some out) :
    out.sequent.hyp = ∅ ↔ publication.fact.sequent.hyp = ∅ := by
  have source := (InferenceRequest.check_eq_some_iff _ _).mp checked
  have same := source.2.1.unique (applyHypotheses_semantics _ _)
  rw [same]
  simp [TypeCorrectTermSubstitution.applyHypotheses]

theorem term_instance_hypotheses_empty_iff (maplets : List SourceSubstitution.TermMaplet) (out : Theorem)
    (checked : (InferenceRequest.inst maplets publication.fact).check = some out) :
    out.sequent.hyp = ∅ ↔ publication.fact.sequent.hyp = ∅ := by
  obtain ⟨_, _, source⟩ := (InferenceRequest.check_eq_some_iff _ _).mp checked
  have same := source.2.1.unique (applyHypotheses_semantics _ _)
  rw [same]
  simp [TypeCorrectTermSubstitution.applyHypotheses]

/-- The original one-premise inference is encoded and admitted into the
actual successor snapshot catalog, retaining its exact parent address. -/
theorem one_premise_inference_installs (request : InferenceRequest) (out : Theorem) (origin : Origin)
    (premises : request.premises = [publication.fact]) (checked : request.check = some out)
    (argumentsFormed : InferenceFormation.Formed publication.sourceContext.signature request)
    (outputFormed : TheoremFormed publication.sourceContext.signature out) :
    ∃ (data : Data) (next : Prepared),
      prepare policy publication.prepared.snapshot publication.contextId data #[publication.fact] = some next ∧
      next.output.context = publication.sourceContext ∧ next.output.theorems = [out] ∧ next.command.parents = [0] := by
  let node : Receipt := ⟨out, .inference request, [0], origin⟩
  have found : Mettapedia.Logic.DerivationGraph.lookupPremises #[publication.fact] node.parents = some node.witness.premises := by
    change some [publication.fact] = some request.premises
    rw [premises]
  have step : node.witness.Semantics policy node.conclusion := (InferenceRequest.check_eq_some_iff request out).mp checked
  obtain ⟨certificates, admitted⟩ := Command.check_proof_complete policy publication.sourceContext #[publication.fact] node found step
    (by intro actual same; cases RuleRequest.inference.inj same; exact argumentsFormed) outputFormed
  obtain ⟨next, computed, outputSame, _, parentsSame⟩ := every_checked_command_installs policy publication.prepared.snapshot
    publication.contextId publication.sourceContext publication.context_exact publication.context_available #[publication.fact]
      (.proof node certificates) ⟨publication.sourceContext, [out]⟩ admitted
  refine ⟨_, next, computed, ?_, ?_, parentsSame⟩
  · rw [outputSame]
  · rw [outputSame]

theorem every_type_instance_installs (maplets : List (Ty × Ty)) (out : Theorem) (origin : Origin)
    (checked : (InferenceRequest.instType maplets publication.fact).check = some out)
    (argumentsFormed : InferenceFormation.Formed publication.sourceContext.signature (.instType maplets publication.fact))
    (outputFormed : TheoremFormed publication.sourceContext.signature out) :
    ∃ (data : Data) (next : Prepared),
      prepare policy publication.prepared.snapshot publication.contextId data #[publication.fact] = some next ∧
      next.output.context = publication.sourceContext ∧ next.output.theorems = [out] ∧ next.command.parents = [0] :=
  publication.one_premise_inference_installs (.instType maplets publication.fact) out origin rfl checked argumentsFormed outputFormed

theorem every_term_instance_installs (maplets : List SourceSubstitution.TermMaplet) (out : Theorem) (origin : Origin)
    (checked : (InferenceRequest.inst maplets publication.fact).check = some out)
    (argumentsFormed : InferenceFormation.Formed publication.sourceContext.signature (.inst maplets publication.fact))
    (outputFormed : TheoremFormed publication.sourceContext.signature out) :
    ∃ (data : Data) (next : Prepared),
      prepare policy publication.prepared.snapshot publication.contextId data #[publication.fact] = some next ∧
      next.output.context = publication.sourceContext ∧ next.output.theorems = [out] ∧ next.command.parents = [0] :=
  publication.one_premise_inference_installs (.inst maplets publication.fact) out origin rfl checked argumentsFormed outputFormed

theorem every_type_instance_activates (maplets : List (Ty × Ty)) (out : Theorem) (origin : Origin)
    (checked : (InferenceRequest.instType maplets publication.fact).check = some out)
    (argumentsFormed : InferenceFormation.Formed publication.sourceContext.signature (.instType maplets publication.fact))
    (outputFormed : TheoremFormed publication.sourceContext.signature out) :
    ∃ (data : Data) (next : Prepared),
      installActivate policy publication.prepared.snapshot publication.contextId data #[publication.fact] =
        some (installRule publication.prepared.snapshot publication.contextId data #[publication.fact] next) ∧
      next.output.context = publication.sourceContext ∧ next.output.theorems = [out] ∧ next.command.parents = [0] := by
  obtain ⟨data, next, computed, contextSame, outputSame, parentsSame⟩ :=
    publication.every_type_instance_installs maplets out origin checked argumentsFormed outputFormed
  exact ⟨data, next, by rw [installActivate, computed]; rfl, contextSame, outputSame, parentsSame⟩

theorem every_term_instance_activates (maplets : List SourceSubstitution.TermMaplet) (out : Theorem) (origin : Origin)
    (checked : (InferenceRequest.inst maplets publication.fact).check = some out)
    (argumentsFormed : InferenceFormation.Formed publication.sourceContext.signature (.inst maplets publication.fact))
    (outputFormed : TheoremFormed publication.sourceContext.signature out) :
    ∃ (data : Data) (next : Prepared),
      installActivate policy publication.prepared.snapshot publication.contextId data #[publication.fact] =
        some (installRule publication.prepared.snapshot publication.contextId data #[publication.fact] next) ∧
      next.output.context = publication.sourceContext ∧ next.output.theorems = [out] ∧ next.command.parents = [0] := by
  obtain ⟨data, next, computed, contextSame, outputSame, parentsSame⟩ :=
    publication.every_term_instance_installs maplets out origin checked argumentsFormed outputFormed
  exact ⟨data, next, by rw [installActivate, computed]; rfl, contextSame, outputSame, parentsSame⟩

theorem forged_term_instance_refused (maplets : List SourceSubstitution.TermMaplet) (out : Theorem)
    (different : out.axioms ≠ publication.fact.axioms) : (InferenceRequest.inst maplets publication.fact).check ≠ some out :=
  fun checked => different (publication.term_instance_preserves_axioms maplets out checked)

theorem hypothesis_erasing_type_instance_refused (maplets : List (Ty × Ty)) (out : Theorem)
    (used : publication.fact.sequent.hyp ≠ ∅) (erased : out.sequent.hyp = ∅) :
    (InferenceRequest.instType maplets publication.fact).check ≠ some out :=
  fun checked => used ((publication.type_instance_hypotheses_empty_iff maplets out checked).mp erased)

end Publication
end Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotPublishedInstantiation
