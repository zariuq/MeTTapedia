import Mettapedia.Logic.TierZero.Adequacy.HOLLightContextInstallation

/-!
# Every source-admitted instance of an actually published HOL theorem

The publication certificate contains an actual protected authority-system
run and its observed exact theorem, not an assumed source derivation. That
run is used once to obtain independent source justification. Every later
term/type instance uses the original local HOL inference operation and its
exact context-formation checks; it does not replay the original run or its
proof graph. Hypotheses and axiom dependencies are retained by those source
operations, including for conclusions with no free term variables.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightPublishedInstantiation

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open InferenceSchemaActivation (Tm action)
open InferenceSchemaKernel (Space Value locatedAction)
open HOLLightContextActivation
open HOLLightContextPublication

universe uC uX uI uO
variable {C : Type uC} {X : Type uX} {I : Type uI} {O : Type uO}
    [DecidableEq O] {policy : AxiomPolicy} [DecidablePred policy]
    {contexts : Nat → TheoryContext} {entries : Nat → Option (Entry contexts)} {location : O → Space}

structure Publication (system : System policy contexts entries C X I O location) (payload : O → Tm) where
  before : Configuration Value O
  after : Configuration Value O
  actors : List I
  run : system.Run payload before actors after
  prior : ProtectedValid policy contexts location payload before
  assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0
  solved : locatedAction.Models assignment after.equations
  occurrence : O
  present : occurrence ∈ after.present
  protectedHere : location occurrence = .judgments
  context : Nat
  fact : Theorem
  observed : action.apply assignment (payload occurrence) = theoremPayload context fact

namespace Publication

variable {system : System policy contexts entries C X I O location} {payload : O → Tm}
    (publication : Publication system payload)

theorem justified : TheoryDerives policy (contexts publication.context) publication.fact :=
  system.published_theorem_has_source_derivation payload publication.run publication.prior
    publication.assignment publication.solved publication.occurrence publication.present
    publication.protectedHere publication.context publication.fact publication.observed

/-- Universally quantified over the actual source type-substitution inputs,
under their original formation and local checking conditions. -/
theorem every_type_instance (maplets : List (Ty × Ty)) (out : Theorem)
    (checked : (InferenceRequest.instType maplets publication.fact).check = some out)
    (argumentsFormed : InferenceFormation.Formed (contexts publication.context).signature
      (.instType maplets publication.fact))
    (outputFormed : TheoremFormed (contexts publication.context).signature out) :
    TheoryDerives policy (contexts publication.context) out := by
  refine .inference ((InferenceRequest.check_eq_some_iff _ _).mp checked) argumentsFormed ?_ outputFormed
  intro premise member
  have same : premise = publication.fact := by simpa [InferenceRequest.premises] using member
  exact same ▸ publication.justified

/-- Every locally admitted source term substitution is licensed from the
same actual publication, with no replay premise for the original run. -/
theorem every_term_instance (maplets : List SourceSubstitution.TermMaplet) (out : Theorem)
    (checked : (InferenceRequest.inst maplets publication.fact).check = some out)
    (argumentsFormed : InferenceFormation.Formed (contexts publication.context).signature
      (.inst maplets publication.fact))
    (outputFormed : TheoremFormed (contexts publication.context).signature out) :
    TheoryDerives policy (contexts publication.context) out := by
  refine .inference ((InferenceRequest.check_eq_some_iff _ _).mp checked) argumentsFormed ?_ outputFormed
  intro premise member
  have same : premise = publication.fact := by simpa [InferenceRequest.premises] using member
  exact same ▸ publication.justified

theorem type_instance_preserves_axioms (maplets : List (Ty × Ty)) (out : Theorem)
    (checked : (InferenceRequest.instType maplets publication.fact).check = some out) :
    out.axioms = publication.fact.axioms :=
  ((InferenceRequest.check_eq_some_iff _ _).mp checked).1

theorem term_instance_preserves_axioms (maplets : List SourceSubstitution.TermMaplet) (out : Theorem)
    (checked : (InferenceRequest.inst maplets publication.fact).check = some out) :
    out.axioms = publication.fact.axioms := by
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

/-- A purported source instance cannot introduce a new axiom dependency. -/
theorem forged_term_instance_refused (maplets : List SourceSubstitution.TermMaplet) (out : Theorem)
    (different : out.axioms ≠ publication.fact.axioms) :
    (InferenceRequest.inst maplets publication.fact).check ≠ some out :=
  fun checked => different (publication.term_instance_preserves_axioms maplets out checked)

/-- Even a closed conclusion cannot erase a genuinely retained hypothesis
by source substitution. -/
theorem hypothesis_erasing_type_instance_refused (maplets : List (Ty × Ty)) (out : Theorem)
    (used : publication.fact.sequent.hyp ≠ ∅) (erased : out.sequent.hyp = ∅) :
    (InferenceRequest.instType maplets publication.fact).check ≠ some out :=
  fun checked => used ((publication.type_instance_hypotheses_empty_iff maplets out checked).mp erased)

end Publication

/-- All original inference requests keep the same immutable context. -/
def inferenceEntry (contexts : Nat → TheoryContext) (context : Nat) (node : Receipt)
    (witnesses : SignatureFormation.InstanceWitnesses) : Entry contexts :=
  ⟨context, context, .proof node witnesses, rfl⟩

/-- Any source-admitted inference with its actual ordered input addresses has
a computed entry activation. The existing catalog-installation theorem then
installs that entry without granting client publication or new axiom rights. -/
theorem inference_has_activation (policy : AxiomPolicy) [DecidablePred policy]
    (contexts : Nat → TheoryContext) (context source : Nat) (node : Receipt) (cache : Array Theorem)
    (found : Mettapedia.Logic.DerivationGraph.lookupPremises cache node.parents = some node.witness.premises)
    (step : node.witness.Semantics policy node.conclusion)
    (argumentsFormed : ∀ request, node.witness = .inference request →
      InferenceFormation.Formed (contexts context).signature request)
    (outputFormed : TheoremFormed (contexts context).signature node.conclusion) :
    ∃ witnesses : SignatureFormation.InstanceWitnesses,
      let entry := inferenceEntry contexts context node witnesses
      activate policy contexts (fun id => if id = source then some entry else none) source cache =
        some (fromResult source entry cache node.witness.premises ⟨contexts context, [node.conclusion]⟩) := by
  obtain ⟨witnesses, checked⟩ := Command.check_proof_complete policy (contexts context) cache node found step argumentsFormed outputFormed
  refine ⟨witnesses, ?_⟩
  let entry := inferenceEntry contexts context node witnesses
  change activate policy contexts (fun id => if id = source then some entry else none) source cache = _
  unfold activate
  rw [show (fun id : Nat => if id = source then some entry else none) source = some entry by simp]
  dsimp only [Bind.bind, Option.bind]
  rw [show entry.command.check policy (contexts entry.before) cache =
    some (⟨contexts context, [node.conclusion]⟩ : Output) from checked,
    show Mettapedia.Logic.DerivationGraph.lookupPremises cache entry.command.parents = some node.witness.premises from found]
  rfl

end Mettapedia.Logic.TierZero.Adequacy.HOLLightPublishedInstantiation
