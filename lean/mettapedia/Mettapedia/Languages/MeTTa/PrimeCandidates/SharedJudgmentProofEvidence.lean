import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServices
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceInterpretation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.UniformListChartProofSyntax

/-!
# Submitted proof evidence for the shared HOL service

The retained artifact contains the actual submitted replay request and its
structurally reconstructed HOL proof. Producer faithfulness is an independent
predicate, not a field inferred from intrinsic derivability. Erasure agrees
with the unchanged coarse producer of every replay-qualified assembly.

The theorem-application view keeps the exact ordered assumptions and source
conclusion but forgets the supplied strategy. Restoring that strategy requires
the submitted request as a sidecar, including its certificates and premises.
A finite structural strategy consumer selects one of two supplied proofs by
node cost; it is not a general learning algorithm or a cost model for replay.

The same assembly's actual native payload is its represented proposition,
not a native proof inhabitant. Its attachment to a raw interpretation requires
independent native-environment formation and meaning compatibility. Checking
the supplied premise lists is not revision freshness or dependency minimality.
No external proof-byte checker, revision authority or final kernel is selected.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentProofEvidence

open Mettapedia.Logic HOL HOL.UniformListInduction
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation
open SharedJudgmentFragment SharedJudgmentServices SharedJudgmentServiceInterpretation
open UniformListChartNIKService

universe u v w w'

variable {Γ : HOL.Ctx BaseSort} {assembly : Assembly}

/-- Raw retained evidence. Its proof is intrinsically admitted, but that fact
alone does not say that this request produced this particular tree. -/
structure Evidence (Γ : HOL.Ctx BaseSort) where
  request : ReplayRequest Γ
  tree : ProofSyntax Symbol request.claim.1 request.claim.2

namespace Evidence

def Produced (evidence : Evidence Γ) : Prop :=
  UniformListChartProofSyntax.produce? Γ evidence.request = some evidence.tree

/-- The existing intrinsic admission, retaining the claim but not the tree. -/
def applicationView (evidence : Evidence Γ) : (intrinsicProofSystem Γ).ProofObject :=
  evidence.tree.intrinsicAdmission

theorem accepted {evidence : Evidence Γ} (faithful : evidence.Produced) :
    replayAccepted Γ evidence.request = true := by
  unfold Produced UniformListChartProofSyntax.produce? at faithful
  split at faithful
  · assumption
  · cases faithful

/-- Exact ordered assumptions, both supplied equational-premise lists and
their checked certificates remain bound to this request. -/
theorem dependencies {evidence : Evidence Γ} (faithful : evidence.Produced) :
    evidence.request.claim = mapLengthClaim Γ ∧
      evidence.request.basePremises = HOL.UniformListInductionChart.baseAssumptions Γ ∧
      evidence.request.stepPremises = HOL.UniformListInductionChart.stepAssumptions Γ := by
  have checked := (replayAccepted_iff Γ evidence.request).mp (accepted faithful)
  exact ⟨checked.1, checked.2.1, checked.2.2.1⟩

theorem applicationView_accepted (evidence : Evidence Γ) :
    (intrinsicKernel Γ).decide evidence.request.claim evidence.applicationView = true :=
  (intrinsicKernel Γ).correct _ _ |>.mpr rfl

def nativeRequest (evidence : Evidence Γ) :
    NIKServiceInvocation.Request ((HOLControls.raw Γ).toService (HOLControls.qualified Γ)) :=
  .nativeProof evidence.request.claim evidence.applicationView

theorem nativeRequest_accepted (evidence : Evidence Γ) :
    (NIKServiceInvocation.invoke evidence.nativeRequest).acceptedValue =
      some evidence.request.claim := by
  simp only [nativeRequest, NIKServiceInvocation.invoke,
    NIKServiceInvocation.Response.acceptedValue, applicationView_accepted, ↓reduceIte]
  rfl

end Evidence

def produce? (request : ReplayRequest Γ) : Option (Evidence Γ) :=
  (UniformListChartProofSyntax.produce? Γ request).map fun tree => ⟨request, tree⟩

theorem produced_faithful {request : ReplayRequest Γ} {evidence : Evidence Γ}
    (produced : produce? request = some evidence) :
    evidence.request = request ∧ evidence.Produced := by
  obtain ⟨tree, returned, equal⟩ := Option.map_eq_some_iff.mp produced
  cases equal
  exact ⟨rfl, returned⟩

/-- Replay qualification fixes the coarse output, but does not fix an
intensional proof strategy. Subtype equality here uses intrinsic admission. -/
theorem assembly_production_exact (qualified : HOLReplayQualified assembly)
    (request : ReplayRequest Γ) :
    assembly.produceHOL Γ request =
      (UniformListChartProofSyntax.produce? Γ request).map ProofSyntax.intrinsicAdmission := by
  rw [UniformListChartProofSyntax.produce_erasure]
  cases output : assembly.produceHOL Γ request with
  | none =>
      have rejected : ¬ replayAccepted Γ request = true := by
        intro accepted
        have present := (qualified.1 Γ request).mpr accepted
        rw [output] at present
        cases present
      simp only [UniformListChartNIKService.produce?, dif_neg rejected]
  | some proof =>
      have accepted := (qualified.1 Γ request).mp (by simp only [output, Option.isSome_some])
      have bound := (qualified.2 Γ request proof output).1
      simp only [UniformListChartNIKService.produce?, dif_pos accepted]
      exact congrArg some (Subtype.ext bound)

theorem faithful_production (qualified : HOLReplayQualified assembly)
    {evidence : Evidence Γ} (faithful : evidence.Produced) :
    assembly.produceHOL Γ evidence.request = some evidence.applicationView := by
  rw [assembly_production_exact qualified, faithful]
  rfl

theorem faithful_invocation (qualified : HOLReplayQualified assembly)
    {evidence : Evidence Γ} (faithful : evidence.Produced)
    {n : Nat} (environment : Sub Tower.Head Γ.length n)
    {represented : Tower.Tm Γ.length}
    (representation : FormationSensitiveHOLInterface.represent
      FormationSensitiveHOLUniformList.signature evidence.request.claim.2 = some represented) :
    Invocation assembly (.hol Γ evidence.request environment)
      (.holProof evidence.applicationView represented) :=
  .holSuccess (faithful_production qualified faithful) representation

theorem faithful_response (qualified : HOLReplayQualified assembly)
    {evidence : Evidence Γ} (faithful : evidence.Produced)
    {n : Nat} (environment : Sub Tower.Head Γ.length n)
    {represented : Tower.Tm Γ.length}
    (representation : FormationSensitiveHOLInterface.represent
      FormationSensitiveHOLUniformList.signature evidence.request.claim.2 = some represented) :
    invoke assembly (.hol Γ evidence.request environment) =
      .holProof evidence.applicationView represented :=
  (invoke_iff _ _ _).mpr (faithful_invocation qualified faithful environment representation)

/-! ## Checked reconstruction and actual theorem application -/

/-- The sidecar is indispensable: claim binding alone cannot choose the
original tree. Replay uses this request's actual certificates and premises. -/
def restore? (request : ReplayRequest Γ) (view : (intrinsicProofSystem Γ).ProofObject) :
    Option (ProofSyntax Symbol request.claim.1 request.claim.2) :=
  if (intrinsicKernel Γ).decide request.claim view then
    UniformListChartProofSyntax.produce? Γ request
  else none

theorem restore_roundtrip {evidence : Evidence Γ} (faithful : evidence.Produced) :
    restore? evidence.request evidence.applicationView = some evidence.tree := by
  simp only [restore?, evidence.applicationView_accepted, ↓reduceIte]
  exact faithful

theorem restore_requires_replay {request : ReplayRequest Γ}
    {view : (intrinsicProofSystem Γ).ProofObject} {tree}
    (restored : restore? request view = some tree) :
    replayAccepted Γ request = true ∧ view.1 = request.claim ∧
      UniformListChartProofSyntax.produce? Γ request = some tree := by
  unfold restore? at restored
  split at restored
  · rename_i bound
    exact ⟨Evidence.accepted (evidence := ⟨request, tree⟩) restored,
      (intrinsicKernel Γ).correct _ _ |>.mp bound, restored⟩
  · cases restored

theorem restore_rejected (request : ReplayRequest Γ)
    (view : (intrinsicProofSystem Γ).ProofObject)
    (rejected : replayAccepted Γ request = false) : restore? request view = none := by
  unfold restore?
  split
  · exact UniformListChartProofSyntax.rejected_no_tree Γ request rejected
  · rfl

theorem restore_wrong_claim (request : ReplayRequest Γ)
    (view : (intrinsicProofSystem Γ).ProofObject) (different : view.1 ≠ request.claim) :
    restore? request view = none := by
  have rejected : ¬ (intrinsicKernel Γ).decide request.claim view = true := by
    intro accepted
    exact different ((intrinsicKernel Γ).correct _ _ |>.mp accepted)
  simp only [restore?, Bool.not_eq_true] at rejected ⊢
  rw [rejected]
  rfl

/-- Applying the forgotten theorem uses the actual HOL quantifier rules and
retains its full theory as assumptions. No proof tree is recovered. -/
theorem applyMapLength (view : (intrinsicProofSystem Γ).ProofObject)
    (bound : (intrinsicKernel Γ).decide (mapLengthClaim Γ) view = true)
    (function : Expr Γ mapping) (input : Expr Γ sequence) :
    HOL.ExtDerivation Symbol theory (preservesLength function input) := by
  have claim := (intrinsicKernel Γ).correct _ _ |>.mp bound
  have proof := view.property
  rw [claim] at proof
  have first := HOL.ExtDerivation.allE function proof
  have first' : HOL.ExtDerivation Symbol theory
      (.all (preservesLength (HOL.weaken function) (.var .vz))) := by
    simpa [mapLengthClaim, mapLength, preservesLength, length, map, HOL.instantiate, HOL.subst,
      HOL.Subst.single, HOL.Subst.lift, HOL.weaken, HOL.rename] using first
  simpa only [instantiate_lengthPredicateBody] using (HOL.ExtDerivation.allE input first')

/-- The retained route performs the same application while preserving the
submitted proof tree beneath its two new elimination nodes. -/
def applyRetained (evidence : Evidence Γ) (faithful : evidence.Produced)
    (function : Expr Γ mapping) (input : Expr Γ sequence) :
    ProofSyntax Symbol theory (preservesLength function input) := by
  have claim := (Evidence.dependencies faithful).1
  have proof := evidence.tree
  rw [claim] at proof
  have first := ProofSyntax.allE function proof
  have first' : ProofSyntax Symbol theory
      (.all (preservesLength (HOL.weaken function) (.var .vz))) := by
    simpa [mapLengthClaim, mapLength, preservesLength, length, map, HOL.instantiate, HOL.subst,
      HOL.Subst.single, HOL.Subst.lift, HOL.weaken, HOL.rename] using first
  simpa only [instantiate_lengthPredicateBody] using (ProofSyntax.allE input first')

theorem application_erasure (evidence : Evidence Γ) (faithful : evidence.Produced)
    (function : Expr Γ mapping) (input : Expr Γ sequence) :
    (applyRetained evidence faithful function input).erase =
      applyMapLength evidence.applicationView
        ((intrinsicKernel Γ).correct _ _ |>.mpr (Evidence.dependencies faithful).1)
        function input := Subsingleton.elim _ _

/-! ## A structural strategy consumer, distinct from theorem application -/

/-- This declared consumer compares retained proof-node counts. It makes
no prediction of proof search, certificate checking or runtime costs. -/
def preferLeft (first second : Evidence Γ) : Bool :=
  decide (first.tree.nodeCount ≤ second.tree.nodeCount)

/-- Selection returns an original artifact, including its request. It does
not replace the selected tree by another proof of the same theorem. -/
def prefer (first second : Evidence Γ) : Evidence Γ :=
  if preferLeft first second then first else second

theorem prefer_is_input (first second : Evidence Γ) :
    prefer first second = first ∨ prefer first second = second := by
  unfold prefer
  split <;> simp only [true_or, or_true]

theorem prefer_faithful {first second : Evidence Γ}
    (left : first.Produced) (right : second.Produced) : (prefer first second).Produced := by
  rcases prefer_is_input first second with selected | selected
  · rw [selected]
    exact left
  · rw [selected]
    exact right

theorem prefer_cost_le (first second : Evidence Γ) :
    (prefer first second).tree.nodeCount ≤ first.tree.nodeCount ∧
      (prefer first second).tree.nodeCount ≤ second.tree.nodeCount := by
  by_cases comparison : first.tree.nodeCount ≤ second.tree.nodeCount
  · have selected : prefer first second = first := by simp [prefer, preferLeft, comparison]
    have cost := congrArg (fun evidence : Evidence Γ => evidence.tree.nodeCount) selected
    rw [cost]
    exact ⟨le_rfl, comparison⟩
  · have selected : prefer first second = second := by simp [prefer, preferLeft, comparison]
    have cost := congrArg (fun evidence : Evidence Γ => evidence.tree.nodeCount) selected
    rw [cost]
    exact ⟨Nat.le_of_lt (Nat.lt_of_not_ge comparison), le_rfl⟩

/-! ## Binding the retained producer to the same native interpretation -/

theorem represented_admitted (qualified : HOLReplayQualified assembly)
    {evidence : Evidence Γ} (faithful : evidence.Produced)
    {represented : Tower.Tm Γ.length}
    (representation : FormationSensitiveHOLInterface.represent
      FormationSensitiveHOLUniformList.signature evidence.request.claim.2 = some represented) :
    FormationSensitive.Judgment assembly.rules
      (FormationSensitiveHOLInterface.context FormationSensitiveHOLUniformList.types Γ)
      represented (.const `HOLUniformList.prop) := by
  obtain ⟨conclusion, assumptions, represented, _, formed, _⟩ :=
    (produced_hol_admission qualified (faithful_production qualified faithful)).2.2
  have same := Option.some.inj (represented.symm.trans representation)
  simpa only [same] using formed

variable {C : Cwf.{u, v, w, w'}}
variable {interpretation : SharedJudgmentInterpretation.Data assembly C}

/-- Independent exact syntax binding for the existing attachment. Its
context is the actual target of the separately formed request environment. -/
def ResponseBound (attachment : NativeAttachment (sourceTarget Γ) interpretation)
    (evidence : Evidence Γ)
    (environment : Sub Tower.Head Γ.length (attachment.scope evidence.request.claim)) : Prop :=
  ∃ represented : Tower.Tm Γ.length,
    FormationSensitiveHOLInterface.represent FormationSensitiveHOLUniformList.signature
        evidence.request.claim.2 = some represented ∧
      attachment.payload evidence.request.claim = subst environment represented ∧
      attachment.nativeType evidence.request.claim = .const `HOLUniformList.prop

/-- The actual assembly response and the raw interpretation concern the
same payload/context/type. Native admission is proved from its representation
and formed environment; semantic compatibility remains an explicit law. -/
theorem produced_attached_response (qualified : HOLReplayQualified assembly)
    {evidence : Evidence Γ} (faithful : evidence.Produced)
    (attachment : NativeAttachment (sourceTarget Γ) interpretation)
    (environment : Sub Tower.Head Γ.length (attachment.scope evidence.request.claim))
    (bound : ResponseBound attachment evidence environment)
    (formed : FormationSensitive.ContextFormation assembly.rules
      (attachment.context evidence.request.claim))
    (typed : FormationSensitive.CtxMor assembly.rules
      (FormationSensitiveHOLInterface.context FormationSensitiveHOLUniformList.types Γ)
      (attachment.context evidence.request.claim) environment)
    (meaning : attachment.MeaningCompatible) :
    (invoke assembly (.hol Γ evidence.request environment)).nativePayload? =
        some (attachment.payload evidence.request.claim, attachment.nativeType evidence.request.claim) ∧
      FormationSensitive.Judgment assembly.rules (attachment.context evidence.request.claim)
        (attachment.payload evidence.request.claim) (attachment.nativeType evidence.request.claim) ∧
      interpretation.ty ⟨attachment.context evidence.request.claim, formed⟩
        (attachment.nativeType evidence.request.claim) (attachment.semanticType evidence.request.claim formed) ∧
      interpretation.term ⟨attachment.context evidence.request.claim, formed⟩
        (attachment.payload evidence.request.claim) (attachment.nativeType evidence.request.claim)
        (attachment.semanticType evidence.request.claim formed) (attachment.value evidence.request.claim formed) := by
  obtain ⟨represented, representation, payload, type⟩ := bound
  refine ⟨?_, ?_, meaning evidence.request.claim formed evidence.tree.erase⟩
  · rw [faithful_response qualified faithful environment representation]
    simp only [Response.nativePayload?, payload, type]
  · rw [payload, type]
    simpa only [Presentation.subst] using
      (represented_admitted qualified faithful representation).substitute formed typed

/-- The existing four-face service interface admits the exact erased tree,
and transports its independently qualified attachment without changing its
general source-derivability target. -/
theorem native_attachment_transport (evidence : Evidence Γ)
    (attachment : NativeAttachment (sourceTarget Γ) interpretation)
    (native : attachment.NativeAdmitted) (meaning : attachment.MeaningCompatible) :
    let context := attachment.admittedContext native evidence.request.claim evidence.tree.erase
    FormationSensitive.Judgment assembly.rules (attachment.context evidence.request.claim)
        (attachment.payload evidence.request.claim) (attachment.nativeType evidence.request.claim) ∧
      interpretation.ty context
        (attachment.nativeType evidence.request.claim) (attachment.semanticType evidence.request.claim context.formed) ∧
      interpretation.term context
        (attachment.payload evidence.request.claim) (attachment.nativeType evidence.request.claim)
        (attachment.semanticType evidence.request.claim context.formed)
        (attachment.value evidence.request.claim context.formed) :=
  attachment.accepted_native_and_meaning (HOLControls.raw Γ) (HOLControls.qualified Γ)
    native meaning evidence.nativeRequest .nativeProof evidence.nativeRequest_accepted

/-! ## Submitted strategies and refusal controls -/

namespace Controls

def actual (Γ : HOL.Ctx BaseSort) : Evidence Γ :=
  ⟨actualRequest Γ, UniformListChartProofSyntax.actualProof Γ⟩

def detoured (Γ : HOL.Ctx BaseSort) : Evidence Γ :=
  ⟨UniformListChartProofSyntax.detouredRequest Γ, UniformListChartProofSyntax.detouredProof Γ⟩

theorem actual_faithful (Γ : HOL.Ctx BaseSort) : (actual Γ).Produced :=
  UniformListChartProofSyntax.actual_produced Γ

theorem detoured_faithful (Γ : HOL.Ctx BaseSort) : (detoured Γ).Produced :=
  UniformListChartProofSyntax.detoured_produced Γ

theorem same_application_view (Γ : HOL.Ctx BaseSort) :
    (actual Γ).applicationView = (detoured Γ).applicationView :=
  UniformListChartProofSyntax.same_intrinsic_admission Γ

theorem actual_preferred : preferLeft (actual []) (detoured []) = true := by
  change decide ((UniformListChartProofSyntax.actualProof []).nodeCount ≤
    (UniformListChartProofSyntax.detouredProof []).nodeCount) = true
  rw [UniformListChartProofSyntax.actual_tree_nodes, UniformListChartProofSyntax.detoured_tree_nodes]
  rfl

theorem detoured_not_preferred : preferLeft (detoured []) (actual []) = false := by
  change decide ((UniformListChartProofSyntax.detouredProof []).nodeCount ≤
    (UniformListChartProofSyntax.actualProof []).nodeCount) = false
  rw [UniformListChartProofSyntax.actual_tree_nodes, UniformListChartProofSyntax.detoured_tree_nodes]
  rfl

theorem select_actual : prefer (actual []) (detoured []) = actual [] ∧
    prefer (detoured []) (actual []) = actual [] := by
  simp [prefer, actual_preferred, detoured_not_preferred]

/-- This genuine structural consumer cannot run on coarse theorem admissions
alone, even though that view suffices for ordinary theorem application. -/
theorem no_coarse_strategy_consumer :
    ¬ ∃ decide : (intrinsicProofSystem []).ProofObject →
        (intrinsicProofSystem []).ProofObject → Bool,
      decide (actual []).applicationView (detoured []).applicationView =
          preferLeft (actual []) (detoured []) ∧
        decide (detoured []).applicationView (actual []).applicationView =
          preferLeft (detoured []) (actual []) := by
  rintro ⟨decide, forward, backward⟩
  rw [same_application_view, actual_preferred] at forward
  rw [same_application_view, detoured_not_preferred] at backward
  exact Bool.noConfusion (forward.symm.trans backward)

/-- Keeping another valid proof of the same claim does not make it the
tree produced by the supplied request. -/
def forged (Γ : HOL.Ctx BaseSort) : Evidence Γ :=
  ⟨actualRequest Γ, UniformListChartProofSyntax.detouredProof Γ⟩

theorem forged_not_faithful : ¬ (forged []).Produced := by
  intro faithful
  have different := UniformListChartProofSyntax.retained_strategies_distinct
  apply different
  exact Option.some.inj ((UniformListChartProofSyntax.actual_produced []).symm.trans faithful)

theorem forged_same_admission : (actual []).applicationView = (forged []).applicationView :=
  UniformListChartProofSyntax.same_intrinsic_admission []

theorem restore_actual : restore? (actual []).request (actual []).applicationView =
    some (actual []).tree := restore_roundtrip (actual_faithful [])

theorem restore_detoured : restore? (detoured []).request (detoured []).applicationView =
    some (detoured []).tree := restore_roundtrip (detoured_faithful [])

theorem changed_premises_rejected : restore?
    { actualRequest [] with stepPremises := HOL.UniformListInductionChart.alteredStepAssumptions [] }
    (actual []).applicationView = none := rfl

theorem malformed_rejected : restore?
    { actualRequest [] with stepProof := HOL.UniformListInductionChart.malformedCertificate [] }
    (actual []).applicationView = none := rfl

theorem missing_induction_rejected : restore?
    { actualRequest [] with claim := (equations, mapLength) }
    (actual []).applicationView = none := rfl

def applied : ProofSyntax Symbol (theory (Γ := [element]))
    (preservesLength (.lam (.var .vz)) (cons (.var .vz) nil)) :=
  applyRetained (actual [element]) (actual_faithful [element])
    (.lam (.var .vz)) (cons (.var .vz) nil)

theorem actual_application : HOL.ExtDerivation Symbol (theory (Γ := [element]))
    (preservesLength (.lam (.var .vz)) (cons (.var .vz) nil)) := applied.erase

theorem common_invocation {n : Nat} (environment : Sub Tower.Head 0 n) :
    Invocation common (.hol [] (actual []).request environment)
      (.holProof (actual []).applicationView FormationSensitiveHOLUniformList.rawMapLength) :=
  faithful_invocation common_hol_replay (actual_faithful []) environment
    (FormationSensitiveHOLUniformList.mapLength_represented [])

end Controls

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentProofEvidence
