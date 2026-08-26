import Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus
import Mettapedia.Languages.MeTTa.Prime.PolicyKeyNIKAdmission

/-!
# Integrated NIK execution capabilities without axis collapse

Prime implementations need three independent judgments:

1. a semantic execution realization is admitted;
2. a receipt key supports the observations requested from that realization;
3. an optional cost comparison establishes profitability.

They share one dependency revision but not one order.  This module places the
last two as displays over an existing `AdmittedExecutionModel`.  Current hot
execution uses only the already-admitted semantic cell and retained keyed
policy.  Profitability is available to selection policy but is absent from the
runner and from semantic preservation.

The exact-candidate law of the maximal-native calculus supplies a further
boundary: candidates with the same requested semantic capabilities cannot be
silently separated by an external profitability preference.  Profitability
therefore does not masquerade as calculus strength; it acts only after the
exact semantic capability fibre has been exposed.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NIKIntegratedExecutionCapabilities

open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.NIKIndexedExecutionAdmission
open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus
open Mettapedia.Languages.MeTTa.Prime.PrimeAbstractImplementationModel
open Mettapedia.Languages.MeTTa.Prime.PolicyKeyNIKAdmission

universe u uObservation uPolicy uValue uKey uCost uIndex uCapability uArtifact

/-! ## Profitability over the abstract implementation model -/

/-- A declared total cost observation on complete proof-relevant traces. -/
abbrev TraceCost {Observation : Type uObservation}
    (object : IndexedObservedOperationalObject.{u, uObservation} Observation)
    (Cost : Type uCost) :=
  ExecutionTrace object.operational → Cost

/-- Profitability evidence for an already-admitted execution model.  The
semantic refinement is an input to this proposition, never an output of it. -/
structure ExecutionProfitabilityReceipt
    {Observation : Type uObservation} {dependencies : DependencySystem}
    {revision : dependencies.Revision}
    {source target : IndexedObservedOperationalObject.{u, uObservation}
      Observation}
    (model : AdmittedExecutionModel dependencies revision source target)
    (Cost : Type uCost) [Preorder Cost]
    (sourceCost : TraceCost source Cost) (targetCost : TraceCost target Cost) :
    Prop where
  improves : ∀ trace,
    targetCost
        (ExecutionTrace.map model.admission.refinement.refinement trace) ≤
      sourceCost trace

/-! ## One shared-current capability bundle -/

/-- A receipt capability and optional profitability evidence displayed over
one admitted semantic implementation.  The profitability proposition is
required only when the surrounding request asks for it. -/
structure ExecutionCapabilityBundle
    {Observation : Type uObservation} {dependencies : DependencySystem}
    {revision : dependencies.Revision}
    {source target : IndexedObservedOperationalObject.{u, uObservation}
      Observation}
    (model : AdmittedExecutionModel dependencies revision source target)
    (request : PolicyRequest (ExecutionTrace target.operational))
    {Key : Type uKey} (key : ExecutionTrace target.operational → Key)
    (Cost : Type uCost) [Preorder Cost]
    (sourceCost : TraceCost source Cost) (targetCost : TraceCost target Cost)
    (requiresProfitability : Prop) where
  receiptView : AdmittedReceiptView model request key
  profitability : requiresProfitability →
    ExecutionProfitabilityReceipt model Cost sourceCost targetCost

namespace ExecutionCapabilityBundle

variable {Observation : Type uObservation} {dependencies : DependencySystem}
variable {revision currentRevision : dependencies.Revision}
variable {source target : IndexedObservedOperationalObject.{u, uObservation}
  Observation}
variable {model : AdmittedExecutionModel dependencies revision source target}
variable {request : PolicyRequest (ExecutionTrace target.operational)}
variable {Key : Type uKey} {key : ExecutionTrace target.operational → Key}
variable {Cost : Type uCost} [Preorder Cost]
variable {sourceCost : TraceCost source Cost} {targetCost : TraceCost target Cost}
variable {requiresProfitability : Prop}

/-- The single active witness is the currentness of the underlying semantic
admission.  Receipt and profitability displays cannot define a different
dependency world. -/
structure Active
    (_bundle : ExecutionCapabilityBundle model request key Cost sourceCost
      targetCost requiresProfitability)
    (currentRevision : dependencies.Revision) : Prop where
  semantic : model.admission.Active currentRevision

def activate
    (bundle : ExecutionCapabilityBundle model request key Cost sourceCost
      targetCost requiresProfitability)
    (current : dependencies.SameDependencies revision currentRevision) :
    bundle.Active currentRevision :=
  ⟨model.admission.activate current⟩

/-- Hot semantic execution is exactly the retained NIK refinement. -/
def Active.compile
    {bundle : ExecutionCapabilityBundle model request key Cost sourceCost
      targetCost requiresProfitability}
    (active : bundle.Active currentRevision) :
    ExecutionTrace source.operational → ExecutionTrace target.operational :=
  model.compileTrace active.semantic

/-- The request-scoped receipt is emitted after semantic execution. -/
def Active.emit
    {bundle : ExecutionCapabilityBundle model request key Cost sourceCost
      targetCost requiresProfitability}
    (active : bundle.Active currentRevision) (prepared : model.PreparedTrace) :
    Key :=
  bundle.receiptView.emit active.semantic prepared

/-- Hot policy evaluation uses only the keyed function retained by receipt
admission.  Profitability evidence is not an argument. -/
def Active.evaluate
    {bundle : ExecutionCapabilityBundle model request key Cost sourceCost
      targetCost requiresProfitability}
    (active : bundle.Active currentRevision) (prepared : model.PreparedTrace)
    (policy : request.Policy) : request.Value policy :=
  bundle.receiptView.evaluate active.semantic prepared policy

theorem Active.compile_eq_semantic
    {bundle : ExecutionCapabilityBundle model request key Cost sourceCost
      targetCost requiresProfitability}
    (active : bundle.Active currentRevision)
    (trace : ExecutionTrace source.operational) :
    active.compile trace = model.compileTrace active.semantic trace :=
  rfl

/-- The integrated keyed runner agrees with the complete target trace. -/
theorem Active.evaluate_eq
    {bundle : ExecutionCapabilityBundle model request key Cost sourceCost
      targetCost requiresProfitability}
    (active : bundle.Active currentRevision) (prepared : model.PreparedTrace)
    (policy : request.Policy) :
    active.evaluate prepared policy =
      request.observe policy
        (model.compileTrace active.semantic prepared.sourceTrace) :=
  bundle.receiptView.evaluate_eq active.semantic prepared policy

/-- Semantic observation agreement is inherited unchanged from the admitted
execution model. -/
theorem Active.semanticObservationAgreement
    {bundle : ExecutionCapabilityBundle model request key Cost sourceCost
      targetCost requiresProfitability}
    (active : bundle.Active currentRevision)
    (trace : ExecutionTrace source.operational) :
    target.observe (active.compile trace).2.2 = source.observe trace.2.2 :=
  model.compileTrace_observationAgreement active.semantic trace

/-- A policy-only bundle needs no profitability evidence. -/
def withoutProfitability
    (view : AdmittedReceiptView model request key) :
    ExecutionCapabilityBundle model request key Cost sourceCost targetCost
      False where
  receiptView := view
  profitability := False.elim

/-- When profitability is requested, it is supplied as an additional receipt
for the already-admitted model. -/
def withProfitability
    (view : AdmittedReceiptView model request key)
    (receipt : ExecutionProfitabilityReceipt model Cost sourceCost targetCost) :
    ExecutionCapabilityBundle model request key Cost sourceCost targetCost
      True where
  receiptView := view
  profitability := fun _ => receipt

/-- Staleness prevents the entire derived bundle from activating, while the
model's independently retained raw fallback remains exact. -/
theorem stale_prevents_bundle_and_preserves_fallback
    (bundle : ExecutionCapabilityBundle model request key Cost sourceCost
      targetCost requiresProfitability)
    {candidateRevision : dependencies.Revision}
    (stale : model.StaleAt candidateRevision)
    (prepared : model.PreparedTrace) :
    (¬ bundle.Active candidateRevision) ∧
      model.rawCodec.decode prepared.fallback = prepared.sourceTrace := by
  constructor
  · rintro ⟨active⟩
    exact model.stale_prevents_activation stale active
  · exact model.stale_preserves_fallback stale prepared

end ExecutionCapabilityBundle

/-! ## Exact semantic requests cannot hide external filtering -/

/-- Candidates which are both licensed and indistinguishable on every
requested semantic capability have identical membership in an exact
capability-request fibre.  An external profitability preference cannot
silently delete one of them. -/
theorem capabilityRequest_membership_iff_of_same_required_support
    {Index : Type uIndex} [PartialOrder Index] [DecidableEq Index]
    {source target :
      Mettapedia.GSLT.LanguageDef.NIKMetalogic.AdmissionObject.{uArtifact}}
    {family : RecognizedFamily.{uIndex, uCapability, uArtifact} Index source
      target}
    (request : family.CapabilityRequest) {first second : Index}
    (firstLicensed : first ∈ family.licensed)
    (secondLicensed : second ∈ family.licensed)
    (sameSupport : ∀ capability ∈ request.required,
      family.supports first capability ↔ family.supports second capability) :
    first ∈ request.candidates ↔ second ∈ request.candidates := by
  constructor
  · intro firstMember
    have firstData := (request.candidates_exact first).mp firstMember
    apply (request.candidates_exact second).mpr
    refine ⟨secondLicensed, ?_⟩
    intro capability required
    exact (sameSupport capability required).mp (firstData.2 capability required)
  · intro secondMember
    have secondData := (request.candidates_exact second).mp secondMember
    apply (request.candidates_exact first).mpr
    refine ⟨firstLicensed, ?_⟩
    intro capability required
    exact (sameSupport capability required).mpr
      (secondData.2 capability required)

/-! ## Positive and negative controls in one model -/

namespace Canary

/-- Type-valued equality evidence for the canary operational object. -/
inductive BoolExecution : Bool → Bool → Type
  | refl (state : Bool) : BoolExecution state state

def operational : IndexedOperationalObject where
  State := Bool
  Execution := BoolExecution
  Meaning := fun _ => True

def observed : IndexedObservedOperationalObject Unit where
  operational := operational
  observe := fun _ => some ()

def dependencies : DependencySystem where
  Revision := Bool × Bool
  Dependency := Unit
  Value := Bool
  read revision _ := revision.1

def traceCodec : ExactCodec (ExecutionTrace operational) where
  Representation := ExecutionTrace operational
  encode := id
  decode := id
  decode_encode := fun _ => rfl

def model : AdmittedExecutionModel dependencies (false, false)
    observed observed where
  admission := IndexedObservedAdmittedAt.id dependencies (false, false) observed
  rawCodec := traceCodec
  receiptCodec := traceCodec

def finalState : ExecutionTrace operational → Bool
  | ⟨_first, last, _execution⟩ => by
      change Bool at last
      exact last

def request : PolicyRequest (ExecutionTrace operational) :=
  singlePolicyRequest finalState False

def fullKey : ExecutionTrace operational → ExecutionTrace operational := id

def fullAdmission :
    PolicyKeyAdmission dependencies (false, false) request fullKey :=
  identityKeyAdmission dependencies (false, false) request

def fullView : AdmittedReceiptView model request fullKey where
  receiptAdmission := fullAdmission

def sourceCost : TraceCost observed Nat := fun _ => 1

def targetCost : TraceCost observed Nat := fun _ => 0

def profitable :
    ExecutionProfitabilityReceipt model Nat sourceCost targetCost where
  improves := fun _ => Nat.zero_le _

def bundle :
    ExecutionCapabilityBundle model request fullKey Nat sourceCost targetCost
      True :=
  ExecutionCapabilityBundle.withProfitability fullView profitable

def active : bundle.Active (false, true) :=
  bundle.activate (fun _ => rfl)

def falseTrace : ExecutionTrace operational :=
  ⟨false, false, BoolExecution.refl false⟩

def trueTrace : ExecutionTrace operational :=
  ⟨true, true, BoolExecution.refl true⟩

def preparedFalse : model.PreparedTrace :=
  model.prepare falseTrace

def preparedTrue : model.PreparedTrace :=
  model.prepare trueTrace

/-- One current witness activates semantic execution and the retained receipt
policy; profitability remains separately available. -/
theorem current_bundle_runs_all_requested_structure :
    active.compile falseTrace = falseTrace ∧
      active.evaluate preparedFalse () = false ∧
      ExecutionProfitabilityReceipt model Nat sourceCost targetCost :=
  ⟨rfl, rfl, bundle.profitability True.intro⟩

def badSourceCost : TraceCost observed Nat := fun _ => 0

def badTargetCost : TraceCost observed Nat := fun _ => 1

/-- Semantic admission and an exact receipt do not manufacture profitability
for a false cost claim. -/
theorem semantic_and_receipt_do_not_imply_profitability :
    Nonempty (AdmittedReceiptView model request fullKey) ∧
      ¬ Nonempty
        (ExecutionProfitabilityReceipt model Nat badSourceCost badTargetCost) := by
  constructor
  · exact ⟨fullView⟩
  · rintro ⟨receipt⟩
    have impossible := receipt.improves falseTrace
    exact Nat.not_succ_le_zero 0 impossible

def collapsedKey : ExecutionTrace operational → Unit := fun _ => ()

/-- The profitable semantic implementation cannot make a lossy receipt key
support a policy which distinguishes its collided traces. -/
theorem semantic_and_profitability_do_not_imply_receipt_sufficiency :
    Nonempty (ExecutionProfitabilityReceipt model Nat sourceCost targetCost) ∧
      ¬ Nonempty
        (PolicyKeyAdmission dependencies (false, false) request collapsedKey) := by
  constructor
  · exact ⟨profitable⟩
  · rintro ⟨admission⟩
    have collision : collapsedKey falseTrace = collapsedKey trueTrace := rfl
    have impossible := admission.supports () collision
    simp [request, singlePolicyRequest, finalState, falseTrace, trueTrace]
      at impossible

theorem relevant_change_is_stale : model.StaleAt (true, false) := by
  intro same
  have impossible := same ()
  simp [dependencies] at impossible

/-- Relevant staleness disables the integrated display but cannot revoke raw
execution. -/
theorem relevant_change_prevents_bundle_and_preserves_fallback :
    (¬ bundle.Active (true, false)) ∧
      model.rawCodec.decode preparedTrue.fallback = preparedTrue.sourceTrace :=
  bundle.stale_prevents_bundle_and_preserves_fallback
    relevant_change_is_stale preparedTrue

end Canary

#print axioms ExecutionCapabilityBundle.Active.evaluate_eq
#print axioms ExecutionCapabilityBundle.Active.semanticObservationAgreement
#print axioms ExecutionCapabilityBundle.stale_prevents_bundle_and_preserves_fallback
#print axioms capabilityRequest_membership_iff_of_same_required_support
#print axioms Canary.current_bundle_runs_all_requested_structure
#print axioms Canary.semantic_and_receipt_do_not_imply_profitability
#print axioms Canary.semantic_and_profitability_do_not_imply_receipt_sufficiency
#print axioms Canary.relevant_change_prevents_bundle_and_preserves_fallback

end Mettapedia.Languages.MeTTa.Prime.NIKIntegratedExecutionCapabilities
