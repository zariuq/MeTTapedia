import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentFragment
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeHOLFragmentDenotation

/-!
# Actual service requests followed by scoped native computation

A source retains its submitted matching request and wire, or its full typed
HOL replay request, together with an ordinary native computation under one
success binder. Invocation calls the corresponding operation of that same
assembly. Success supplies the actual returned native payload to the binder;
decline and missing representation remain distinct and run no continuation.

The request/response crossing is separate from the contextual effect program.
It can therefore be attached to a request/return execution language without
precomputing away the service operation. This module supplies no serialization
or GSLT evaluator. HOL requests retain the existing intrinsic syntax and raw
chart certificates; returned intrinsic HOL proofs are not unchecked external
bytes or native dependent inhabitants of their represented propositions.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServices

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.ScopedComputation
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open SharedJudgmentFragment

variable {n : Nat}

/-- The native environment interprets a HOL context at this service scope.
It is raw substitution data; its formation is an independent obligation. -/
inductive Request (n : Nat) where
  | matching (expected : PolarizedNeedMatchedIndex.Request) (input : NativeWireData.Wire)
  | hol (gamma : Mettapedia.Logic.HOL.Ctx Mettapedia.Logic.HOL.UniformListInduction.BaseSort)
      (replay : UniformListChartNIKService.ReplayRequest gamma)
      (environment : Sub Tower.Head gamma.length n)

inductive Status where
  | success
  | declined
  | representationFailure
  deriving DecidableEq, Repr

/-- A response contains data, except for the already disclosed intrinsic HOL
proof output. Indexing retains the exact request, including its certificates.
Neither successful constructor contains an admission proof about its payload. -/
inductive Response : Request n → Type where
  | declined (request : Request n) : Response request
  | matched {expected input} (source proposition : Tower.Tm 0) :
      Response (.matching expected input)
  | holProof {gamma replay environment}
      (proof : (UniformListChartNIKService.intrinsicProofSystem gamma).ProofObject)
      (represented : Tower.Tm gamma.length) : Response (.hol gamma replay environment)
  | representationFailure {gamma replay environment}
      (proof : (UniformListChartNIKService.intrinsicProofSystem gamma).ProofObject) :
      Response (.hol gamma replay environment)

namespace Response

def status {request : Request n} : Response request → Status
  | .declined _ => .declined
  | .matched _ _ | .holProof _ _ => .success
  | .representationFailure _ => .representationFailure

/-- HOL success returns the formed representation, not a purported native
proof of it. The actual native environment is read from the authored request. -/
def nativePayload? {request : Request n} : Response request → Option (Tower.Tm n × Tower.Tm n)
  | .declined _ | .representationFailure _ => none
  | .matched source proposition => some (liftClosed source, liftClosed proposition)
  | @holProof _ _ _ environment _ represented =>
      some (subst environment represented, .const `HOLUniformList.prop)

theorem payload_isSome_iff_status {request : Request n} (response : Response request) :
    response.nativePayload?.isSome = true ↔ response.status = .success := by
  cases response <;> simp [nativePayload?, status]

end Response

/-- The request and bound native continuation are authored source data.
The continuation is syntax, not a host function of an admitted proof. -/
structure Source (n : Nat) where
  request : Request n
  continuation : Code Tower.Head NativeExamples.Operation (n + 1)

def invoke (assembly : Assembly) : (request : Request n) → Response request
  | .matching expected input =>
      match assembly.reconstructMatch expected input with
      | none => .declined _
      | some (source, proposition) => .matched source proposition
  | .hol gamma replay _environment =>
      match assembly.produceHOL gamma replay with
      | none => .declined _
      | some proof =>
          match FormationSensitiveHOLInterface.represent
            FormationSensitiveHOLUniformList.signature replay.claim.2 with
          | none => .representationFailure proof
          | some represented => .holProof proof represented

/-- These rule-sized crossings expose the actual primitive calls. They do
not package execution of the native continuation into a relation query. -/
inductive Invocation (assembly : Assembly) : (request : Request n) → Response request → Prop where
  | matchingSuccess {expected input source proposition}
      (returned : assembly.reconstructMatch expected input = some (source, proposition)) :
      Invocation assembly (.matching expected input) (.matched source proposition)
  | matchingDecline {expected input}
      (declined : assembly.reconstructMatch expected input = none) :
      Invocation assembly (.matching expected input) (.declined _)
  | holSuccess {gamma replay environment proof represented}
      (returned : assembly.produceHOL gamma replay = some proof)
      (representation : FormationSensitiveHOLInterface.represent
        FormationSensitiveHOLUniformList.signature replay.claim.2 = some represented) :
      Invocation assembly (.hol gamma replay environment) (.holProof proof represented)
  | holDecline {gamma replay environment}
      (declined : assembly.produceHOL gamma replay = none) :
      Invocation assembly (.hol gamma replay environment) (.declined _)
  | holRepresentationFailure {gamma replay environment proof}
      (returned : assembly.produceHOL gamma replay = some proof)
      (missing : FormationSensitiveHOLInterface.represent
        FormationSensitiveHOLUniformList.signature replay.claim.2 = none) :
      Invocation assembly (.hol gamma replay environment) (.representationFailure proof)

theorem invoke_crossing (assembly : Assembly) (request : Request n) :
    Invocation assembly request (invoke assembly request) := by
  cases request with
  | matching expected input =>
      cases returned : assembly.reconstructMatch expected input with
      | none => simpa only [invoke, returned] using Invocation.matchingDecline returned
      | some payload =>
          simpa only [invoke, returned] using Invocation.matchingSuccess returned
  | hol gamma replay environment =>
      cases returned : assembly.produceHOL gamma replay with
      | none => simpa only [invoke, returned] using Invocation.holDecline returned
      | some proof =>
          cases represented : FormationSensitiveHOLInterface.represent
              FormationSensitiveHOLUniformList.signature replay.claim.2 with
          | none =>
              simpa only [invoke, returned, represented] using
                Invocation.holRepresentationFailure returned represented
          | some formula =>
              simpa only [invoke, returned, represented] using
                Invocation.holSuccess returned represented

theorem invoke_iff (assembly : Assembly) (request : Request n) (response : Response request) :
    invoke assembly request = response ↔ Invocation assembly request response := by
  constructor
  · intro equality
    rw [← equality]
    exact invoke_crossing assembly request
  · intro crossing
    cases crossing with
    | matchingSuccess returned => simp only [invoke, returned]
    | matchingDecline declined => simp only [invoke, declined]
    | holSuccess returned representation => simp only [invoke, returned, representation]
    | holDecline declined => simp only [invoke, declined]
    | holRepresentationFailure returned missing => simp only [invoke, returned, missing]

theorem invocation_deterministic {assembly : Assembly} {request : Request n}
    {first second : Response request}
    (left : Invocation assembly request first) (right : Invocation assembly request second) :
    first = second :=
  ((invoke_iff _ _ _).mpr left).symm.trans ((invoke_iff _ _ _).mpr right)

/-- This second phase uses the assembly's actual handler. It neither resets
state nor reduces the submitted source before the service has responded. -/
def continuationProgram (assembly : Assembly) (source : Source n)
    (response : Response source.request) : Option (Program Bool (Tower.Tm n) Nat) :=
  response.nativePayload?.map fun payload =>
    Code.interpret (assembly.execution n).handler (consSub payload.1 ids) source.continuation

theorem continuation_success {assembly : Assembly} {source : Source n}
    {response : Response source.request} {payload type : Tower.Tm n}
    (returned : response.nativePayload? = some (payload, type)) :
    continuationProgram assembly source response = some
      (Code.interpret (assembly.execution n).handler (consSub payload ids) source.continuation) := by
  simp only [continuationProgram, returned, Option.map_some]

theorem continuation_absent_iff {assembly : Assembly} {source : Source n}
    (response : Response source.request) :
    continuationProgram assembly source response = none ↔ response.status ≠ .success := by
  cases source with
  | mk request continuation =>
      cases response <;> simp [continuationProgram, Response.nativePayload?, Response.status]

/-! ## Admission and coverage use the same qualified assembly -/

variable {assembly : Assembly}

theorem matching_admitted
    (qualified : specification.Satisfies assembly) {expected input source proposition}
    (crossing : Invocation assembly (Request.matching (n := n) expected input)
      (.matched source proposition)) :
    ∃ transport : MatchedIndexDependentTransport.Transport,
      MatchedIndexDependentTransport.decodeAdmitted input = some transport.receipt ∧
      Nonempty (PolarizedNeedMatchedIndex.Evidence expected transport.receipt) ∧
      getElem? transport.receipt.values expected.index = some transport.selected ∧
      transport.selected = transport.receipt.output ∧
      proposition = transport.proposition ∧
      FormationSensitive.Judgment assembly.rules .nil source proposition := by
  cases crossing with
  | matchingSuccess returned =>
      exact reconstructed_selection
        (qualified .matchAdmission (by simp [specification])) returned

theorem hol_admitted
    (qualified : specification.Satisfies assembly) {gamma replay environment proof represented}
    (crossing : Invocation assembly (Request.hol (n := n) gamma replay environment)
      (.holProof proof represented)) :
    proof.1 = replay.claim ∧
    (UniformListChartNIKService.intrinsicKernel gamma).decide replay.claim proof = true ∧
    Mettapedia.Logic.HOL.ExtDerivation Mettapedia.Logic.HOL.UniformListInduction.Symbol
      replay.claim.1 replay.claim.2 ∧
    FormationSensitiveHOLInterface.represent FormationSensitiveHOLUniformList.signature
      replay.claim.2 = some represented ∧
    FormationSensitive.Judgment assembly.rules
      (FormationSensitiveHOLInterface.context FormationSensitiveHOLUniformList.types gamma)
      represented (.const `HOLUniformList.prop) := by
  cases crossing with
  | holSuccess returned representation =>
      have replayQualified : HOLReplayQualified assembly :=
        qualified .holReplay (by simp [specification])
      obtain ⟨binding, actual, assumptions, represented, _, formed, _⟩ :=
        replayQualified.2 _ _ _ returned
      have same := Option.some.inj (represented.symm.trans representation)
      subst actual
      obtain ⟨accepted, derivation, _⟩ := produced_hol_admission replayQualified returned
      exact ⟨binding, accepted, derivation, representation, formed⟩

theorem hol_submitted_replay_checked
    (qualified : specification.Satisfies assembly) {gamma replay environment proof represented}
    (crossing : Invocation assembly (Request.hol (n := n) gamma replay environment)
      (.holProof proof represented)) :
    UniformListChartNIKService.replayAccepted gamma replay = true := by
  cases crossing with
  | holSuccess returned _ =>
      have replayQualified : HOLReplayQualified assembly :=
        qualified .holReplay (by simp [specification])
      exact (replayQualified.1 _ _).mp (by simp only [returned, Option.isSome_some])

theorem hol_full_claim_formation
    (qualified : specification.Satisfies assembly) {gamma replay environment proof represented}
    (crossing : Invocation assembly (Request.hol (n := n) gamma replay environment)
      (.holProof proof represented)) :
    RepresentationAdmitted assembly gamma replay.claim := by
  cases crossing with
  | holSuccess returned _ =>
      exact (show HOLReplayQualified assembly from
        qualified .holReplay (by simp [specification])).2 _ _ _ returned |>.2

/-! ## The returned formula has its independently defined native meaning

These laws concern the actual service response and the actual substitution
in its request. The semantic environment is checked component by component;
formation of a native substitution alone does not identify its interpretation.
Truth additionally requires the source assumptions in the supplied model.
Neither the formula's formation nor an effectful continuation supplies a
native proof inhabitant of that formula.
-/

namespace HOLMeaning

open Mettapedia.Logic HOL.UniformListInduction
open NativeHOLFragmentDenotation

universe w

/-- The source-scope formula retained in a successful response is interpreted
by the constructorwise native judgment, not by decoding its bytes or reading
the already intrinsic proof object's conclusion as its definition. -/
theorem response_denotes (model : HOL.HenkinModel.{0, 0, w} BaseSort Symbol)
    {gamma : HOL.Ctx BaseSort} {replay : UniformListChartNIKService.ReplayRequest gamma}
    {environment : Sub Tower.Head gamma.length n} {proof represented}
    (crossing : Invocation assembly (.hol gamma replay environment)
      (.holProof proof represented)) :
    Denotes model represented (fun valuation => model.denote replay.claim.2 valuation) := by
  cases crossing with
  | holSuccess _ represented => exact representation_square replay.claim.2 represented

/-- A successful payload really is the represented source formula after the
submitted native substitution. The semantic counterpart of that substitution
is established from its actual components, including higher-order values. -/
theorem payload_denotes (model : HOL.HenkinModel.{0, 0, w} BaseSort Symbol)
    {gamma delta : HOL.Ctx BaseSort} {replay : UniformListChartNIKService.ReplayRequest gamma}
    {substitution : Sub Tower.Head gamma.length delta.length}
    (environment : model.Valuation delta → model.Valuation gamma)
    (components : ∀ {type} (index : HOL.Var gamma type),
      Denotes model (substitution (FormationSensitiveHOLInterface.variableIndex index))
        (fun valuation => environment valuation index))
    {response : Response (.hol gamma replay substitution)}
    (crossing : Invocation assembly (.hol gamma replay substitution) response)
    {payload type : Tower.Tm delta.length}
    (returned : response.nativePayload? = some (payload, type)) :
    type = .const `HOLUniformList.prop ∧
      Denotes model payload (fun valuation => model.denote replay.claim.2 (environment valuation)) := by
  cases crossing with
  | holSuccess produced representation =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj returned)
      exact ⟨rfl, (representation_square replay.claim.2 representation).substitute
        substitution environment components⟩
  | holDecline _ => cases returned
  | holRepresentationFailure _ _ => cases returned

/-- An independently interpreted service payload cannot be assigned a second
value. This needs interpretation of the actual request substitution, but no
truth assumption: uniqueness of meaning and validity remain distinct. -/
theorem payload_meaning_unique (model : HOL.HenkinModel.{0, 0, w} BaseSort Symbol)
    {gamma delta : HOL.Ctx BaseSort} {replay : UniformListChartNIKService.ReplayRequest gamma}
    {substitution : Sub Tower.Head gamma.length delta.length}
    (environment : model.Valuation delta → model.Valuation gamma)
    (components : ∀ {type} (index : HOL.Var gamma type),
      Denotes model (substitution (FormationSensitiveHOLInterface.variableIndex index))
        (fun valuation => environment valuation index))
    {response : Response (.hol gamma replay substitution)}
    (crossing : Invocation assembly (.hol gamma replay substitution) response)
    {payload type : Tower.Tm delta.length}
    (returned : response.nativePayload? = some (payload, type))
    {value : model.Valuation delta → HOL.Ty.denote model.Carrier .prop}
    (meaning : Denotes model payload value) (valuation : model.Valuation delta) :
    value valuation = model.denote replay.claim.2 (environment valuation) :=
  meaning.coherent (payload_denotes model environment components crossing returned).2 valuation

/-- Model validity is a further, assumption-relative consequence of the
qualified producer. The requested native term and its denotation are the
same ones that will open the actual continuation binder. -/
theorem payload_model_sound (qualified : specification.Satisfies assembly)
    (model : HOL.HenkinModel.{0, 0, w} BaseSort Symbol)
    (respects : model.FunctionsRespectEqv)
    {gamma delta : HOL.Ctx BaseSort} {replay : UniformListChartNIKService.ReplayRequest gamma}
    {substitution : Sub Tower.Head gamma.length delta.length}
    (environment : model.Valuation delta → model.Valuation gamma)
    (components : ∀ {type} (index : HOL.Var gamma type),
      Denotes model (substitution (FormationSensitiveHOLInterface.variableIndex index))
        (fun valuation => environment valuation index))
    {response : Response (.hol gamma replay substitution)}
    (crossing : Invocation assembly (.hol gamma replay substitution) response)
    {payload type : Tower.Tm delta.length}
    (returned : response.nativePayload? = some (payload, type)) :
    Denotes model payload (fun valuation => model.denote replay.claim.2 (environment valuation)) ∧
      ∀ valuation, model.ValuationAdmissible valuation →
        HOL.Soundness.SatisfiesHyps model (environment valuation) replay.claim.1 →
        (model.denote replay.claim.2 (environment valuation)).down := by
  refine ⟨(payload_denotes model environment components crossing returned).2, ?_⟩
  have derivation : HOL.ExtDerivation Symbol replay.claim.1 replay.claim.2 := by
    cases crossing with
    | holSuccess produced representation =>
        exact (hol_admitted qualified (environment := substitution)
          (.holSuccess produced representation)).2.2.1
    | holDecline _ => cases returned
    | holRepresentationFailure _ _ => cases returned
  intro valuation admissible assumptions
  exact HOL.Soundness.extDerivation_sound derivation respects
    (interpreted_environment_admissible substitution environment components admissible) assumptions

end HOLMeaning

theorem qualified_no_representation_failure
    (qualified : specification.Satisfies assembly) {gamma replay environment proof} :
    ¬ Invocation assembly (Request.hol (n := n) gamma replay environment)
      (.representationFailure proof) := by
  intro crossing
  cases crossing with
  | holRepresentationFailure returned missing =>
      have replayQualified : HOLReplayQualified assembly :=
        qualified .holReplay (by simp [specification])
      obtain ⟨_, _, _, represented, _⟩ := replayQualified.2 _ _ _ returned
      rw [missing] at represented
      cases represented

theorem matching_success_iff
    (qualified : specification.Satisfies assembly)
    (expected : PolarizedNeedMatchedIndex.Request) (input : NativeWireData.Wire) :
    (invoke assembly (Request.matching (n := n) expected input)).status = .success ↔
      (MatchedIndexDependentTransport.consume? expected input).isSome = true := by
  have exactness := match_acceptance_iff
    (qualified .matchAdmission (by simp [specification]))
    (qualified .matchCoverage (by simp [specification])) expected input
  cases returned : assembly.reconstructMatch expected input <;>
    simpa [invoke, returned, Response.status] using exactness

theorem hol_success_iff
    (qualified : specification.Satisfies assembly)
    (gamma : Mettapedia.Logic.HOL.Ctx Mettapedia.Logic.HOL.UniformListInduction.BaseSort)
    (replay : UniformListChartNIKService.ReplayRequest gamma)
    (environment : Sub Tower.Head gamma.length n) :
    (invoke assembly (.hol gamma replay environment)).status = .success ↔
      UniformListChartNIKService.replayAccepted gamma replay = true := by
  have replayQualified : HOLReplayQualified assembly :=
    qualified .holReplay (by simp [specification])
  have exactness := replayQualified.1 gamma replay
  cases returned : assembly.produceHOL gamma replay with
  | none => simpa [invoke, returned, Response.status] using exactness
  | some proof =>
      obtain ⟨_, represented, _, representation, _⟩ := replayQualified.2 _ _ _ returned
      simpa [invoke, returned, representation, Response.status] using exactness

/-- Only the HOL call has a nonempty source-context interpretation to check.
Matching outputs are closed; no cast from a raw wire is an environment proof. -/
def EnvironmentAdmitted (assembly : Assembly) (context : Tower.Ctx n) : Request n → Prop
  | .matching _ _ => FormationSensitive.ContextFormation assembly.rules context
  | .hol gamma _ environment =>
      FormationSensitive.ContextFormation assembly.rules context ∧
      FormationSensitive.CtxMor assembly.rules
        (FormationSensitiveHOLInterface.context FormationSensitiveHOLUniformList.types gamma)
        context environment

theorem invoked_payload_admitted
    (qualified : specification.Satisfies assembly) {context : Tower.Ctx n}
    {request : Request n} {response : Response request} {payload type : Tower.Tm n}
    (environment : EnvironmentAdmitted assembly context request)
    (crossing : Invocation assembly request response)
    (returned : response.nativePayload? = some (payload, type)) :
    FormationSensitive.Judgment assembly.rules context payload type := by
  cases crossing with
  | matchingSuccess reconstructed =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj returned)
      obtain ⟨_, _, _, admitted⟩ :=
        (show MatchAdmission assembly from qualified .matchAdmission (by simp [specification]))
          _ _ _ _ reconstructed
      exact ⟨environment, admitted.typing.renameTyping (fun index => Fin.elim0 index)⟩
  | holSuccess produced represented =>
      rename_i gamma replay rho proof formula
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj returned)
      have admitted := (hol_admitted qualified (environment := rho)
        (.holSuccess produced represented)).2.2.2.2
      simpa only [subst] using admitted.substitute environment.1 environment.2
  | matchingDecline _ => cases returned
  | holDecline _ => cases returned
  | holRepresentationFailure _ _ => cases returned

/-- The source body is independently admitted under the successful payload
type. Its actual selected payload opens that binder by refined substitution. -/
theorem continuation_preserves
    (qualified : specification.Satisfies assembly) {context : Tower.Ctx n}
    {source : Source n} {response : Response source.request} {payload type : Tower.Tm n}
    {resultType : Tower.Tm (n + 1)}
    (environment : EnvironmentAdmitted assembly context source.request)
    (crossing : Invocation assembly source.request response)
    (returned : response.nativePayload? = some (payload, type))
    (body : Judgment assembly.rules NativeExamples.signature (.snoc context type)
      source.continuation resultType)
    {state : Bool} {branch : BranchTrace} {output : WorldResult Bool (Tower.Tm n) Nat}
    (observed : output ∈ runWorldsAt
      (Code.interpret (assembly.execution n).handler (consSub payload ids) source.continuation)
      state branch) :
    FormationSensitive.Judgment assembly.rules context output.answer (inst0 payload resultType) := by
  have admitted := invoked_payload_admitted qualified environment crossing returned
  have identity : FormationSensitive.CtxMor assembly.rules context context ids := by
    intro index
    simpa only [ids, subst_ids] using
      (FormationSensitive.Typing.var (R := assembly.rules) (Γ := context) index)
  have extended := extendEnvironment identity (by simpa only [subst_ids] using admitted.typing)
  exact qualified_execution (qualified .execution (by simp [specification]))
    body admitted.context extended observed

theorem continuation_worlds
    (qualified : specification.Satisfies assembly) (source : Source n)
    (payload : Tower.Tm n) (state : Bool) (branch : BranchTrace) :
    runWorldsAt
      (Code.interpret (assembly.execution n).handler (consSub payload ids) source.continuation)
      state branch =
    Code.worlds (assembly.execution n).primitive (consSub payload ids)
      source.continuation state branch :=
  ImplementationStudy.qualified_worlds (assembly.execution n)
    ((qualified .execution (by simp [specification])) n) _ _ _ _

/-! ## Executed services and a genuinely payload-dependent continuation -/

namespace Examples

open NativeExamples

/-- The existing effectful choice/reflexivity computation runs first. Its
state and intents survive into dependent sequencing of the service payload.
The selected native payload, not a fixed term, is paired with its reflexivity. -/
def nativeContinuation : Code Tower.Head NativeExamples.Operation 3 :=
  .sequence (NativeExamples.source.rename Fin.succ)
    (.sequenceSigma (.returnValue (.var 1)) (.returnValue (.refl (.var 0))))

def matchingSource (expected : PolarizedNeedMatchedIndex.Request)
    (input : NativeWireData.Wire) : Source 2 :=
  ⟨.matching expected input, nativeContinuation⟩

def holSource
    (gamma : Mettapedia.Logic.HOL.Ctx Mettapedia.Logic.HOL.UniformListInduction.BaseSort)
    (replay : UniformListChartNIKService.ReplayRequest gamma)
    (environment : Sub Tower.Head gamma.length 2) : Source 2 :=
  ⟨.hol gamma replay environment, nativeContinuation⟩

def payloadSigma (type : Tower.Tm 0) : Tower.Tm n :=
  .sigma (liftClosed type) (.id (liftClosed type) (.var 0) (.var 0))

private theorem closed_formed (type : Tower.Tm 0)
    (formed : FormationSensitive.Typing assembly.rules .nil type (sortTm Tower.zero))
    (context : Tower.Ctx n) :
    FormationSensitive.Typing assembly.rules context (liftClosed type) (sortTm Tower.zero) :=
  formed.renameTyping (fun index => Fin.elim0 index)

theorem payloadSigma_formed (type : Tower.Tm 0)
    (formed : FormationSensitive.Typing assembly.rules .nil type (sortTm Tower.zero))
    (context : Tower.Ctx n) :
    FormationSensitive.Typing assembly.rules context (payloadSigma type)
      (sortTm (.max Tower.zero Tower.zero)) := by
  apply FormationSensitive.Typing.sigmaForm (closed_formed type formed context) (.sort Tower.zero)
    _ (.sort Tower.zero) (.sorts Tower.zero Tower.zero)
  apply FormationSensitive.Typing.idForm (closed_formed type formed _) (.sort Tower.zero)
  · simpa only [Ctx.lookup_snoc_zero, rename_liftClosed] using
      (FormationSensitive.Typing.var (R := assembly.rules)
        (Γ := .snoc context (liftClosed type)) 0)
  · simpa only [Ctx.lookup_snoc_zero, rename_liftClosed] using
      (FormationSensitive.Typing.var (R := assembly.rules)
        (Γ := .snoc context (liftClosed type)) 0)

private theorem rename_payloadSigma (type : Tower.Tm 0) {m : Nat} (rho : Ren n m) :
    rename rho (payloadSigma type) = payloadSigma type := by
  simp [payloadSigma, rename, rename_liftClosed, liftRen]

/-- The continuation is admitted as syntax before any service invocation.
Its native Sigma result really binds the returned payload as its identity index. -/
theorem nativeContinuation_admitted (type : Tower.Tm 0)
    (formed : FormationSensitive.Typing assembly.rules .nil type (sortTm Tower.zero)) :
    Judgment assembly.rules NativeExamples.signature
      (.snoc NativeExamples.context (liftClosed type)) nativeContinuation (payloadSigma type) := by
  let target : Tower.Ctx 3 := .snoc NativeExamples.context (liftClosed type)
  have targetFormed : FormationSensitive.ContextFormation assembly.rules target :=
    .snoc (OpaqueRelatorScopedComputation.context_formed assembly.declarations)
      (closed_formed type formed _) (.sort Tower.zero)
  have first := (OpaqueRelatorScopedComputation.source_judgments assembly.declarations).2
  have firstTyped := first.typing.rename (ρ := Fin.succ) (Δ := target) (fun _ => rfl)
  have firstFormed :=
    (NativeExamples.sigma_formed.includeSignature NativeIndexedFamilies.IntrinsicRelator.rawSignature).includeSignature
      assembly.declarations
  have firstFormed' : FormationSensitive.Typing assembly.rules target
      (rename Fin.succ (.sigma ground identityFamily)) (sortTm (.max Tower.zero Tower.zero)) :=
    (show FormationSensitive.Typing assembly.rules NativeExamples.context
      (.sigma ground identityFamily) (sortTm (.max Tower.zero Tower.zero)) from firstFormed).renameTyping
        (ρ := Fin.succ) (fun _ => rfl)
  refine ⟨targetFormed, Typing.sequence firstFormed' (.sort _) (payloadSigma_formed type formed target)
    (.sort _) firstTyped ?_⟩
  rw [rename_payloadSigma]
  apply Typing.sequenceSigma (payloadSigma_formed type formed _) (.sort _)
  · apply Typing.returnValue
    have selected : FormationSensitive.Typing assembly.rules
        (.snoc target (rename Fin.succ (.sigma ground identityFamily)))
        (.var (Fin.succ (0 : Fin 3))) (liftClosed type) := by
      simpa only [target, Ctx.lookup_snoc_succ, Ctx.lookup_snoc_zero, rename_liftClosed] using
        (FormationSensitive.Typing.var (R := assembly.rules)
          (Γ := .snoc target (rename Fin.succ (.sigma ground identityFamily))) (Fin.succ (0 : Fin 3)))
    simpa only [Fin.succ_zero_eq_one'] using selected
  · apply Typing.returnValue
    apply FormationSensitive.Typing.reflIntro
    simpa only [Ctx.lookup_snoc_zero, rename_liftClosed] using
      (FormationSensitive.Typing.var (R := assembly.rules)
        (Γ := .snoc (.snoc target (rename Fin.succ (.sigma ground identityFamily)))
          (liftClosed type)) 0)

theorem nativeContinuation_worlds (payload : Tower.Tm 2) (state : Bool) (branch : BranchTrace) :
    runWorldsAt (Code.interpret (common.execution 2).handler (consSub payload ids)
      nativeContinuation) state branch =
    [{ branch := false :: branch, answer := .pair payload (.refl payload),
       state := true, intents := [10, 30] },
     { branch := true :: branch, answer := .pair payload (.refl payload),
       state := false, intents := [20, 40] }] := by
  rfl

theorem nativeContinuation_results
    (qualified : specification.Satisfies assembly) {request : Request 2}
    {response : Response request} {payload : Tower.Tm 2} (type : Tower.Tm 0)
    (formed : FormationSensitive.Typing assembly.rules .nil type (sortTm Tower.zero))
    (environment : EnvironmentAdmitted assembly NativeExamples.context request)
    (crossing : Invocation assembly request response)
    (returned : response.nativePayload? = some (payload, liftClosed type))
    {state : Bool} {branch : BranchTrace} {output : WorldResult Bool (Tower.Tm 2) Nat}
    (observed : output ∈ runWorldsAt
      (Code.interpret (assembly.execution 2).handler (consSub payload ids) nativeContinuation)
      state branch) :
    FormationSensitive.Judgment assembly.rules NativeExamples.context output.answer (payloadSigma type) := by
  have preserved := continuation_preserves qualified (source := ⟨request, nativeContinuation⟩)
    environment crossing returned (nativeContinuation_admitted type formed) observed
  simpa [inst0, payloadSigma, subst, subst_liftClosed, liftSub, subst0] using preserved

def canonicalMatchingSource : Source 2 :=
  matchingSource PolarizedNeedMatchedIndex.Examples.canonical.request
    (PolarizedNeedMatchedIndex.admittedWire PolarizedNeedMatchedIndex.Examples.canonical)

def canonicalTransport : MatchedIndexDependentTransport.Transport :=
  ⟨PolarizedNeedMatchedIndex.Examples.canonical, PolarizedNeedMatchedIndex.Examples.b⟩

def actualHOLSource : Source 2 :=
  holSource [] (UniformListChartNIKService.actualRequest []) Fin.elim0

def alteredOutputSource : Source 2 :=
  matchingSource PolarizedNeedMatchedIndex.Examples.canonical.request
    (PolarizedNeedMatchedIndex.admittedWire PolarizedNeedMatchedIndex.Examples.changedOutput)

def alteredIndexSource : Source 2 :=
  matchingSource { PolarizedNeedMatchedIndex.Examples.canonical.request with index := 0 }
    (PolarizedNeedMatchedIndex.admittedWire PolarizedNeedMatchedIndex.Examples.canonical)

def malformedHOLSource : Source 2 :=
  holSource [] { UniformListChartNIKService.actualRequest [] with
    stepProof := Mettapedia.Logic.HOL.UniformListInductionChart.malformedCertificate [] } Fin.elim0

def alteredPremisesHOLSource : Source 2 :=
  holSource [] { UniformListChartNIKService.actualRequest [] with
    stepPremises := Mettapedia.Logic.HOL.UniformListInductionChart.alteredStepAssumptions [] } Fin.elim0

def changedClaimHOLSource : Source 2 :=
  holSource [] { UniformListChartNIKService.actualRequest [] with
    claim := (Mettapedia.Logic.HOL.UniformListInduction.equations,
      Mettapedia.Logic.HOL.UniformListInduction.mapLength) } Fin.elim0

theorem canonical_matching_crossing :
    Invocation common canonicalMatchingSource.request
      (.matched canonicalTransport.source canonicalTransport.proposition) := by
  apply Invocation.matchingSuccess
  exact congrArg (Option.map fun transport : MatchedIndexDependentTransport.Transport =>
    (transport.source, transport.proposition))
    (MatchedIndexDependentTransport.consume_checked_receipt _ _
      PolarizedNeedMatchedIndex.Examples.canonical_checked)

theorem actual_hol_crossing :
    Invocation common actualHOLSource.request
      (.holProof (UniformListChartNIKService.actualNativeProof [])
        FormationSensitiveHOLUniformList.rawMapLength) :=
  .holSuccess (UniformListChartNIKService.actual_produced [])
    (FormationSensitiveHOLUniformList.mapLength_represented [])

theorem canonical_matching_program :
    continuationProgram common canonicalMatchingSource (invoke common canonicalMatchingSource.request) =
      some (Code.interpret (common.execution 2).handler (consSub (liftClosed canonicalTransport.source) ids)
        nativeContinuation) := by
  rw [(invoke_iff _ _ _).mpr canonical_matching_crossing]
  rfl

def holPayload : Tower.Tm 2 :=
  subst Fin.elim0 (FormationSensitiveHOLUniformList.rawMapLength : Tower.Tm 0)

theorem actual_hol_program :
    continuationProgram common actualHOLSource (invoke common actualHOLSource.request) =
      some (Code.interpret (common.execution 2).handler (consSub holPayload ids) nativeContinuation) := by
  rw [(invoke_iff _ _ _).mpr actual_hol_crossing]
  rfl

private theorem canonical_type_formed :
    FormationSensitive.Typing common.rules .nil canonicalTransport.proposition (sortTm Tower.zero) :=
  HOLNativeRelatorCompatibility.wire_relator_typing
    (.idForm (NativeWireRelatorCompatibility.dataType_formed .nil) (.sort Tower.zero)
      (MatchedIndexDependentTransport.nativePattern_typed .nil _)
      (MatchedIndexDependentTransport.nativePattern_typed .nil _))

private theorem hol_proposition_formed :
    FormationSensitive.Typing common.rules .nil (.const `HOLUniformList.prop) (sortTm Tower.zero) :=
  HOLNativeRelatorCompatibility.hol_typing (FormationSensitiveHOLUniformList.proposition_formed .nil)

/-- The actual receipt call, its dependent continuation and all ordered
native results are connected by one returned payload and one assembly. -/
theorem canonical_matching_workload (state : Bool) (branch : BranchTrace) :
    ∃ program : Program Bool (Tower.Tm 2) Nat,
      continuationProgram common canonicalMatchingSource
        (invoke common canonicalMatchingSource.request) = some program ∧
      runWorldsAt program state branch =
        [{ branch := false :: branch,
           answer := .pair (liftClosed canonicalTransport.source) (.refl (liftClosed canonicalTransport.source)),
           state := true, intents := [10, 30] },
         { branch := true :: branch,
           answer := .pair (liftClosed canonicalTransport.source) (.refl (liftClosed canonicalTransport.source)),
           state := false, intents := [20, 40] }] ∧
      ∀ output ∈ runWorldsAt program state branch,
        FormationSensitive.Judgment common.rules NativeExamples.context output.answer
          (payloadSigma canonicalTransport.proposition) := by
  refine ⟨_, canonical_matching_program, nativeContinuation_worlds _ state branch, ?_⟩
  intro output observed
  exact nativeContinuation_results common_qualified (request := canonicalMatchingSource.request)
    canonicalTransport.proposition canonical_type_formed
    (OpaqueRelatorScopedComputation.context_formed common.declarations)
    canonical_matching_crossing rfl observed

/-- The native result contains the actual represented formula and native
reflexivity at that formula. Its source HOL proof is retained at the separate
response boundary; this theorem does not identify those two proof notions. -/
theorem actual_hol_workload (state : Bool) (branch : BranchTrace) :
    ∃ program : Program Bool (Tower.Tm 2) Nat,
      continuationProgram common actualHOLSource (invoke common actualHOLSource.request) = some program ∧
      runWorldsAt program state branch =
        [{ branch := false :: branch, answer := .pair holPayload (.refl holPayload),
           state := true, intents := [10, 30] },
         { branch := true :: branch, answer := .pair holPayload (.refl holPayload),
           state := false, intents := [20, 40] }] ∧
      ∀ output ∈ runWorldsAt program state branch,
        FormationSensitive.Judgment common.rules NativeExamples.context output.answer
          (payloadSigma (.const `HOLUniformList.prop)) := by
  refine ⟨_, actual_hol_program, nativeContinuation_worlds _ state branch, ?_⟩
  intro output observed
  exact nativeContinuation_results common_qualified (request := actualHOLSource.request)
    (.const `HOLUniformList.prop) hol_proposition_formed
    ⟨OpaqueRelatorScopedComputation.context_formed common.declarations, fun index => Fin.elim0 index⟩
    actual_hol_crossing rfl observed

theorem actual_hol_source_derivation :
    Mettapedia.Logic.HOL.ExtDerivation Mettapedia.Logic.HOL.UniformListInduction.Symbol
      (UniformListChartNIKService.actualRequest []).claim.1
      (UniformListChartNIKService.actualRequest []).claim.2 :=
  (hol_admitted common_qualified actual_hol_crossing).2.2.1

/-- The actual response retains a closed native formula with a true standard
interpretation and a false junk interpretation. The latter model satisfies
the displayed equations but not the induction assumption of the accepted
source proof. This concerns the retained formula, not an interpretation of
the surrounding mixed native context or its identity proofs. -/
theorem actual_hol_retained_model_boundary :
    invoke common actualHOLSource.request =
      .holProof (UniformListChartNIKService.actualNativeProof [])
        FormationSensitiveHOLUniformList.rawMapLength ∧
    NativeHOLFragmentDenotation.Denotes
      Mettapedia.Logic.HOL.UniformListInduction.StandardListModel.model
      (gamma := [])
      (FormationSensitiveHOLUniformList.rawMapLength : Tower.Tm 0)
      (NativeHOLFragmentDenotation.mapLengthValue
        Mettapedia.Logic.HOL.UniformListInduction.StandardListModel.model []) ∧
    (∀ valuation, (NativeHOLFragmentDenotation.mapLengthValue
      Mettapedia.Logic.HOL.UniformListInduction.StandardListModel.model [] valuation).down) ∧
    NativeHOLFragmentDenotation.Denotes
      Mettapedia.Logic.HOL.UniformListInduction.JunkModel.model
      (gamma := [])
      (FormationSensitiveHOLUniformList.rawMapLength : Tower.Tm 0)
      (NativeHOLFragmentDenotation.mapLengthValue
        Mettapedia.Logic.HOL.UniformListInduction.JunkModel.model []) ∧
    (∀ valuation, ¬ (NativeHOLFragmentDenotation.mapLengthValue
      Mettapedia.Logic.HOL.UniformListInduction.JunkModel.model [] valuation).down) ∧
    (∀ formula ∈ Mettapedia.Logic.HOL.UniformListInduction.equations (Γ := []),
      Mettapedia.Logic.HOL.UniformListInduction.JunkModel.model.models formula) ∧
    ¬ Mettapedia.Logic.HOL.UniformListInduction.JunkModel.model.models
      Mettapedia.Logic.HOL.UniformListInduction.inductionPrinciple :=
  ⟨(invoke_iff _ _ _).mpr actual_hol_crossing,
    (NativeHOLFragmentDenotation.standard_native_mapLength []).1,
    (NativeHOLFragmentDenotation.standard_native_mapLength []).2,
    (NativeHOLFragmentDenotation.junk_native_mapLength []).1,
    (NativeHOLFragmentDenotation.junk_native_mapLength []).2.1,
    (NativeHOLFragmentDenotation.junk_native_mapLength []).2.2.1,
    (NativeHOLFragmentDenotation.junk_native_mapLength []).2.2.2⟩

/-- Requests are not specialized to the displayed two-element vector: every
valid finite index uses that request's own vector and submitted receipt. -/
theorem vector_matching_succeeds (values : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (index : Fin values.length) :
    (invoke common (matchingSource (PolarizedNeedMatchedIndex.Examples.vectorRequest values index.val)
      (PolarizedNeedMatchedIndex.admittedWire
        (PolarizedNeedMatchedIndex.Examples.vectorReceipt values index))).request).status = .success := by
  apply (matching_success_iff common_qualified _ _).mpr
  rw [MatchedIndexDependentTransport.consume_checked_receipt _ _
    (PolarizedNeedMatchedIndex.select_validates
      (PolarizedNeedMatchedIndex.Examples.vector_selected values index))]
  rfl

theorem altered_output_declines :
    invoke common alteredOutputSource.request = .declined alteredOutputSource.request :=
  (invoke_iff _ _ _).mpr (.matchingDecline altered_match_output_rejected)

theorem altered_index_declines :
    invoke common alteredIndexSource.request = .declined alteredIndexSource.request := by
  apply (invoke_iff _ _ _).mpr
  apply Invocation.matchingDecline
  exact match_rejects_invalid common_match_admission
    (MatchedIndexDependentTransport.consume_rejects_index (by decide))

theorem malformed_hol_declines :
    invoke common malformedHOLSource.request = .declined malformedHOLSource.request :=
  (invoke_iff _ _ _).mpr (.holDecline (UniformListChartNIKService.malformed_leaf_rejected []))

theorem altered_hol_premises_decline :
    invoke common alteredPremisesHOLSource.request = .declined alteredPremisesHOLSource.request :=
  (invoke_iff _ _ _).mpr (.holDecline (UniformListChartNIKService.altered_local_premise_rejected []))

theorem changed_hol_claim_declines :
    invoke common changedClaimHOLSource.request = .declined changedClaimHOLSource.request :=
  (invoke_iff _ _ _).mpr (.holDecline (UniformListChartNIKService.missing_induction_request_rejected []))

theorem declined_sources_do_not_run :
    continuationProgram common alteredOutputSource (invoke common alteredOutputSource.request) = none ∧
    continuationProgram common malformedHOLSource (invoke common malformedHOLSource.request) = none := by
  rw [altered_output_declines, malformed_hol_declines]
  exact ⟨rfl, rfl⟩

theorem changed_request_sources_do_not_run :
    continuationProgram common alteredIndexSource (invoke common alteredIndexSource.request) = none ∧
    continuationProgram common alteredPremisesHOLSource
      (invoke common alteredPremisesHOLSource.request) = none ∧
    continuationProgram common changedClaimHOLSource (invoke common changedClaimHOLSource.request) = none := by
  rw [altered_index_declines, altered_hol_premises_decline, changed_hol_claim_declines]
  exact ⟨rfl, rfl, rfl⟩

theorem always_declining_assembly_does_not_run :
    invoke decliningMatch canonicalMatchingSource.request = .declined canonicalMatchingSource.request ∧
    continuationProgram decliningMatch canonicalMatchingSource
      (invoke decliningMatch canonicalMatchingSource.request) = none ∧
    invoke decliningHOL actualHOLSource.request = .declined actualHOLSource.request ∧
    continuationProgram decliningHOL actualHOLSource
      (invoke decliningHOL actualHOLSource.request) = none := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end Examples

#print axioms invoke_iff
#print axioms invocation_deterministic
#print axioms matching_admitted
#print axioms hol_admitted
#print axioms hol_submitted_replay_checked
#print axioms hol_full_claim_formation
#print axioms HOLMeaning.response_denotes
#print axioms HOLMeaning.payload_denotes
#print axioms HOLMeaning.payload_meaning_unique
#print axioms HOLMeaning.payload_model_sound
#print axioms qualified_no_representation_failure
#print axioms matching_success_iff
#print axioms hol_success_iff
#print axioms invoked_payload_admitted
#print axioms continuation_preserves
#print axioms continuation_worlds
#print axioms Examples.nativeContinuation_admitted
#print axioms Examples.nativeContinuation_worlds
#print axioms Examples.nativeContinuation_results
#print axioms Examples.canonical_matching_crossing
#print axioms Examples.actual_hol_crossing
#print axioms Examples.canonical_matching_program
#print axioms Examples.actual_hol_program
#print axioms Examples.canonical_matching_workload
#print axioms Examples.actual_hol_workload
#print axioms Examples.actual_hol_source_derivation
#print axioms Examples.actual_hol_retained_model_boundary
#print axioms Examples.vector_matching_succeeds
#print axioms Examples.declined_sources_do_not_run
#print axioms Examples.changed_request_sources_do_not_run
#print axioms Examples.always_declining_assembly_does_not_run

#eval (invoke common Examples.canonicalMatchingSource.request).status
#eval (invoke common Examples.actualHOLSource.request).status
#eval (invoke common Examples.alteredOutputSource.request).status
#eval (invoke common Examples.alteredIndexSource.request).status
#eval (invoke common Examples.malformedHOLSource.request).status
#eval (invoke common Examples.alteredPremisesHOLSource.request).status
#eval (invoke common Examples.changedClaimHOLSource.request).status

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServices
