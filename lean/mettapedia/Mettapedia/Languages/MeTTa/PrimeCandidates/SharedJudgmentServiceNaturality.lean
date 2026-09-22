import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentPolarizedServices

/-!
# Qualified target-scope substitution for actual shared service calls

HOL operations reindex their native argument templates under the argument
binder. Every native argument is supported by that structural square.
Matching inspects its native argument as wire data: encoded wire terms are
opaque to native substitution, but a native variable can become readable
only after substitution. Consequently formation alone cannot justify the
unrestricted callback square.

The source class below is concrete: all HOL arguments and encoded matching
arguments. The proofs retain actual submitted requests, responses, dependent
payload types and explicit retryable residuals. Admission uses a separately
formed native substitution and the same assembly's qualification. No result
equates wire syntax with an open native argument, chooses a global strategy,
or extends the square to arbitrary machine heaps and sharing consumers.
-/

open Mettapedia.Machines.BranchLocalNeed

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceNaturality

open Mettapedia.Logic
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation NeedReference
open SharedJudgmentFragment SharedJudgmentServices SharedJudgmentPolarizedServices

variable {n m k : Nat}

/-- The argument hole remains the newest binder. Source claims and supplied
certificates are not rewritten as if they were native open terms. -/
def reindexOperation (substitution : Sub Tower.Head n m) : Operation n → Operation m
  | .matching expected => .matching expected
  | .hol gamma replay environment => .hol gamma replay (subComp (liftSub substitution) environment)

@[simp] theorem reindexOperation_ids (operation : Operation n) :
    reindexOperation ids operation = operation := by
  cases operation <;> simp only [reindexOperation, liftSub_ids, subComp_ids_left]

theorem reindexOperation_comp (later : Sub Tower.Head m k) (earlier : Sub Tower.Head n m)
    (operation : Operation n) :
    reindexOperation later (reindexOperation earlier operation) =
      reindexOperation (subComp later earlier) operation := by
  cases operation with
  | matching expected => rfl
  | hol gamma replay environment =>
      have lifted : subComp (liftSub later) (liftSub earlier) = liftSub (subComp later earlier) := by
        funext index
        exact liftSub_comp_apply later earlier index
      simp only [reindexOperation, subComp_assoc, lifted]

/-- This sufficient source grammar is independent of callback results.
It does not classify every malformed argument whose failure happens to be
stable under a particular substitution. -/
inductive SupportedArgument : {n : Nat} → Operation n → Tower.Tm n → Prop where
  | wire {n : Nat} (expected : PolarizedNeedMatchedIndex.Request) (input : NativeWireData.Wire) :
      SupportedArgument (.matching expected) (NativeWireData.encode (n := n) input)
  | hol {n : Nat} (gamma : HOL.Ctx HOL.UniformListInduction.BaseSort)
      (replay : UniformListChartNIKService.ReplayRequest gamma)
      (environment : Sub Tower.Head gamma.length (n + 1)) (argument : Tower.Tm n) :
      SupportedArgument (.hol gamma replay environment) argument

theorem SupportedArgument.reindex (substitution : Sub Tower.Head n m)
    {operation : Operation n} {argument : Tower.Tm n}
    (supported : SupportedArgument operation argument) :
    SupportedArgument (reindexOperation substitution operation) (subst substitution argument) := by
  cases supported with
  | wire expected input =>
      simpa only [reindexOperation, NativeWireData.subst_encode] using
        (SupportedArgument.wire (n := m) expected input)
  | hol gamma replay environment argument => exact .hol gamma replay _ _

/-- Filling the argument binder commutes with actual target substitution. -/
theorem reindex_filled_environment (substitution : Sub Tower.Head n m)
    (argument : Tower.Tm n) {length : Nat}
    (environment : Sub Tower.Head length (n + 1)) :
    subComp (consSub (subst substitution argument) ids)
        (subComp (liftSub substitution) environment) =
      subComp substitution (subComp (consSub argument ids) environment) := by
  rw [subComp_assoc, ScopedComputation.Code.consSub_liftSub_comp,
    subComp_ids_left, subComp_assoc, subComp_consSub, subComp_ids_right]

theorem submitted_reindex (substitution : Sub Tower.Head n m)
    {operation : Operation n} {argument : Tower.Tm n}
    (supported : SupportedArgument operation argument) :
    submitted? (reindexOperation substitution operation) (subst substitution argument) =
      (submitted? operation argument).map (Request.substitute substitution) := by
  cases supported with
  | wire expected input =>
      simp only [reindexOperation, NativeWireData.subst_encode,
        submitted_matching_encode, Option.map_some, Request.substitute]
  | hol gamma replay environment argument =>
      simp only [reindexOperation, submitted?, Option.map_some, Request.substitute,
        reindex_filled_environment]

/-- For matching, preservation of the inspected wire is precisely the
submitted-request condition. Native admission alone says nothing about it. -/
theorem submitted_matching_square_iff (substitution : Sub Tower.Head n m)
    (expected : PolarizedNeedMatchedIndex.Request) (argument : Tower.Tm n) :
    submitted? (reindexOperation substitution (.matching expected)) (subst substitution argument) =
        (submitted? (.matching expected) argument).map (Request.substitute substitution) ↔
      NativeWireData.decode (subst substitution argument) = NativeWireData.decode argument := by
  cases before : NativeWireData.decode argument <;>
    cases after : NativeWireData.decode (subst substitution argument) <;>
    simp [reindexOperation, submitted?, before, after, Request.substitute]

/-- Reindex the complete dependent pair, not an equality cast on the
response alone and not a replacement call to another producer. -/
def reindexResponse (substitution : Sub Tower.Head n m)
    (result : Sigma (@Response n)) : Sigma (@Response m) :=
  ⟨result.1.substitute substitution, result.2.substitute substitution⟩

/-- Retaining the complete request makes its structural substitution square
both necessary and sufficient for the actual dependent callback square. -/
theorem invocation_reindex_iff_submitted (assembly : Assembly) (substitution : Sub Tower.Head n m)
    (operation : Operation n) (argument : Tower.Tm n) :
    invocation? assembly (reindexOperation substitution operation) (subst substitution argument) =
        (invocation? assembly operation argument).map (reindexResponse substitution) ↔
      submitted? (reindexOperation substitution operation) (subst substitution argument) =
        (submitted? operation argument).map (Request.substitute substitution) := by
  constructor
  · intro same
    have projected := congrArg (Option.map (fun result : Sigma (@Response m) => result.1)) same
    simpa only [invocation?, Option.map_map, Function.comp_def, reindexResponse, Option.map_id'] using projected
  · intro submitted
    simp only [invocation?, submitted, Option.map_map]
    congr 1
    funext request
    simp only [Function.comp_def, reindexResponse, invoke_substitute]

/-- This criterion concerns the full retained invocation. Equality of a
coarser returned value need not determine which receipt was submitted. -/
theorem invocation_matching_square_iff (assembly : Assembly) (substitution : Sub Tower.Head n m)
    (expected : PolarizedNeedMatchedIndex.Request) (argument : Tower.Tm n) :
    invocation? assembly (reindexOperation substitution (.matching expected)) (subst substitution argument) =
        (invocation? assembly (.matching expected) argument).map (reindexResponse substitution) ↔
      NativeWireData.decode (subst substitution argument) = NativeWireData.decode argument := by
  rw [invocation_reindex_iff_submitted, submitted_matching_square_iff]

/-- Actual invocation commutes on the stated source class for every raw
assembly. The callback equations are derived, not qualification premises. -/
theorem invocation_reindex (assembly : Assembly) (substitution : Sub Tower.Head n m)
    {operation : Operation n} {argument : Tower.Tm n}
    (supported : SupportedArgument operation argument) :
    invocation? assembly (reindexOperation substitution operation) (subst substitution argument) =
      (invocation? assembly operation argument).map (reindexResponse substitution) :=
  (invocation_reindex_iff_submitted assembly substitution operation argument).mpr
    (submitted_reindex substitution supported)

def reindexResidual (substitution : Sub Tower.Head n m) : Residual n → Residual m
  | .unreadable operation argument =>
      .unreadable (reindexOperation substitution operation) (subst substitution argument)
  | .noPayload request response =>
      .noPayload (request.substitute substitution) (response.substitute substitution)

def reindexRetry (substitution : Sub Tower.Head n m) : RetryReason (Residual n) → RetryReason (Residual m)
  | .domain fault => .domain (reindexResidual substitution fault)
  | .blackhole cell => .blackhole cell
  | .outOfScope cell => .outOfScope cell
  | .noRule cell => .noRule cell
  | .ownershipLost cell expected actual => .ownershipLost cell expected actual
  | .allocationCollision cell => .allocationCollision cell

/-- Preserve the stable/retryable distinction. In particular, an unreadable
source call is not transported into a successful result by this observation. -/
def reindexProduced (substitution : Sub Tower.Head n m) :
    Produced (Tower.Tm n) Empty (Residual n) → Produced (Tower.Tm m) Empty (Residual m)
  | .value value => .value (subst substitution value)
  | .stableFault impossible => nomatch impossible
  | .retryableFault reason => .retryableFault (reindexRetry substitution reason)

theorem responseProduced_reindex (substitution : Sub Tower.Head n m)
    {request : Request n} (response : Response request) :
    responseProduced (response.substitute substitution) =
      reindexProduced substitution (responseProduced response) := by
  cases response <;>
    simp only [Response.substitute, responseProduced, Response.nativePayload?, reindexProduced,
      reindexRetry, reindexResidual, subst_liftClosed, subst_subComp]

theorem primitive_reindex (assembly : Assembly) (substitution : Sub Tower.Head n m)
    {operation : Operation n} {argument : Tower.Tm n}
    (supported : SupportedArgument operation argument) :
    primitive assembly (reindexOperation substitution operation) (subst substitution argument) =
      reindexProduced substitution (primitive assembly operation argument) := by
  unfold primitive
  rw [invocation_reindex assembly substitution supported]
  cases invocation? assembly operation argument with
  | none => rfl
  | some result => exact responseProduced_reindex substitution result.2

/-- The same submitted callback square transports both payload and its
dependent native type through an independently admitted substitution. -/
theorem reindexed_callback_admitted {assembly : Assembly}
    (qualified : specification.Satisfies assembly)
    {source : Tower.Ctx n} {target : Tower.Ctx m}
    (substitution : Sub Tower.Head n m)
    (targetFormed : FormationSensitive.ContextFormation assembly.rules target)
    (typed : FormationSensitive.CtxMor assembly.rules source target substitution)
    {operation : Operation n} {argument argumentType : Tower.Tm n}
    (supported : SupportedArgument operation argument)
    (argumentAdmitted : FormationSensitive.Judgment assembly.rules source argument argumentType)
    {request : Request n} {response : Response request} {value type : Tower.Tm n}
    (environment : EnvironmentAdmitted assembly source request)
    (called : invocation? assembly operation argument = some ⟨request, response⟩)
    (payload : response.nativePayload? = some (value, type)) :
    invocation? assembly (reindexOperation substitution operation) (subst substitution argument) =
        some ⟨request.substitute substitution, response.substitute substitution⟩ ∧
      (response.substitute substitution).nativePayload? =
        some (subst substitution value, subst substitution type) ∧
      EnvironmentAdmitted assembly target (request.substitute substitution) ∧
      FormationSensitive.Judgment assembly.rules target
        (subst substitution argument) (subst substitution argumentType) ∧
      FormationSensitive.Judgment assembly.rules target
        (subst substitution value) (subst substitution type) := by
  have transported := environment.substitute targetFormed typed
  have crossing := ((invocation_iff assembly operation argument request response).mp called).2
  have returned : (response.substitute substitution).nativePayload? =
      some (subst substitution value, subst substitution type) := by
    rw [Response.nativePayload_substitute, payload, Option.map_some]
  refine ⟨?_, returned, transported, argumentAdmitted.substitute targetFormed typed,
    invoked_payload_admitted qualified transported (crossing.substitute substitution) returned⟩
  rw [invocation_reindex assembly substitution supported, called]
  rfl

/-! ## Formed source data need not commute with inspection -/

namespace WireControls

open PolarizedNeedMatchedIndex PolarizedNeedMatchedIndex.Examples
open SharedJudgmentServices.Examples
open SharedJudgmentPolarizedServices.Controls

def sourceContext : Tower.Ctx 1 := .snoc .nil NativeWireData.dataType

theorem sourceContext_formed : FormationSensitive.ContextFormation common.rules sourceContext :=
  .snoc .nil (HOLNativeRelatorCompatibility.wire_typing (NativeWireData.dataType_formed _))
    (.sort Tower.zero)

/-- Replace an open native Data argument by an actual validated wire receipt. -/
def fillReceipt : Sub Tower.Head 1 0 := fun _ => NativeWireData.encode (admittedWire canonical)

theorem fillReceipt_typed :
    FormationSensitive.CtxMor common.rules sourceContext .nil fillReceipt := by
  intro index
  have only : index = 0 := Fin.eq_zero index
  subst index
  exact HOLNativeRelatorCompatibility.wire_typing
    (NativeWireData.encode_typing .nil (admittedWire canonical))

theorem open_argument_admitted :
    FormationSensitive.Judgment common.rules sourceContext (.var 0) NativeWireData.dataType :=
  ⟨sourceContext_formed, .var 0⟩

theorem filled_argument_admitted :
    FormationSensitive.Judgment common.rules .nil
      (subst fillReceipt (.var 0)) NativeWireData.dataType :=
  open_argument_admitted.substitute .nil fillReceipt_typed

theorem open_argument_unreadable : NativeWireData.decode (n := 1) (.var 0) = none :=
  NativeWireData.native_variable_rejected 0

theorem filled_argument_readable :
    NativeWireData.decode (subst fillReceipt (.var 0)) = some (admittedWire canonical) :=
  NativeWireData.decode_encode _

/-- The input itself is a canonical wire datum, so even a substitution that
changes a native variable cannot change its internal quoted syntax. -/
theorem encoded_receipt_square :
    primitive common (reindexOperation fillReceipt matchingOperation)
        (subst fillReceipt receiptArgument) =
      reindexProduced fillReceipt (primitive common matchingOperation receiptArgument) :=
  primitive_reindex common fillReceipt (.wire canonical.request (admittedWire canonical))

theorem encoded_receipt_returns :
    primitive common (reindexOperation fillReceipt matchingOperation)
        (subst fillReceipt receiptArgument) =
      .value (liftClosed canonicalTransport.source) := by
  rw [encoded_receipt_square, canonical_callback]
  simp only [reindexProduced, subst_liftClosed]

theorem filled_call_returns :
    primitive common (reindexOperation fillReceipt matchingOperation)
        (subst fillReceipt (.var 0)) =
      .value (liftClosed canonicalTransport.source) :=
  matching_primitive SharedJudgmentAssemblyServices.ReceiptControls.canonical_distinct_returned_proofs.1

/-- Failure before substitution and success after substitution are different
actual callbacks, despite formation of both arguments and the substitution. -/
theorem open_argument_breaks_square :
    primitive common (reindexOperation fillReceipt matchingOperation)
        (subst fillReceipt (.var 0)) ≠
      reindexProduced fillReceipt (primitive common matchingOperation (.var 0)) := by
  rw [filled_call_returns, unreadable_callback]
  intro same
  cases same

theorem formed_substitution_is_not_sufficient :
    FormationSensitive.Judgment common.rules sourceContext (.var 0) NativeWireData.dataType ∧
      FormationSensitive.CtxMor common.rules sourceContext .nil fillReceipt ∧
      FormationSensitive.Judgment common.rules .nil
        (subst fillReceipt (.var 0)) NativeWireData.dataType ∧
      primitive common (reindexOperation fillReceipt matchingOperation)
          (subst fillReceipt (.var 0)) ≠
        reindexProduced fillReceipt (primitive common matchingOperation (.var 0)) :=
  ⟨open_argument_admitted, fillReceipt_typed, filled_argument_admitted, open_argument_breaks_square⟩

/-- The negative control is outside the stated sufficient grammar, not a
counterexample to the qualified theorem. -/
theorem open_argument_not_supported :
    ¬ SupportedArgument matchingOperation (.var 0) := by
  intro supported
  have square := primitive_reindex common fillReceipt supported
  exact open_argument_breaks_square square

theorem altered_receipt_residual_transports :
    primitive common (reindexOperation fillReceipt matchingOperation)
        (subst fillReceipt alteredArgument) =
      .retryableFault (.domain (.noPayload
        (.matching canonical.request (admittedWire changedOutput)) (.declined _))) := by
  rw [primitive_reindex common fillReceipt (operation := matchingOperation) (argument := alteredArgument)
    (.wire canonical.request (admittedWire changedOutput)), altered_callback]
  rfl

end WireControls

/-! ## Actual higher-order HOL arguments cross a target-scope boundary -/

namespace HOLControls

open HOL.UniformListInduction
open FormationSensitiveHOLInterface FormationSensitiveHOLUniformList
open SharedJudgmentServices.SubstitutionExamples
open SharedJudgmentPolarizedServices.Controls

def extendedContext : Tower.Ctx 2 := .snoc mappingContext NativeWireData.dataType
def weakenTarget : Sub Tower.Head 1 2 := renSub wk

theorem extendedContext_formed : FormationSensitive.ContextFormation common.rules extendedContext :=
  .snoc functionSquare_admitted.context
    (HOLNativeRelatorCompatibility.wire_typing (NativeWireData.dataType_formed _)) (.sort Tower.zero)

theorem weakenTarget_typed :
    FormationSensitive.CtxMor common.rules mappingContext extendedContext weakenTarget := by
  intro index
  simpa only [weakenTarget, extendedContext, renSub, subst_renSub, rename] using
    (FormationSensitive.Typing.var (R := common.rules) (Γ := mappingContext) index).weaken
      (extension := NativeWireData.dataType)

def liftedSquare : Tower.Tm 2 := .lam (.app (.var 2) (.app (.var 2) (.var 0)))

/-- The free function crosses both the target extension and its own lambda
binder. It is not captured by the new Data variable. -/
theorem lifted_argument : subst weakenTarget functionSquare = liftedSquare := rfl

theorem lifted_argument_not_captured :
    liftedSquare ≠ (.lam (.app (.var 1) (.app (.var 1) (.var 0))) : Tower.Tm 2) := by decide

def liftedRequest : Request 2 :=
  .hol [mapping] (UniformListChartNIKService.actualRequest [mapping]) (fun _ => liftedSquare)

def liftedResponse : Response liftedRequest :=
  .holProof (UniformListChartNIKService.actualNativeProof [mapping]) rawMapLength

theorem actual_invocation :
    invocation? common holOperation functionSquare =
      some ⟨Request.hol [mapping] (UniformListChartNIKService.actualRequest [mapping]) squareSubstitution,
        Response.holProof (UniformListChartNIKService.actualNativeProof [mapping]) rawMapLength⟩ :=
  (invocation_iff _ _ _ _ _).mpr ⟨hol_submission,
    .holSuccess (UniformListChartNIKService.actual_produced [mapping])
      (mapLength_represented [mapping])⟩

/-- The complete indexed request/response crosses from native scope one to
two, while source HOL premises and certificates remain unchanged. -/
theorem lifted_invocation :
    invocation? common (reindexOperation weakenTarget holOperation) (subst weakenTarget functionSquare) =
      some ⟨liftedRequest, liftedResponse⟩ := by
  rw [invocation_reindex common weakenTarget (operation := holOperation) (argument := functionSquare)
    (.hol _ _ _ _), actual_invocation]
  rfl

theorem lifted_callback :
    primitive common (reindexOperation weakenTarget holOperation) liftedSquare =
      .value (subst weakenTarget holPayload) := by
  rw [← lifted_argument, primitive_reindex common weakenTarget
    (operation := holOperation) (argument := functionSquare) (.hol _ _ _ _), hol_callback]
  rfl

theorem lifted_environment_and_result_admitted :
    EnvironmentAdmitted common extendedContext liftedRequest ∧
      FormationSensitive.Judgment common.rules extendedContext liftedSquare (typeAt types 2 mapping) ∧
      FormationSensitive.Judgment common.rules extendedContext
        (subst weakenTarget holPayload) (.const `HOLUniformList.prop) := by
  have result := reindexed_callback_admitted common_qualified weakenTarget
    extendedContext_formed weakenTarget_typed (.hol _ _ _ _) functionSquare_admitted
    (request := .hol [mapping] (UniformListChartNIKService.actualRequest [mapping]) squareSubstitution)
    (response := .holProof (UniformListChartNIKService.actualNativeProof [mapping]) rawMapLength)
    (value := holPayload) (type := .const `HOLUniformList.prop)
    substituted_request_admitted actual_invocation rfl
  refine ⟨result.2.2.1, ?_, result.2.2.2.2⟩
  simpa only [lifted_argument, typeAt_subst] using result.2.2.2.1

theorem altered_premises_remain_residual :
    primitive common (reindexOperation weakenTarget alteredHOL) liftedSquare =
      .retryableFault (.domain (.noPayload
        (.hol [mapping] (SharedJudgmentAssemblyServices.HOLCallbackControls.changedPremises [mapping])
          (fun _ => liftedSquare)) (.declined _))) := by
  rw [← lifted_argument, primitive_reindex common weakenTarget
    (operation := alteredHOL) (argument := functionSquare) (.hol _ _ _ _), altered_hol_residual]
  rfl

end HOLControls

#print axioms invocation_reindex
#print axioms primitive_reindex
#print axioms reindexed_callback_admitted
#print axioms WireControls.formed_substitution_is_not_sufficient
#print axioms HOLControls.lifted_environment_and_result_admitted

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceNaturality
