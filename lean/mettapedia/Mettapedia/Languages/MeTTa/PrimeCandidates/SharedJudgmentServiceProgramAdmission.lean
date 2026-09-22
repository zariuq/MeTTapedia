import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServicePrograms

/-!
# Native admission through repeated judgment-service calls

Admission is stated independently of the authored program's direct worlds
and resumption interpreter. Native leaves use the existing formed computation
judgment. Request leaves retain an independently formed environment and an
explicit contract on the type of every actual successful response. That
contract does not assert that the service succeeds.

Ordinary sequencing requires a result type independent of the bound value.
Dependent sequencing retains the selected value in a native Sigma pair.
Only value outcomes are native inhabitants; stopped request/reply data remain
observable without licensing a native term. This is preservation for the
displayed scoped syntax, not normalization, a full CBPV calculus, or a model
of arbitrary native terms.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServicePrograms

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation SharedJudgmentFragment SharedJudgmentServices
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.GSLT.Dynamics.ServiceResumption

variable {n m : Nat} {assembly : Assembly}

/-- Independent source admission. The request constructor displays its full
universal successful-response premise: neither status nor an accepted subtype
is used as a substitute for this actual invocation/payload contract. -/
inductive Admission (assembly : Assembly) :
    {n : Nat} → Tower.Ctx n → Code n → Tower.Tm n → Prop where
  | native {n : Nat} {context : Tower.Ctx n} {body : NativeCode n} {type : Tower.Tm n}
      (admitted : ScopedComputation.Judgment assembly.rules
        ScopedComputation.NativeExamples.signature context body type) :
      Admission assembly context (.native body) type
  | request {n : Nat} {context : Tower.Ctx n} {input : Request n}
      {type : Tower.Tm n} {universeHead : Tower.Head}
      (environment : EnvironmentAdmitted assembly context input)
      (formed : FormationSensitive.Typing assembly.rules context type (.head universeHead))
      (isUniverse : assembly.rules.isUniverse universeHead)
      (successfulType : ∀ (response : Response input) (payload actualType : Tower.Tm n),
        Invocation assembly input response →
        response.nativePayload? = some (payload, actualType) → actualType = type) :
      Admission assembly context (.request input) type
  | sequence {n : Nat} {context : Tower.Ctx n} {first : Code n} {body : Code (n + 1)}
      {firstType resultType : Tower.Tm n} {firstUniverse resultUniverse : Tower.Head}
      (firstFormed : FormationSensitive.Typing assembly.rules context firstType (.head firstUniverse))
      (firstIsUniverse : assembly.rules.isUniverse firstUniverse)
      (resultFormed : FormationSensitive.Typing assembly.rules context resultType (.head resultUniverse))
      (resultIsUniverse : assembly.rules.isUniverse resultUniverse)
      (firstAdmitted : Admission assembly context first firstType)
      (bodyAdmitted : Admission assembly (.snoc context firstType) body (rename wk resultType)) :
      Admission assembly context (.sequence first body) resultType
  | sequenceSigma {n : Nat} {context : Tower.Ctx n} {first : Code n} {body : Code (n + 1)}
      {firstType : Tower.Tm n} {family : Tower.Tm (n + 1)} {universeHead : Tower.Head}
      (formed : FormationSensitive.Typing assembly.rules context
        (.sigma firstType family) (.head universeHead))
      (isUniverse : assembly.rules.isUniverse universeHead)
      (firstAdmitted : Admission assembly context first firstType)
      (bodyAdmitted : Admission assembly (.snoc context firstType) body family) :
      Admission assembly context (.sequenceSigma first body) (.sigma firstType family)
  | choose {n : Nat} {context : Tower.Ctx n} {left right : Code n} {type : Tower.Tm n}
      (leftAdmitted : Admission assembly context left type)
      (rightAdmitted : Admission assembly context right type) :
      Admission assembly context (.choose left right) type

namespace Admission

theorem context_formed {context : Tower.Ctx n} {code : Code n} {type : Tower.Tm n}
    (admitted : Admission assembly context code type) :
    FormationSensitive.ContextFormation assembly.rules context := by
  induction admitted with
  | native judgment => exact judgment.context
  | @request _ _ input _ _ environment _ _ _ =>
      cases input with
      | matching _ _ => exact environment
      | hol _ _ _ => exact environment.1
  | sequence _ _ _ _ _ _ firstIH _ => exact firstIH
  | sequenceSigma _ _ _ _ firstIH _ => exact firstIH
  | choose _ _ leftIH _ => exact leftIH

/-- Every successful HOL response returns a proposition representation. The
intrinsic HOL proof object is not returned as a dependent native inhabitant. -/
theorem hol_payload_type
    {gamma : Mettapedia.Logic.HOL.Ctx Mettapedia.Logic.HOL.UniformListInduction.BaseSort}
    {replay : UniformListChartNIKService.ReplayRequest gamma}
    {environment : Sub Tower.Head gamma.length n}
    (response : Response (.hol gamma replay environment)) (payload actualType : Tower.Tm n)
    (_crossing : Invocation assembly (.hol gamma replay environment) response)
    (returned : response.nativePayload? = some (payload, actualType)) :
    actualType = .const `HOLUniformList.prop := by
  cases response with
  | declined _ => cases returned
  | holProof proof represented => exact (Prod.mk.inj (Option.some.inj returned)).2.symm
  | representationFailure proof => cases returned

/-- The actual fixed matching return determines every successful response
at this exact request and wire. It does not replace request validation by a
bare proposition annotation. -/
theorem matching_payload_type
    {expected : PolarizedNeedMatchedIndex.Request} {input : NativeWireData.Wire}
    {source proposition : Tower.Tm 0}
    (actual : assembly.reconstructMatch expected input = some (source, proposition))
    (response : Response (Request.matching (n := n) expected input))
    (payload actualType : Tower.Tm n)
    (crossing : Invocation assembly (.matching expected input) response)
    (returned : response.nativePayload? = some (payload, actualType)) :
    actualType = liftClosed proposition := by
  cases crossing with
  | matchingSuccess observed =>
      have same := Option.some.inj (actual.symm.trans observed)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      exact (Prod.mk.inj (Option.some.inj returned)).2.symm
  | matchingDecline _ => cases returned

theorem hol_request {context : Tower.Ctx n}
    {gamma : Mettapedia.Logic.HOL.Ctx Mettapedia.Logic.HOL.UniformListInduction.BaseSort}
    {replay : UniformListChartNIKService.ReplayRequest gamma}
    {environment : Sub Tower.Head gamma.length n} {universeHead : Tower.Head}
    (admitted : EnvironmentAdmitted assembly context (.hol gamma replay environment))
    (formed : FormationSensitive.Typing assembly.rules context
      (.const `HOLUniformList.prop) (.head universeHead))
    (isUniverse : assembly.rules.isUniverse universeHead) :
    Admission assembly context (.request (.hol gamma replay environment))
      (.const `HOLUniformList.prop) :=
  .request admitted formed isUniverse hol_payload_type

theorem matching_request {context : Tower.Ctx n}
    {expected : PolarizedNeedMatchedIndex.Request} {input : NativeWireData.Wire}
    {source proposition : Tower.Tm 0} {universeHead : Tower.Head}
    (actual : assembly.reconstructMatch expected input = some (source, proposition))
    (contextFormed : FormationSensitive.ContextFormation assembly.rules context)
    (formed : FormationSensitive.Typing assembly.rules context
      (liftClosed proposition) (.head universeHead))
    (isUniverse : assembly.rules.isUniverse universeHead) :
    Admission assembly context (.request (.matching expected input)) (liftClosed proposition) :=
  .request contextFormed formed isUniverse (matching_payload_type actual)

/-- A known actual invocation discharges the universal response-type premise
by invocation determinism. Formation is still an independent argument. -/
theorem request_of_returned {context : Tower.Ctx n} {input : Request n}
    {payload type : Tower.Tm n} {universeHead : Tower.Head}
    (environment : EnvironmentAdmitted assembly context input)
    (formed : FormationSensitive.Typing assembly.rules context type (.head universeHead))
    (isUniverse : assembly.rules.isUniverse universeHead)
    (actual : (invoke assembly input).nativePayload? = some (payload, type)) :
    Admission assembly context (.request input) type := by
  refine .request environment formed isUniverse ?_
  intro response value actualType crossing returned
  rw [(invoke_iff _ _ _).mpr crossing] at actual
  exact (Prod.mk.inj (Option.some.inj (returned.symm.trans actual))).2

private theorem request_worlds_preserve
    (qualified : specification.Satisfies assembly)
    {context : Tower.Ctx n} {targetContext : Tower.Ctx m}
    {input : Request n} {type : Tower.Tm n} {environment : Sub Tower.Head n m}
    (inputAdmitted : EnvironmentAdmitted assembly context input)
    (successfulType : ∀ (response : Response input) (payload actualType : Tower.Tm n),
      Invocation assembly input response →
      response.nativePayload? = some (payload, actualType) → actualType = type)
    (target : FormationSensitive.ContextFormation assembly.rules targetContext)
    (typed : FormationSensitive.CtxMor assembly.rules context targetContext environment)
    {state : Bool} {branch : BranchTrace}
    {output : Result (Request m) (@Response m) Bool (Outcome m) Nat} {value : Tower.Tm m}
    (observed : output ∈ Code.worlds assembly environment (.request input) state branch)
    (isValue : output.world.answer = .value value) :
    FormationSensitive.Judgment assembly.rules targetContext value (subst environment type) := by
  simp only [Code.worlds, ← invoke_substitute, Response.nativePayload_substitute] at observed
  cases returned : (invoke assembly input).nativePayload? with
  | none =>
      simp only [returned, Option.map_none, List.mem_singleton] at observed
      subst output
      cases isValue
  | some payload =>
      simp only [returned, Option.map_some, List.mem_singleton] at observed
      subst output
      have same := Outcome.value.inj isValue
      subst value
      have admitted := invoked_payload_admitted qualified inputAdmitted
        (invoke_crossing assembly input) returned
      rw [successfulType _ _ _ (invoke_crossing assembly input) returned] at admitted
      exact admitted.substitute target typed

/-- Arbitrary composed source admission is preserved by the independently
recursive world semantics after an actual refined native environment. A
stopped outcome cannot discharge the explicit value-equality premise. -/
theorem worlds_preserve
    (qualified : specification.Satisfies assembly)
    {context : Tower.Ctx n} {code : Code n} {type : Tower.Tm n}
    (admitted : Admission assembly context code type) :
    ∀ {m : Nat} {targetContext : Tower.Ctx m} {environment : Sub Tower.Head n m}
      {state : Bool} {branch : BranchTrace}
      {output : Result (Request m) (@Response m) Bool (Outcome m) Nat} {value : Tower.Tm m},
      FormationSensitive.ContextFormation assembly.rules targetContext →
      FormationSensitive.CtxMor assembly.rules context targetContext environment →
      output ∈ Code.worlds assembly environment code state branch →
      output.world.answer = .value value →
      FormationSensitive.Judgment assembly.rules targetContext value (subst environment type) := by
  induction admitted with
  | native judgment =>
      intro m targetContext environment state branch output value target typed observed isValue
      obtain ⟨prior, priorMem, rfl⟩ := List.mem_map.mp observed
      have same := Outcome.value.inj isValue
      subst value
      apply qualified_execution (qualified .execution (by simp [specification])) judgment target typed
      rw [ScopedComputation.ImplementationStudy.qualified_worlds
        (assembly.execution m) ((qualified .execution (by simp [specification])) m)]
      exact priorMem
  | request inputAdmitted _ _ successfulType =>
      intro m targetContext environment state branch output value target typed observed isValue
      exact request_worlds_preserve qualified inputAdmitted successfulType target typed observed isValue
  | sequence _ _ _ _ _ _ firstIH bodyIH =>
      intro m targetContext environment state branch output value target typed observed isValue
      obtain ⟨prior, priorMem, suffixMem⟩ := List.mem_flatMap.mp observed
      cases priorOutcome : prior.world.answer with
      | value firstValue =>
          rw [priorOutcome] at suffixMem
          obtain ⟨later, laterMem, rfl⟩ := List.mem_map.mp suffixMem
          have firstTyped := firstIH target typed priorMem priorOutcome
          have laterTyped := bodyIH target
            (ScopedComputation.extendEnvironment typed firstTyped.typing) laterMem isValue
          simpa only [subst_consSub_rename_wk] using laterTyped
      | stopped reply =>
          rw [priorOutcome] at suffixMem
          have same := List.mem_singleton.mp suffixMem
          subst output
          rw [priorOutcome] at isValue
          cases isValue
  | sequenceSigma formed isUniverse _ _ firstIH bodyIH =>
      intro m targetContext environment state branch output value target typed observed isValue
      obtain ⟨prior, priorMem, suffixMem⟩ := List.mem_flatMap.mp observed
      cases priorOutcome : prior.world.answer with
      | value firstValue =>
          rw [priorOutcome] at suffixMem
          obtain ⟨later, laterMem, rfl⟩ := List.mem_map.mp suffixMem
          cases laterOutcome : later.world.answer with
          | value laterValue =>
              simp only [Result.prepend, Result.mapAnswer,
                Mettapedia.TypeTheory.ContextualDependentSequencing.WorldResult.mapAnswer,
                laterOutcome, Outcome.map] at isValue
              have same := Outcome.value.inj isValue
              subst value
              have firstTyped := firstIH target typed priorMem priorOutcome
              have laterTyped := bodyIH target
                (ScopedComputation.extendEnvironment typed firstTyped.typing) laterMem laterOutcome
              refine ⟨target, FormationSensitive.Typing.pairIntro
                (formed.substitute typed) isUniverse firstTyped.typing ?_⟩
              simpa only [subst_consSub] using laterTyped.typing
          | stopped reply =>
              simp only [Result.prepend, Result.mapAnswer,
                Mettapedia.TypeTheory.ContextualDependentSequencing.WorldResult.mapAnswer,
                laterOutcome, Outcome.map] at isValue
              cases isValue
      | stopped reply =>
          rw [priorOutcome] at suffixMem
          have same := List.mem_singleton.mp suffixMem
          subst output
          rw [priorOutcome] at isValue
          cases isValue
  | choose _ _ leftIH rightIH =>
      intro m targetContext environment state branch output value target typed observed isValue
      rcases List.mem_append.mp observed with left | right
      · exact leftIH target typed left isValue
      · exact rightIH target typed right isValue

/-- Exact interpretation transports the general source-world theorem to the
actual request-indexed resumption run without dropping stopped replies. -/
theorem run_preserve
    (qualified : specification.Satisfies assembly)
    {context : Tower.Ctx n} {targetContext : Tower.Ctx m} {code : Code n} {type : Tower.Tm n}
    (admitted : Admission assembly context code type) {environment : Sub Tower.Head n m}
    (target : FormationSensitive.ContextFormation assembly.rules targetContext)
    (typed : FormationSensitive.CtxMor assembly.rules context targetContext environment)
    {state : Bool} {branch : BranchTrace}
    {output : Result (Request m) (@Response m) Bool (Outcome m) Nat} {value : Tower.Tm m}
    (observed : output ∈ Code.run assembly environment code state branch)
    (isValue : output.world.answer = .value value) :
    FormationSensitive.Judgment assembly.rules targetContext value (subst environment type) := by
  rw [Code.interpret_worlds assembly (qualified .execution (by simp [specification]))] at observed
  exact admitted.worlds_preserve qualified target typed observed isValue

end Admission

namespace AdmissionExamples

open ScopedComputation.NativeExamples

private theorem proposition_formed {n : Nat} (context : Tower.Ctx n) :
    FormationSensitive.Typing common.rules context (.const `HOLUniformList.prop) (sortTm Tower.zero) :=
  HOLNativeRelatorCompatibility.hol_typing
    (FormationSensitiveHOLUniformList.proposition_formed context)

private theorem matching_type_formed {n : Nat} (context : Tower.Ctx n) :
    FormationSensitive.Typing common.rules context (Examples.matchingType n) (sortTm Tower.zero) := by
  have closed : FormationSensitive.Typing common.rules .nil
      SharedJudgmentServices.Examples.canonicalTransport.proposition (sortTm Tower.zero) :=
    HOLNativeRelatorCompatibility.wire_relator_typing
      (.idForm (NativeWireRelatorCompatibility.dataType_formed .nil) (.sort Tower.zero)
        (MatchedIndexDependentTransport.nativePattern_typed .nil _)
        (MatchedIndexDependentTransport.nativePattern_typed .nil _))
  exact closed.renameTyping (fun index => Fin.elim0 index)

private theorem initial_context_formed :
    FormationSensitive.ContextFormation common.rules context :=
  OpaqueRelatorScopedComputation.context_formed common.declarations

def matchingContext : Tower.Ctx 3 := .snoc context (Examples.matchingType 2)

def holContext : Tower.Ctx 4 := .snoc matchingContext (.const `HOLUniformList.prop)

private theorem matching_context_formed :
    FormationSensitive.ContextFormation common.rules matchingContext :=
  .snoc initial_context_formed (matching_type_formed context) (.sort Tower.zero)

private theorem hol_context_formed :
    FormationSensitive.ContextFormation common.rules holContext :=
  .snoc matching_context_formed (proposition_formed matchingContext) (.sort Tower.zero)

private theorem matching_request_admitted :
    Admission common context (.request (Examples.matchingRequest 2)) (Examples.matchingType 2) :=
  Admission.request_of_returned initial_context_formed (matching_type_formed context)
    (.sort Tower.zero) (Examples.matching_returned 2)

private theorem hol_request_admitted
    (replay : UniformListChartNIKService.ReplayRequest []) :
    Admission common matchingContext (.request (.hol [] replay Fin.elim0))
      (.const `HOLUniformList.prop) :=
  Admission.hol_request ⟨matching_context_formed, fun index => Fin.elim0 index⟩
    (proposition_formed matchingContext) (.sort Tower.zero)

def pairType (n : Nat) : Tower.Tm n :=
  .sigma (Examples.matchingType n) (.const `HOLUniformList.prop)

private theorem pair_type_formed {n : Nat} (context : Tower.Ctx n) :
    FormationSensitive.Typing common.rules context (pairType n)
      (sortTm (.max Tower.zero Tower.zero)) :=
  .sigmaForm (matching_type_formed context) (.sort Tower.zero)
    (proposition_formed _) (.sort Tower.zero) (.sorts Tower.zero Tower.zero)

private theorem pair_type_rename {n m : Nat} (rho : Ren n m) :
    rename rho (pairType n) = pairType m := by
  simp only [pairType, rename, Examples.matchingType, rename_liftClosed]

private theorem pair_body_admitted :
    Admission common holContext (.native (.returnValue (.pair (.var 1) (.var 0)))) (pairType 4) := by
  refine .native ⟨hol_context_formed, .returnValue ?_⟩
  apply FormationSensitive.Typing.pairIntro (pair_type_formed holContext)
    (.sort (.max Tower.zero Tower.zero))
  · have selected := FormationSensitive.Typing.var (R := common.rules) (Γ := holContext)
      (Fin.succ (0 : Fin 3))
    simp only [holContext, matchingContext, Ctx.lookup_snoc_succ, Ctx.lookup_snoc_zero,
      Examples.matchingType, rename_liftClosed] at selected
    simpa only [holContext, matchingContext, Examples.matchingType,
      Fin.succ_zero_eq_one'] using selected
  · simpa only [inst0, subst, holContext, Ctx.lookup_snoc_zero, rename] using
      (FormationSensitive.Typing.var (R := common.rules) (Γ := holContext) 0)

private theorem two_requests_admitted (replay : UniformListChartNIKService.ReplayRequest []) :
    Admission common context
      (.sequence (.request (Examples.matchingRequest 2))
        (.sequence (.request (.hol [] replay Fin.elim0))
          (.native (.returnValue (.pair (.var 1) (.var 0)))))) (pairType 2) := by
  apply Admission.sequence (matching_type_formed context) (.sort Tower.zero)
    (pair_type_formed context) (.sort (.max Tower.zero Tower.zero)) matching_request_admitted
  rw [pair_type_rename]
  apply Admission.sequence (proposition_formed matchingContext) (.sort Tower.zero)
    (pair_type_formed matchingContext) (.sort (.max Tower.zero Tower.zero)) (hol_request_admitted replay)
  rw [pair_type_rename]
  exact pair_body_admitted

/-- Independently type the actual ordinary two-call source already executed
by the shared program module, retaining both returned native variables. -/
theorem matching_then_hol_admitted :
    Admission common context Examples.matchingThenHOL (pairType 2) :=
  two_requests_admitted (UniformListChartNIKService.actualRequest [])

/-- Admission of a request does not claim that its submitted proof succeeds.
This source has the same continuation type but a declined second request. -/
theorem matching_then_changed_hol_admitted :
    Admission common context Examples.matchingThenChangedHOL (pairType 2) :=
  two_requests_admitted { UniformListChartNIKService.actualRequest [] with
    claim := (Mettapedia.Logic.HOL.UniformListInduction.equations,
      Mettapedia.Logic.HOL.UniformListInduction.mapLength) }

private theorem identity_environment : FormationSensitive.CtxMor common.rules context context ids := by
  intro index
  simpa only [ids, subst_ids] using
    (FormationSensitive.Typing.var (R := common.rules) (Γ := context) index)

theorem matching_then_hol_result_admitted :
    FormationSensitive.Judgment common.rules context
      (.pair (Examples.matchingValue 2) (Examples.holValue 2)) (pairType 2) := by
  have result := matching_then_hol_admitted.run_preserve common_qualified initial_context_formed
    identity_environment (state := false) (branch := [])
    (output := ⟨⟨[], .value (.pair (Examples.matchingValue 2) (Examples.holValue 2)), false, []⟩,
      [⟨Examples.matchingRequest 2, invoke common (Examples.matchingRequest 2)⟩,
        ⟨Examples.holRequest 2, invoke common (Examples.holRequest 2)⟩]⟩)
    (by rw [Examples.matching_then_hol_worlds]; exact List.mem_singleton_self _) rfl
  simpa only [subst_ids] using result

/-- Retain both selected service values, then construct native reflexivity
at the actual HOL representation under the innermost success binder. -/
def matchingThenHOLIdentity : Code 2 :=
  .sequenceSigma (.request (Examples.matchingRequest 2))
    (.sequenceSigma (.request (Examples.holRequest 3))
      (.native (.returnValue (.refl (.var 0)))))

def holIdentityType (n : Nat) : Tower.Tm n :=
  .sigma (.const `HOLUniformList.prop) (.id (.const `HOLUniformList.prop) (.var 0) (.var 0))

def nestedType : Tower.Tm 2 := .sigma (Examples.matchingType 2) (holIdentityType 3)

private theorem hol_identity_type_formed {n : Nat} (context : Tower.Ctx n) :
    FormationSensitive.Typing common.rules context (holIdentityType n)
      (sortTm (.max Tower.zero Tower.zero)) := by
  apply FormationSensitive.Typing.sigmaForm (proposition_formed context) (.sort Tower.zero)
    _ (.sort Tower.zero) (.sorts Tower.zero Tower.zero)
  apply FormationSensitive.Typing.idForm (proposition_formed _) (.sort Tower.zero)
  all_goals simpa only [Ctx.lookup_snoc_zero, rename] using
    (FormationSensitive.Typing.var (R := common.rules)
      (Γ := .snoc context (.const `HOLUniformList.prop)) 0)

theorem nested_admitted : Admission common context matchingThenHOLIdentity nestedType := by
  apply Admission.sequenceSigma
    (FormationSensitive.Typing.sigmaForm (matching_type_formed context) (.sort Tower.zero)
      (hol_identity_type_formed matchingContext) (.sort (.max Tower.zero Tower.zero))
      (.sorts Tower.zero (.max Tower.zero Tower.zero)))
    (.sort (.max Tower.zero (.max Tower.zero Tower.zero))) matching_request_admitted
  apply Admission.sequenceSigma (hol_identity_type_formed matchingContext)
    (.sort (.max Tower.zero Tower.zero)) (hol_request_admitted (UniformListChartNIKService.actualRequest []))
  refine .native ⟨hol_context_formed, .returnValue (.reflIntro ?_)⟩
  simpa only [holContext, Ctx.lookup_snoc_zero, rename] using
    (FormationSensitive.Typing.var (R := common.rules) (Γ := holContext) 0)

def nestedValue : Tower.Tm 2 :=
  .pair (Examples.matchingValue 2)
    (.pair (Examples.holValue 2) (.refl (Examples.holValue 2)))

theorem nested_worlds (state : Bool) (branch : BranchTrace) :
    Code.run common ids matchingThenHOLIdentity state branch =
      [⟨⟨branch, .value nestedValue, state, []⟩,
        [⟨Examples.matchingRequest 2, invoke common (Examples.matchingRequest 2)⟩,
          ⟨Examples.holRequest 2, invoke common (Examples.holRequest 2)⟩]⟩] := by
  rw [Code.interpret_worlds common common_execution]
  have requestSame := Examples.holRequest_substitute
    (consSub (Examples.matchingValue 2) (ids (Head := Tower.Head)))
  have secondReturned :=
    (congrArg (fun input : Request 2 => (invoke common input).nativePayload?) requestSame).trans
      (Examples.hol_returned 2)
  have replySame := congrArg (fun input : Request 2 =>
    (⟨input, invoke common input⟩ : Sigma (@Response 2))) requestSame
  simp only [matchingThenHOLIdentity, Code.worlds, Examples.matchingRequest_substitute,
    Examples.matching_returned, secondReturned, replySame,
    ScopedComputation.Code.worlds, subst, consSub_zero,
    List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.append_nil,
    Result.prepend, Result.mapAnswer, Outcome.map,
    Mettapedia.TypeTheory.ContextualDependentSequencing.WorldResult.mapAnswer, nestedValue]
  rfl

theorem nested_result_admitted :
    FormationSensitive.Judgment common.rules context nestedValue nestedType := by
  have result := nested_admitted.run_preserve common_qualified initial_context_formed
    identity_environment (state := false) (branch := [])
    (output := ⟨⟨[], .value nestedValue, false, []⟩,
      [⟨Examples.matchingRequest 2, invoke common (Examples.matchingRequest 2)⟩,
        ⟨Examples.holRequest 2, invoke common (Examples.holRequest 2)⟩]⟩)
    (by rw [nested_worlds]; exact List.mem_singleton_self _) rfl
  simpa only [subst_ids] using result

/-- Even an admitted program need not return a native inhabitant: the actual
second request declines and the native continuation is not run. -/
theorem stopped_has_no_value (state : Bool) (branch : BranchTrace)
    {output : Result (Request 2) (@Response 2) Bool (Outcome 2) Nat} {value : Tower.Tm 2}
    (observed : output ∈ Code.run common ids Examples.matchingThenChangedHOL state branch) :
    output.world.answer ≠ .value value := by
  rw [Examples.matching_then_changed_hol_stops] at observed
  have same := List.mem_singleton.mp observed
  subst output
  intro impossible
  cases impossible

/-- The actual declined source is independently admitted and has a nonempty
stopped run, but no native value outcome. Preservation is not progress. -/
theorem admitted_program_can_stop (state : Bool) (branch : BranchTrace) :
    Admission common context Examples.matchingThenChangedHOL (pairType 2) ∧
    Code.run common ids Examples.matchingThenChangedHOL state branch ≠ [] ∧
    ∀ output ∈ Code.run common ids Examples.matchingThenChangedHOL state branch,
      ¬ ∃ value, output.world.answer = .value value :=
  ⟨matching_then_changed_hol_admitted, Examples.stopped_run_nonempty_without_value state branch⟩

end AdmissionExamples

#print axioms Admission.worlds_preserve
#print axioms Admission.run_preserve
#print axioms AdmissionExamples.matching_then_hol_admitted
#print axioms AdmissionExamples.matching_then_hol_result_admitted
#print axioms AdmissionExamples.nested_admitted
#print axioms AdmissionExamples.nested_worlds
#print axioms AdmissionExamples.nested_result_admitted
#print axioms AdmissionExamples.matching_then_changed_hol_admitted
#print axioms AdmissionExamples.stopped_has_no_value
#print axioms AdmissionExamples.admitted_program_can_stop

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServicePrograms
