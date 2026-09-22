import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServices

/-!
# Capture-safe substitution through shared service requests

Matching requests contain closed data. A HOL request retains its source
claim, ordered premises and submitted certificates while composing its native
environment with the ambient substitution. Responses retain the actual
source proof or matching reconstruction at that same request index.

The native continuation is substituted under its success binder. Its
interpretation law uses one target handler and the existing scoped-code
substitution theorem; it assumes no naturality between handlers at different
scopes. Request formation and result admission remain independent judgments.
This module does not add recursive service composition or a raw proof codec.
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

variable {n m k : Nat}

namespace Request

/-- Substitute native inputs without changing the submitted source claim or
certificates. The source HOL context is not the ambient native context. -/
def substitute (substitution : Sub Tower.Head n m) : Request n → Request m
  | .matching expected input => .matching expected input
  | .hol gamma replay environment =>
      .hol gamma replay (subComp substitution environment)

@[simp] theorem substitute_matching (substitution : Sub Tower.Head n m)
    (expected : PolarizedNeedMatchedIndex.Request) (input : NativeWireData.Wire) :
    (Request.matching expected input).substitute substitution =
      Request.matching expected input := rfl

@[simp] theorem substitute_hol (substitution : Sub Tower.Head n m)
    (gamma : Mettapedia.Logic.HOL.Ctx Mettapedia.Logic.HOL.UniformListInduction.BaseSort)
    (replay : UniformListChartNIKService.ReplayRequest gamma)
    (environment : Sub Tower.Head gamma.length n) :
    (Request.hol gamma replay environment).substitute substitution =
      Request.hol gamma replay (subComp substitution environment) := rfl

@[simp] theorem substitute_ids (request : Request n) :
    request.substitute ids = request := by
  cases request <;> simp only [substitute, subComp_ids_left]

@[simp] theorem substitute_comp (later : Sub Tower.Head m k)
    (earlier : Sub Tower.Head n m) (request : Request n) :
    (request.substitute earlier).substitute later =
      request.substitute (subComp later earlier) := by
  cases request <;> simp only [substitute, subComp_assoc]

end Request

namespace Response

/-- Transport the request index, retaining every returned data field and the
already intrinsic HOL proof object. This performs no new service invocation. -/
def substitute (substitution : Sub Tower.Head n m) {request : Request n} :
    Response request → Response (request.substitute substitution)
  | .declined request => .declined (request.substitute substitution)
  | .matched source proposition => .matched source proposition
  | .holProof proof represented => .holProof proof represented
  | .representationFailure proof => .representationFailure proof

/-- Identity retains the full dependent request-response pair. -/
@[simp] theorem substitute_ids {request : Request n} (response : Response request) :
    (⟨request.substitute ids, response.substitute ids⟩ : Sigma (@Response n)) =
      ⟨request, response⟩ := by
  cases response with
  | declined request =>
      exact congrArg
        (fun request => (⟨request, Response.declined request⟩ : Sigma (@Response n)))
        request.substitute_ids
  | matched source proposition => rfl
  | @holProof gamma replay environment proof represented =>
      exact congrArg
        (fun environment => (⟨Request.hol gamma replay environment,
          Response.holProof proof represented⟩ : Sigma (@Response n)))
        (subComp_ids_left environment)
  | @representationFailure gamma replay environment proof =>
      exact congrArg
        (fun environment => (⟨Request.hol gamma replay environment,
          Response.representationFailure proof⟩ : Sigma (@Response n)))
        (subComp_ids_left environment)

/-- Composition retains the same request and response, including proof and
representation fields; equality is taken in their dependent sum. -/
@[simp] theorem substitute_comp (later : Sub Tower.Head m k)
    (earlier : Sub Tower.Head n m) {request : Request n} (response : Response request) :
    (⟨(request.substitute earlier).substitute later,
      (response.substitute earlier).substitute later⟩ : Sigma (@Response k)) =
      ⟨request.substitute (subComp later earlier),
        response.substitute (subComp later earlier)⟩ := by
  cases response with
  | declined request =>
      exact congrArg
        (fun request => (⟨request, Response.declined request⟩ : Sigma (@Response k)))
        (request.substitute_comp later earlier)
  | matched source proposition => rfl
  | @holProof gamma replay environment proof represented =>
      exact congrArg
        (fun environment => (⟨Request.hol gamma replay environment,
          Response.holProof proof represented⟩ : Sigma (@Response k)))
        (subComp_assoc later earlier environment)
  | @representationFailure gamma replay environment proof =>
      exact congrArg
        (fun environment => (⟨Request.hol gamma replay environment,
          Response.representationFailure proof⟩ : Sigma (@Response k)))
        (subComp_assoc later earlier environment)

@[simp] theorem substitute_status (substitution : Sub Tower.Head n m)
    {request : Request n} (response : Response request) :
    (response.substitute substitution).status = response.status := by
  cases response <;> rfl

/-- The actual returned native value and its type follow the same ambient
substitution. No proof or representation is inferred from the Option tag. -/
theorem nativePayload_substitute (substitution : Sub Tower.Head n m)
    {request : Request n} (response : Response request) :
    (response.substitute substitution).nativePayload? =
      response.nativePayload?.map
        (fun payload => (subst substitution payload.1, subst substitution payload.2)) := by
  cases response <;>
    simp only [substitute, nativePayload?, Option.map_none, Option.map_some,
      subst_liftClosed, subst_subComp, subst]

end Response

namespace Invocation

/-- The five actual service crossings are preserved by native substitution.
Their submitted source claims, certificates and producer results are unchanged. -/
theorem substitute (substitution : Sub Tower.Head n m)
    {assembly : Assembly} {request : Request n} {response : Response request}
    (crossing : Invocation assembly request response) :
    Invocation assembly (request.substitute substitution) (response.substitute substitution) := by
  cases crossing with
  | matchingSuccess returned => exact .matchingSuccess returned
  | matchingDecline declined => exact .matchingDecline declined
  | holSuccess returned represented => exact .holSuccess returned represented
  | holDecline declined => exact .holDecline declined
  | holRepresentationFailure returned missing => exact .holRepresentationFailure returned missing

end Invocation

/-- Invocation commutes with the actual request substitution, for any raw
assembly. Semantic qualification is not needed for this operational equation. -/
theorem invoke_substitute (assembly : Assembly) (substitution : Sub Tower.Head n m)
    (request : Request n) :
    (invoke assembly request).substitute substitution =
      invoke assembly (request.substitute substitution) :=
  ((invoke_iff assembly _ _).mpr
    ((invoke_crossing assembly request).substitute substitution)).symm

namespace Source

/-- Lift once under the service-success binder, then let the existing Code
substitution lift again under each of its own binders. -/
def substitute (substitution : Sub Tower.Head n m) (source : Source n) : Source m where
  request := source.request.substitute substitution
  continuation := source.continuation.substitute (liftSub substitution)

@[simp] theorem substitute_request (substitution : Sub Tower.Head n m) (source : Source n) :
    (source.substitute substitution).request = source.request.substitute substitution := rfl

@[simp] theorem substitute_continuation (substitution : Sub Tower.Head n m) (source : Source n) :
    (source.substitute substitution).continuation =
      source.continuation.substitute (liftSub substitution) := rfl

@[simp] theorem substitute_ids (source : Source n) : source.substitute ids = source := by
  cases source
  simp only [substitute, Request.substitute_ids, liftSub_ids, Code.substitute_ids]

@[simp] theorem substitute_comp (later : Sub Tower.Head m k)
    (earlier : Sub Tower.Head n m) (source : Source n) :
    (source.substitute earlier).substitute later = source.substitute (subComp later earlier) := by
  cases source with
  | mk request body =>
      simp only [substitute, Request.substitute_comp, Code.substitute_comp]
      congr 2
      funext index
      exact liftSub_comp_apply later earlier index

end Source

namespace EnvironmentAdmitted

/-- Refined request environments compose componentwise using the existing
formation-sensitive substitution theorem, never through raw typing alone. -/
theorem substitute {assembly : Assembly} {context : Tower.Ctx n} {targetContext : Tower.Ctx m}
    {request : Request n} {substitution : Sub Tower.Head n m}
    (admitted : EnvironmentAdmitted assembly context request)
    (target : FormationSensitive.ContextFormation assembly.rules targetContext)
    (typed : FormationSensitive.CtxMor assembly.rules context targetContext substitution) :
    EnvironmentAdmitted assembly targetContext (request.substitute substitution) := by
  cases request with
  | matching expected input => exact target
  | hol gamma replay environment =>
      refine ⟨target, ?_⟩
      intro index
      change FormationSensitive.Typing assembly.rules targetContext
        (subst substitution (environment index))
        (subst (subComp substitution environment)
          (Ctx.lookup (FormationSensitiveHOLInterface.context
            FormationSensitiveHOLUniformList.types gamma) index))
      simpa only [subst_subComp] using (admitted.2 index).substitute typed

end EnvironmentAdmitted

/-- Substitute the authored body and then open its success binder. Both
sides use the same target handler; no cross-scope handler equation is assumed. -/
theorem continuationProgram_substitute (assembly : Assembly)
    (substitution : Sub Tower.Head n m) (source : Source n)
    (response : Response source.request) :
    continuationProgram assembly (source.substitute substitution) (response.substitute substitution) =
      response.nativePayload?.map fun payload =>
        Code.interpret (assembly.execution m).handler
          (consSub (subst substitution payload.1) substitution) source.continuation := by
  simp only [continuationProgram, Source.substitute, Response.nativePayload_substitute,
    Option.map_map]
  congr 1
  funext payload
  simp only [Function.comp_def, Code.interpret_substitute,
    Code.consSub_liftSub_comp, subComp_ids_left]

/-- Every result of the actual substituted request/body has the substituted
dependent result type. The source request and body are admitted separately. -/
theorem substituted_continuation_preserves
    {assembly : Assembly} (qualified : specification.Satisfies assembly)
    {context : Tower.Ctx n} {targetContext : Tower.Ctx m}
    {substitution : Sub Tower.Head n m} {source : Source n}
    {response : Response source.request} {payload type : Tower.Tm n}
    {resultType : Tower.Tm (n + 1)}
    (environment : EnvironmentAdmitted assembly context source.request)
    (target : FormationSensitive.ContextFormation assembly.rules targetContext)
    (typed : FormationSensitive.CtxMor assembly.rules context targetContext substitution)
    (crossing : Invocation assembly source.request response)
    (returned : response.nativePayload? = some (payload, type))
    (body : Judgment assembly.rules NativeExamples.signature (.snoc context type)
      source.continuation resultType)
    {program : Program Bool (Tower.Tm m) Nat}
    (selected : continuationProgram assembly (source.substitute substitution)
      (response.substitute substitution) = some program)
    {state : Bool} {branch : BranchTrace} {output : WorldResult Bool (Tower.Tm m) Nat}
    (observed : output ∈ runWorldsAt program state branch) :
    FormationSensitive.Judgment assembly.rules targetContext output.answer
      (subst substitution (inst0 payload resultType)) := by
  rw [continuationProgram_substitute, returned, Option.map_some] at selected
  cases selected
  have payloadAdmitted := invoked_payload_admitted qualified environment crossing returned
  have transported := payloadAdmitted.typing.substitute typed
  have extended := extendEnvironment typed transported
  have preserved := qualified_execution (qualified .execution (by simp [specification]))
    body target extended observed
  simpa only [subst_consSub, subst_inst0] using preserved

/-! ## A function-valued environment through the actual HOL service -/

namespace SubstitutionExamples

open Mettapedia.Logic HOL.UniformListInduction
open FormationSensitiveHOLInterface FormationSensitiveHOLUniformList

def mappingContext : Tower.Ctx 1 := context types [mapping]

/-- Replace the free function by its self-composition, not by a closed value
or an identity substitution. Its free occurrence must survive every binder. -/
def functionSquare : Tower.Tm 1 :=
  .lam (.app (.var 1) (.app (.var 1) (.var 0)))

def sourceFunctionSquare : Expr [mapping] mapping :=
  .lam (.app (.var (.vs .vz)) (.app (.var (.vs .vz)) (.var .vz)))

theorem functionSquare_represented :
    represent signature sourceFunctionSquare = some functionSquare := rfl

theorem functionSquare_admitted :
    FormationSensitive.Judgment common.rules mappingContext functionSquare
      (typeAt types 1 mapping) :=
  HOLNativeRelatorCompatibility.hol_judgment
    (represent_judgment signature sourceFunctionSquare functionSquare_represented)

def squareSubstitution : Sub Tower.Head 1 1 := fun _ => functionSquare

theorem squareSubstitution_typed :
    FormationSensitive.CtxMor common.rules mappingContext mappingContext squareSubstitution := by
  intro index
  have same : index = 0 := Fin.eq_zero index
  subst index
  change FormationSensitive.Typing common.rules mappingContext functionSquare
    (subst squareSubstitution (Ctx.lookup mappingContext 0))
  have lookup : Ctx.lookup mappingContext 0 = typeAt types 1 mapping :=
    context_lookup types (show HOL.Var [mapping] mapping from .vz)
  rw [lookup, typeAt_subst]
  exact functionSquare_admitted.typing

def request : Request 1 := .hol [mapping] (UniformListChartNIKService.actualRequest [mapping]) ids

def response : Response request :=
  .holProof (UniformListChartNIKService.actualNativeProof [mapping]) rawMapLength

theorem actual_crossing : Invocation common request response :=
  .holSuccess (UniformListChartNIKService.actual_produced [mapping])
    (mapLength_represented [mapping])

theorem request_admitted : EnvironmentAdmitted common mappingContext request := by
  refine ⟨functionSquare_admitted.context, ?_⟩
  change FormationSensitive.CtxMor common.rules mappingContext mappingContext ids
  intro index
  simpa only [ids, subst_ids] using
    (FormationSensitive.Typing.var (R := common.rules) (Γ := mappingContext) index)

theorem substituted_request_admitted :
    EnvironmentAdmitted common mappingContext (request.substitute squareSubstitution) :=
  request_admitted.substitute functionSquare_admitted.context squareSubstitution_typed

/-- Return both the actual represented theorem and a lambda using the free
function. The continuation contains the service-success and lambda binders. -/
def source : Source 1 where
  request := request
  continuation := .returnValue (.pair (.var 0) (.lam (.app (.var 2) (.var 0))))

def bodyType : Tower.Tm 2 :=
  .sigma (.const `HOLUniformList.prop) (typeAt types 3 mapping)

theorem body_admitted :
    Judgment common.rules NativeExamples.signature
      (.snoc mappingContext (.const `HOLUniformList.prop)) source.continuation bodyType := by
  have function : FormationSensitive.Judgment common.rules
      (.snoc mappingContext (.const `HOLUniformList.prop))
      (.lam (.app (.var 2) (.var 0))) (typeAt types 2 mapping) :=
    HOLNativeRelatorCompatibility.hol_judgment
    (represent_judgment signature
      (show Expr [.prop, mapping] mapping from .lam (.app (.var (.vs (.vs .vz))) (.var .vz)))
      (show represent signature
        (show Expr [.prop, mapping] mapping from .lam (.app (.var (.vs (.vs .vz))) (.var .vz))) =
          some (.lam (.app (.var 2) (.var 0))) from rfl))
  refine ⟨function.context, Typing.returnValue ?_⟩
  apply FormationSensitive.Typing.pairIntro (R := common.rules)
      (FormationSensitive.Typing.sigmaForm (R := common.rules)
        (HOLNativeRelatorCompatibility.hol_typing (proposition_formed _)) (.sort Tower.zero)
        (HOLNativeRelatorCompatibility.hol_typing (simple_type_formed mapping _))
        (.sort Tower.zero) (.sorts Tower.zero Tower.zero))
      (.sort (.max Tower.zero Tower.zero))
  · simpa only [Ctx.lookup_snoc_zero, Presentation.rename] using
      (FormationSensitive.Typing.var (R := common.rules)
        (Γ := .snoc mappingContext (.const `HOLUniformList.prop)) 0)
  · simpa only [inst0, typeAt_subst] using function.typing

/-- The inserted free function is index three inside all three binders:
service success, the authored lambda, and the replacement's lambda. -/
theorem substituted_body :
    (source.substitute squareSubstitution).continuation =
      .returnValue (.pair (.var 0)
        (.lam (.app (.lam (.app (.var 3) (.app (.var 3) (.var 0)))) (.var 0)))) := rfl

theorem substituted_actual_crossing :
    Invocation common (source.substitute squareSubstitution).request
      (response.substitute squareSubstitution) :=
  actual_crossing.substitute squareSubstitution

def originalResult : Tower.Tm 1 :=
  .pair rawMapLength (.lam (.app (.var 1) (.var 0)))

def substitutedResult : Tower.Tm 1 :=
  .pair rawMapLength
    (.lam (.app (.lam (.app (.var 2) (.app (.var 2) (.var 0)))) (.var 0)))

theorem original_program :
    continuationProgram common source (invoke common source.request) =
      some (.pure originalResult) := by
  change continuationProgram common source (invoke common request) = some (.pure originalResult)
  rw [(invoke_iff _ _ _).mpr actual_crossing]
  rfl

theorem substituted_program :
    continuationProgram common (source.substitute squareSubstitution)
      (invoke common (source.substitute squareSubstitution).request) =
      some (.pure substitutedResult) := by
  rw [(invoke_iff _ _ _).mpr substituted_actual_crossing]
  rfl

/-- The actual result has the independently derived substituted body type.
The HOL proof is still at the response boundary, not a native inhabitant. -/
theorem substituted_result_admitted :
    FormationSensitive.Judgment common.rules mappingContext substitutedResult
      (subst squareSubstitution (inst0 rawMapLength bodyType)) := by
  apply substituted_continuation_preserves common_qualified request_admitted
    functionSquare_admitted.context squareSubstitution_typed actual_crossing
    (source := source) (response := response) (payload := rawMapLength)
    (type := .const `HOLUniformList.prop) (body := body_admitted) (returned := by rfl)
    (program := .pure substitutedResult) (state := false) (branch := [])
    (output := ⟨[], substitutedResult, false, []⟩)
  · rfl
  · exact List.mem_cons_self

/-- One accepted request, its substituted authored body, the complete world
list, and the independently admitted result share the same concrete data. -/
theorem substituted_workload (state : Bool) (branch : BranchTrace) :
    ∃ program : Program Bool (Tower.Tm 1) Nat,
      continuationProgram common (source.substitute squareSubstitution)
        (invoke common (source.substitute squareSubstitution).request) = some program ∧
      runWorldsAt program state branch =
        [{ branch := branch, answer := substitutedResult, state := state, intents := [] }] ∧
      FormationSensitive.Judgment common.rules mappingContext substitutedResult
        (subst squareSubstitution (inst0 rawMapLength bodyType)) :=
  ⟨.pure substitutedResult, substituted_program, rfl, substituted_result_admitted⟩

/-- A dropped lift would refer to the service payload as a function. The
actual source substitution is not that captured syntax. -/
theorem captured_body_rejected :
    (source.substitute squareSubstitution).continuation ≠
      .returnValue (.pair (.var 0)
        (.lam (.app (.lam (.app (.var 2) (.app (.var 2) (.var 0)))) (.var 0)))) := by
  rw [substituted_body]
  decide

/-- Ignoring the changed environment changes the actual returned syntax.
This is an exact-output control, not a conversion or logical refutation. -/
theorem changed_environment_changes_result : substitutedResult ≠ originalResult := by decide

theorem wrong_environment_program_rejected :
    continuationProgram common (source.substitute squareSubstitution)
      (invoke common (source.substitute squareSubstitution).request) ≠
      some (.pure originalResult) := by
  rw [substituted_program]
  intro same
  exact changed_environment_changes_result (Program.pure.inj (Option.some.inj same))

theorem wrong_environment_worlds_rejected (state : Bool) (branch : BranchTrace) :
    ¬ ∃ program : Program Bool (Tower.Tm 1) Nat,
      continuationProgram common (source.substitute squareSubstitution)
        (invoke common (source.substitute squareSubstitution).request) = some program ∧
      runWorldsAt program state branch =
        [{ branch := branch, answer := originalResult, state := state, intents := [] }] := by
  rintro ⟨program, selected, worlds⟩
  rw [substituted_program] at selected
  cases (Option.some.inj selected).symm
  have answers := congrArg (List.map WorldResult.answer) worlds
  change [substitutedResult] = [originalResult] at answers
  exact changed_environment_changes_result (List.cons.inj answers).1

end SubstitutionExamples

#print axioms Request.substitute_comp
#print axioms Response.substitute_comp
#print axioms Response.nativePayload_substitute
#print axioms Invocation.substitute
#print axioms invoke_substitute
#print axioms Source.substitute_comp
#print axioms EnvironmentAdmitted.substitute
#print axioms continuationProgram_substitute
#print axioms substituted_continuation_preserves
#print axioms SubstitutionExamples.substituted_request_admitted
#print axioms SubstitutionExamples.substituted_actual_crossing
#print axioms SubstitutionExamples.substituted_result_admitted
#print axioms SubstitutionExamples.substituted_workload
#print axioms SubstitutionExamples.captured_body_rejected
#print axioms SubstitutionExamples.wrong_environment_program_rejected
#print axioms SubstitutionExamples.wrong_environment_worlds_rejected

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServices
