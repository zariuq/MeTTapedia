import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentServiceProgramBackend
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeWireDataDenotation
import Mettapedia.GSLT.Core.PolicyFamilySufficiency

/-!
# Retained source context and public observations of service programs

An implicit native environment can be elaborated into scoped source without
changing the complete observations of the independently authored backend.
The original source, environment and admission claim can nevertheless be
retained for an inspecting consumer. Completion output alone cannot recover
that source: two different authored programs can have exactly the same
complete output, including replies, effects and branch records.

These interfaces describe the existing finite service-program presentation.
They do not select a surface syntax, equate source substitution with a
small-step cost model, or implement full CBPV. The assembly and target context
are external parameters. A native substitution is not a complete account of
store revisions, authorization or interpretation dependencies.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentPublicContext

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation SharedJudgmentFragment SharedJudgmentServices SharedJudgmentServicePrograms
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.GSLT.Dynamics.ServiceResumption
open Mettapedia.GSLT.Core

variable {n m : Nat}

/-- Raw input metadata. Stating a source type or context here is not evidence
that the program or its environment has that type. -/
structure Input (n m : Nat) where
  sourceContext : Tower.Ctx n
  code : Code n
  resultType : Tower.Tm n
  environment : Sub Tower.Head n m
  initialState : Bool
  initialBranch : BranchTrace

def Input.start (input : Input n m) : SharedJudgmentServiceProgramBackend.Term m :=
  SharedJudgmentServiceProgramBackend.start input.environment input.code input.initialState input.initialBranch

def Input.elaborated (input : Input n m) : Code m :=
  input.code.substitute input.environment

/-- Admission binds the actual source and substitution to one externally
supplied target context, using the existing formation-sensitive judgments. -/
def Input.Admitted (assembly : Assembly) (targetContext : Tower.Ctx m)
    (input : Input n m) : Prop :=
  Admission assembly input.sourceContext input.code input.resultType ∧
    FormationSensitive.ContextFormation assembly.rules targetContext ∧
    FormationSensitive.CtxMor assembly.rules input.sourceContext targetContext input.environment

def Input.Completes (assembly : Assembly) (input : Input n m)
    (outputs : List (SharedJudgmentServiceProgramBackend.Output m)) : Prop :=
  SharedJudgmentServiceProgramBackend.Reaches assembly input.start (.completed outputs)

/-- Expanding an implicit environment into the full scoped code preserves
and reflects completion with the same complete outputs, not only the final
native values. No correspondence of paths or costs is asserted. -/
theorem elaborated_completion_iff (assembly : Assembly) (input : Input n m)
    (outputs : List (SharedJudgmentServiceProgramBackend.Output m)) :
    SharedJudgmentServiceProgramBackend.Reaches assembly
        (SharedJudgmentServiceProgramBackend.start ids input.elaborated input.initialState input.initialBranch)
        (.completed outputs) ↔ input.Completes assembly outputs := by
  simpa only [Input.elaborated, Input.Completes, Input.start, subComp_ids_left] using
    SharedJudgmentServiceProgramBackend.completion_substitute_iff assembly ids input.environment input.code
      input.initialState input.initialBranch outputs

/-- The ordinary runner is the existing source interpretation. Its result is
qualified against the backend below, rather than installed as a new rule. -/
def Input.run (assembly : Assembly) (input : Input n m) : List (SharedJudgmentServiceProgramBackend.Output m) :=
  Code.run assembly input.environment input.code input.initialState input.initialBranch

theorem completes_iff_run (assembly : Assembly) (input : Input n m)
    (outputs : List (SharedJudgmentServiceProgramBackend.Output m)) :
    input.Completes assembly outputs ↔ outputs = input.run assembly :=
  SharedJudgmentServiceProgramBackend.completion_run_iff assembly input.environment input.code
    input.initialState input.initialBranch outputs

theorem run_has_backend_completion (assembly : Assembly) (input : Input n m) :
    input.Completes assembly (input.run assembly) :=
  (completes_iff_run assembly input _).mpr rfl

/-- Equal elaborations and equal initial worlds determine equal complete
outputs at one fixed assembly. This does not assert equal machine traces. -/
theorem run_eq_of_elaboration_eq (assembly : Assembly) (first second : Input n m)
    (code : first.elaborated = second.elaborated)
    (state : first.initialState = second.initialState)
    (branch : first.initialBranch = second.initialBranch) :
    first.run assembly = second.run assembly := by
  have firstPath := (elaborated_completion_iff assembly first _).mpr
    (run_has_backend_completion assembly first)
  have secondPath := (elaborated_completion_iff assembly second _).mpr
    (run_has_backend_completion assembly second)
  rw [code, state, branch] at firstPath
  exact (SharedJudgmentServiceProgramBackend.completion_sound assembly ids second.elaborated
    second.initialState second.initialBranch firstPath).trans
      (SharedJudgmentServiceProgramBackend.completion_sound assembly ids second.elaborated
        second.initialState second.initialBranch secondPath).symm

/-- Merely retaining the source makes no reachability assertion. The current
configuration is kept separately, so a restart is not mislabeled a resume. -/
structure Retained (n m : Nat) where
  input : Input n m
  configuration : SharedJudgmentServiceProgramBackend.Term m

def Retained.Reachable (assembly : Assembly) (retained : Retained n m) : Prop :=
  SharedJudgmentServiceProgramBackend.Reaches assembly retained.input.start retained.configuration

/-- An inspectable completed record. Authenticity remains a separate
predicate relating its outputs to the actual original backend start. -/
structure Completion (n m : Nat) where
  input : Input n m
  outputs : List (SharedJudgmentServiceProgramBackend.Output m)

def Completion.Authentic (assembly : Assembly) (completion : Completion n m) : Prop :=
  completion.input.Completes assembly completion.outputs

def Completion.retained (completion : Completion n m) : Retained n m :=
  ⟨completion.input, .completed completion.outputs⟩

theorem Completion.authentic_iff_reachable (assembly : Assembly)
    (completion : Completion n m) :
    completion.Authentic assembly ↔ completion.retained.Reachable assembly := Iff.rfl

def complete (assembly : Assembly) (input : Input n m) : Completion n m :=
  ⟨input, input.run assembly⟩

theorem complete_authentic (assembly : Assembly) (input : Input n m) :
    (complete assembly input).Authentic assembly :=
  run_has_backend_completion assembly input

/-- Retained admission metadata yields a typing conclusion only together
with source admission, qualified services and authentic backend execution. -/
theorem admitted_completion_value {assembly : Assembly}
    (qualified : specification.Satisfies assembly) {targetContext : Tower.Ctx m}
    {completion : Completion n m}
    (admitted : completion.input.Admitted assembly targetContext)
    (authentic : completion.Authentic assembly)
    {output : SharedJudgmentServiceProgramBackend.Output m} {value : Tower.Tm m}
    (observed : output ∈ completion.outputs) (isValue : output.world.answer = .value value) :
    FormationSensitive.Judgment assembly.rules targetContext value
      (subst completion.input.environment completion.input.resultType) :=
  SharedJudgmentServiceProgramBackend.completion_value_admitted qualified admitted.1 admitted.2.1 admitted.2.2
    authentic observed isValue

/-! ## Different declared consumers of the same retained record -/

inductive Inspection where
  | outputs
  | originalSource
  | nativeEnvironment

/-- Three concrete observations, not a claim to enumerate every cognitive
consumer. An occurrence-history or dependency consumer must be added explicitly. -/
def inspectionFamily (n m : Nat) : PolicyFamily (Completion n m) where
  Policy := Inspection
  Result
    | .outputs => List (SharedJudgmentServiceProgramBackend.Output m)
    | .originalSource => Code n
    | .nativeEnvironment => Sub Tower.Head n m
  decide
    | .outputs, completion => completion.outputs
    | .originalSource, completion => completion.input.code
    | .nativeEnvironment, completion => completion.input.environment

def outputFamily (n m : Nat) : PolicyFamily (Completion n m) :=
  (inspectionFamily n m).reindex (fun _ : Unit => Inspection.outputs)

/-- Hiding the original input is sufficient for this declared output-only
consumer. It is not automatically sufficient for the larger inspection family. -/
def outputRealization (n m : Nat) :
    (outputFamily n m).ReadoutRealization Completion.outputs where
  run := fun _ outputs => outputs
  agrees := fun _ _ => rfl

/-! ## Actual scoped programs distinguish hiding from erasure -/

namespace Controls

open NativeWireDataDenotation

def parameterInput (value : Value) : Input 4 3 where
  sourceContext := NativeMatchedTransportDenotation.parameterContext
  code := .native (.returnValue parameterTerm)
  resultType := NativeWireData.dataType
  environment := fillParameter value
  initialState := false
  initialBranch := []

theorem parameter_admitted (value : Value) :
    (parameterInput value).Admitted common OpaqueRelatorScopedComputation.Common.context := by
  refine ⟨.native ⟨NativeMatchedTransportDenotation.parameterContext_formed,
    .returnValue ?_⟩, OpaqueRelatorScopedComputation.Common.context_formed,
    fillParameter_typed value⟩
  exact (parameterTerm_denotes (State := Unit) (fun _ _ => Value.nil)).typed

theorem parameter_completion (value : Value) :
    (parameterInput value).Completes common
      [⟨⟨[], .value (quote (parameterValue value)), false, []⟩, []⟩] := by
  apply (completes_iff_run common (parameterInput value) _).mpr
  rw [Input.run, Code.interpret_worlds common common_execution]
  simp only [parameterInput, Code.worlds, ScopedComputation.Code.worlds, fillParameter_term,
    List.map_cons, List.map_nil]

/-- This control changes an actually typed, nonidentity substitution while
retaining exactly the same displayed source program. -/
theorem same_source_different_environment (left right : Value) (different : left ≠ right) :
    (parameterInput left).code = (parameterInput right).code ∧
      (parameterInput left).run common ≠ (parameterInput right).run common := by
  refine ⟨rfl, ?_⟩
  have first := (completes_iff_run common (parameterInput left) _).mp (parameter_completion left)
  have second := (completes_iff_run common (parameterInput right) _).mp (parameter_completion right)
  intro equal
  have outputs := first.trans (equal.trans second.symm)
  have sameTerm : quote (n := 3) (parameterValue left) = quote (parameterValue right) := by
    injection outputs with head
    have answer := congrArg (fun result : SharedJudgmentServiceProgramBackend.Output 3 => result.world.answer) head
    exact Outcome.value.inj answer
  have firstMeaning := quote_denotes OpaqueRelatorScopedComputation.Common.context
    (fun (_ : Fin 3) (_ : Unit) => Value.nil) (parameterValue left)
  have secondMeaning := quote_denotes OpaqueRelatorScopedComputation.Common.context
    (fun (_ : Fin 3) (_ : Unit) => Value.nil) (parameterValue right)
  rw [← sameTerm] at secondMeaning
  exact different (parameterValue_injective
    (congrFun (firstMeaning.functional secondMeaning) ()))

/-- Return directly, or return and then pass the selected value through a
native binder. These are genuinely different source constructors. -/
def direct (value : Value) : Input 4 3 := parameterInput value

def detour (value : Value) : Input 4 3 :=
  { parameterInput value with
    code := .sequence (.native (.returnValue parameterTerm)) (.native (.returnValue (.var 0))) }

theorem detour_admitted (value : Value) :
    (detour value).Admitted common OpaqueRelatorScopedComputation.Common.context := by
  have formed := HOLNativeRelatorCompatibility.wire_typing
    (NativeWireData.dataType_formed NativeMatchedTransportDenotation.parameterContext)
  refine ⟨.sequence formed (.sort Tower.zero) formed (.sort Tower.zero)
    (parameter_admitted value).1 ?_, OpaqueRelatorScopedComputation.Common.context_formed,
    fillParameter_typed value⟩
  exact .native ⟨.snoc NativeMatchedTransportDenotation.parameterContext_formed formed
    (.sort Tower.zero), .returnValue (.var 0)⟩

theorem source_distinct (value : Value) : (direct value).code ≠ (detour value).code := by
  intro same
  cases same

theorem output_same (value : Value) : (direct value).run common = (detour value).run common := by
  rw [Input.run, Input.run, Code.interpret_worlds common common_execution,
    Code.interpret_worlds common common_execution]
  simp only [direct, detour, parameterInput, Code.worlds, ScopedComputation.Code.worlds,
    fillParameter_term, subst, consSub_zero, List.map_cons, List.map_nil, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, Result.prepend]

/-- Output-only erasure loses the distinction even on authentic executions
of admitted programs, not merely on forged or unformed records. -/
theorem authentic_output_cannot_recover_source :
    ¬ NonFactorization.Factors
      (fun completion : { completion : Completion 4 3 // completion.Authentic common ∧
          completion.input.Admitted common OpaqueRelatorScopedComputation.Common.context } =>
        completion.val.outputs)
      (fun completion => completion.val.input.code) := by
  let first : { completion : Completion 4 3 // completion.Authentic common ∧
      completion.input.Admitted common OpaqueRelatorScopedComputation.Common.context } :=
    ⟨complete common (direct (.symbol "payload")),
      complete_authentic _ _, parameter_admitted _⟩
  let second : { completion : Completion 4 3 // completion.Authentic common ∧
      completion.input.Admitted common OpaqueRelatorScopedComputation.Common.context } :=
    ⟨complete common (detour (.symbol "payload")),
      complete_authentic _ _, detour_admitted _⟩
  apply NonFactorization.NonTrivialFiber.not_factors
  exact ⟨first, second, output_same _, source_distinct _⟩

theorem inspection_refuses_output_only :
    ¬ (inspectionFamily 4 3).SupportsReadout Completion.outputs := by
  apply (inspectionFamily 4 3).not_supportsReadout_of_policy_collision Completion.outputs
    (first := complete common (direct (.symbol "payload")))
    (second := complete common (detour (.symbol "payload")))
    (output_same (.symbol "payload")) .originalSource
  exact source_distinct (.symbol "payload")

end Controls

#print axioms elaborated_completion_iff
#print axioms run_eq_of_elaboration_eq
#print axioms admitted_completion_value
#print axioms Controls.parameter_completion
#print axioms Controls.parameter_admitted
#print axioms Controls.detour_admitted
#print axioms Controls.same_source_different_environment
#print axioms Controls.authentic_output_cannot_recover_source
#print axioms Controls.inspection_refuses_output_only

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentPublicContext
