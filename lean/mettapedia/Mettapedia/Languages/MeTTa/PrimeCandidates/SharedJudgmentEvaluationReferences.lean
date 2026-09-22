import Mettapedia.TypeTheory.ContextualEvaluationReferences
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNamedContext

/-!
# Scoped evaluation references for admitted service programs

The origin and evaluation references are independent coordinates. The former
supports pure inspection of the retained source and its named environment;
the latter resolves the substitution used by the existing service interpreter.
Its lowering is the existing effect program, with no replacement interpreter.
The reader laws therefore apply before observing that program's actual worlds.

Missing context resolution is an explicit outer failure, not an empty successful
enumeration. The optional answer below is only a mathematical totalization of
partial resolution. It does not prescribe an allocation, diagnostic namespace,
execution history, or repeated judgment invocation in an implementation.

The native substitution square and backend admission laws concern executions
at one common final scope. They do not assert naturality of arbitrary handlers
between different native scopes, identify a space handle with a logical context,
or select a surface meaning for `&self` or a default reference mode.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentEvaluationReferences

open Mettapedia.Machines
open Mettapedia.TypeTheory
open Mettapedia.GSLT.Dynamics
open Mettapedia.TypeTheory.NamedValueContexts
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation SharedJudgmentFragment SharedJudgmentServicePrograms SharedJudgmentServices
open SharedJudgmentPublicContext
open SharedJudgmentNamedContext (Body Table)
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.GSLT.Dynamics.ServiceResumption (Result)


variable {Name Revision : Type} {n m : Nat}

abbrev Frame (Name Revision : Type) := ContextualEvaluationReferences.References (Reference Name Revision)
abbrev Answer (m : Nat) := Outcome m × List (Sigma (@Response m))
abbrev Execution (Name Revision : Type) (m : Nat) :=
  ContextualEvaluationReferences.Computation (Reference Name Revision) Bool (Option (Answer m)) Nat

/-- The same actual service interpreter and request lowering, selected by the
evaluation coordinate. Origin is not implicitly substituted for this coordinate. -/
def program (assembly : Assembly) (table : Table Name Revision n m)
    (current : RevisionEnvironment Name Revision) (body : Body n) :
    Execution Name Revision m := fun frame =>
  match resolve table current frame.evaluation with
  | none => .pure none
  | some environment => Program.map some
      (ServiceResumption.lower (invoke assembly) (Code.interpret assembly environment body.code))

def decodeWorld (world : WorldResult Bool (Option (Answer m)) Nat) :
    Option (SharedJudgmentServiceProgramBackend.Output m) :=
  world.answer.map fun answer => Result.ofWorld
    { branch := world.branch, answer := answer, state := world.state, intents := world.intents }

def decodeWorlds : List (WorldResult Bool (Option (Answer m)) Nat) →
    Option (List (SharedJudgmentServiceProgramBackend.Output m))
  | [] => some []
  | world :: rest => do
      let output ← decodeWorld world
      let outputs ← decodeWorlds rest
      pure (output :: outputs)

/-- The observation wrapper preserves every actual world and reply; it does
not discard missing results with a filtering operation. -/
theorem decodeWorlds_some (worlds : List (WorldResult Bool (Answer m) Nat)) :
    decodeWorlds (worlds.map (ContextualDependentSequencing.WorldResult.mapAnswer some)) =
      some (worlds.map Result.ofWorld) := by
  induction worlds with
  | nil => rfl
  | cons world rest ih =>
      simp only [List.map_cons, decodeWorlds, decodeWorld,
        ContextualDependentSequencing.WorldResult.mapAnswer, Option.map_some, ih]
      rfl

def observe (execution : Execution Name Revision m) (frame : Frame Name Revision)
    (state : Bool) (branch : BranchTrace) : Option (List (SharedJudgmentServiceProgramBackend.Output m)) :=
  decodeWorlds (runWorldsAt (execution frame) state branch)

def run (assembly : Assembly) (table : Table Name Revision n m)
    (current : RevisionEnvironment Name Revision) (body : Body n)
    (frame : Frame Name Revision) : Option (List (SharedJudgmentServiceProgramBackend.Output m)) :=
  observe (program assembly table current body) frame body.initialState body.initialBranch

/-- Exact agreement with the previously qualified named runner. The proof
passes through its actual effect lowering, not a newly stipulated transition. -/
theorem run_eq_named (assembly : Assembly) (table : Table Name Revision n m)
    (current : RevisionEnvironment Name Revision) (body : Body n)
    (frame : Frame Name Revision) :
    run assembly table current body frame =
      SharedJudgmentNamedContext.run assembly table current ⟨body, frame.evaluation⟩ := by
  cases found : resolve table current frame.evaluation with
  | none =>
      simp [run, observe, program, found, SharedJudgmentNamedContext.run, SharedJudgmentNamedContext.resolveInput,
        runWorldsAt, decodeWorlds, decodeWorld]
  | some environment =>
      simp only [run, observe, program, found, ContextualDependentSequencing.runWorldsAt_map,
        decodeWorlds_some, SharedJudgmentNamedContext.run, SharedJudgmentNamedContext.resolveInput, Option.map_some,
        Body.bind, Input.run, Code.run, ServiceResumption.runWorldsAt]

/-- Scoped relocation changes only the selected named evaluation context,
and still reaches the independently authored backend relation. -/
theorem scoped_backend_iff (assembly : Assembly) (table : Table Name Revision n m)
    (current : RevisionEnvironment Name Revision) (body : Body n)
    (frame : Frame Name Revision) (target : Reference Name Revision)
    (environment : Sub Tower.Head n m)
    (found : resolve table current target = some environment)
    (outputs : List (SharedJudgmentServiceProgramBackend.Output m)) :
    observe (ContextualEvaluationReferences.atSpace target (program assembly table current body)) frame
        body.initialState body.initialBranch = some outputs ↔
      (body.bind environment).Completes assembly outputs := by
  change run assembly table current body { frame with evaluation := target } = _ ↔ _
  rw [run_eq_named]
  exact SharedJudgmentNamedContext.run_backend_iff assembly table current ⟨body, target⟩ environment found outputs

/-- The source/context substitution square holds at the effect-program level,
before worlds, branch histories, replies or values are observed. -/
theorem scoped_program_substitution {k : Nat} (assembly : Assembly)
    (table : Table Name Revision k m) (current : RevisionEnvironment Name Revision)
    (body : Body n) (middle : Tower.Ctx k) (earlier : Sub Tower.Head n k)
    (target : Reference Name Revision) :
    ContextualEvaluationReferences.atSpace target (program assembly table current (body.substitute middle earlier)) =
      ContextualEvaluationReferences.atSpace target (program assembly (SharedJudgmentNamedContext.precompose earlier table) current body) := by
  funext frame
  simp only [ContextualEvaluationReferences.atSpace, ContextualEvaluationReferences.withReferences, program, SharedJudgmentNamedContext.resolve_precompose]
  cases resolve table current target with
  | none => rfl
  | some later =>
      simp only [Option.map_some, Body.substitute, Code.interpret_substitute]

/-- Typed source and two genuine context morphisms qualify the same scoped
square. Its dependent result type keeps both substitutions. -/
theorem scoped_substitution_value_admitted {k : Nat} {assembly : Assembly}
    (qualified : specification.Satisfies assembly)
    (table : Table Name Revision k m) (current : RevisionEnvironment Name Revision)
    (body : Body n) (middle : Tower.Ctx k) (targetContext : Tower.Ctx m)
    (earlier : Sub Tower.Head n k) (later : Sub Tower.Head k m)
    (admitted : Admission assembly body.sourceContext body.code body.resultType)
    (earlierTyped : FormationSensitive.CtxMor assembly.rules body.sourceContext middle earlier)
    (laterTyped : FormationSensitive.CtxMor assembly.rules middle targetContext later)
    (targetFormed : FormationSensitive.ContextFormation assembly.rules targetContext)
    (frame : Frame Name Revision) (target : Reference Name Revision)
    (found : resolve table current target = some later)
    (outputs : List (SharedJudgmentServiceProgramBackend.Output m))
    (completed : observe (ContextualEvaluationReferences.atSpace target
        (program assembly table current (body.substitute middle earlier))) frame
        body.initialState body.initialBranch = some outputs)
    {output : SharedJudgmentServiceProgramBackend.Output m} {value : Tower.Tm m}
    (member : output ∈ outputs) (isValue : output.world.answer = .value value) :
    FormationSensitive.Judgment assembly.rules targetContext value
      (subst later (subst earlier body.resultType)) := by
  have path := (scoped_backend_iff assembly table current (body.substitute middle earlier)
    frame target later found outputs).mp completed
  exact SharedJudgmentServiceProgramBackend.completion_substitute_value_admitted qualified admitted earlierTyped laterTyped
    targetFormed path member isValue

/-- Origin inspection has no assembly or evaluator argument. It retains the
authored body and caller-selected binding footprint without executing either. -/
def inspectOrigin (table : Table Name Revision n m)
    (current : RevisionEnvironment Name Revision) (body : Body n)
    (frame : Frame Name Revision) (footprint : List (Fin n)) :
    Option (Body n × List (Fin n × Option (Tower.Tm m))) :=
  SharedJudgmentNamedContext.inspectInput table current ⟨body, frame.origin⟩ footprint

theorem relocation_preserves_origin_inspection (table : Table Name Revision n m)
    (current : RevisionEnvironment Name Revision) (body : Body n)
    (frame : Frame Name Revision) (target : Reference Name Revision)
    (footprint : List (Fin n)) :
    inspectOrigin table current body { frame with evaluation := target } footprint =
      inspectOrigin table current body frame footprint := rfl

/-- Fresh named publication preserves a retained origin binding. The live
evaluation selector is unrestricted and need not retain its earlier output. -/
theorem publication_preserves_origin [DecidableEq Name] [DecidableEq Revision]
    (table updated : Table Name Revision n m) (before after : RevisionEnvironment Name Revision)
    (body : Body n) (oldVersion newVersion : StoreReadToken Name Revision)
    (oldEnvironment newEnvironment : Sub Tower.Head n m)
    (found : table oldVersion = some oldEnvironment)
    (published : publishVersion? table newVersion newEnvironment = some updated)
    (evaluation : Reference Name Revision) (footprint : List (Fin n)) :
    inspectOrigin updated after body ⟨.versioned oldVersion, evaluation⟩ footprint =
      inspectOrigin table before body ⟨.versioned oldVersion, evaluation⟩ footprint := by
  have retained := publication_preserves_existing table updated newVersion oldVersion
    newEnvironment oldEnvironment published found
  simp only [inspectOrigin, SharedJudgmentNamedContext.inspectInput, inspect, resolve, retained, found]

namespace Controls

open NativeWireDataDenotation
open Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation

def frame : Frame String Nat := ⟨.versioned SharedJudgmentNamedContext.Controls.oldVersion, .live "C"⟩

/-- The same actual typed native source keeps its origin inspection while
its deliberately live evaluation environment changes its backend output. -/
theorem stable_origin_live_evaluation :
    inspectOrigin SharedJudgmentNamedContext.Controls.newTable SharedJudgmentNamedContext.Controls.after SharedJudgmentNamedContext.Controls.body frame [0] =
      inspectOrigin SharedJudgmentNamedContext.Controls.oldTable SharedJudgmentNamedContext.Controls.before SharedJudgmentNamedContext.Controls.body frame [0] ∧
    run common SharedJudgmentNamedContext.Controls.oldTable SharedJudgmentNamedContext.Controls.before SharedJudgmentNamedContext.Controls.body frame ≠
      run common SharedJudgmentNamedContext.Controls.newTable SharedJudgmentNamedContext.Controls.after SharedJudgmentNamedContext.Controls.body frame := by
  constructor
  · exact publication_preserves_origin SharedJudgmentNamedContext.Controls.oldTable SharedJudgmentNamedContext.Controls.newTable
      SharedJudgmentNamedContext.Controls.before SharedJudgmentNamedContext.Controls.after SharedJudgmentNamedContext.Controls.body SharedJudgmentNamedContext.Controls.oldVersion SharedJudgmentNamedContext.Controls.newVersion
      (fillParameter (.natural 2)) (fillParameter (.natural 3))
      SharedJudgmentNamedContext.Controls.old_binding_resolves SharedJudgmentNamedContext.Controls.accepted_publication (.live "C") [0]
  · simpa only [run_eq_named, frame, SharedJudgmentNamedContext.Controls.live] using
      SharedJudgmentNamedContext.Controls.live_update_changes_output

/-- Redirecting execution to the unchanged origin is observably wrong for
this explicitly live program, although its displayed native source is identical. -/
theorem origin_cannot_replace_evaluation :
    observe (ContextualEvaluationReferences.atSpace frame.origin
      (program common SharedJudgmentNamedContext.Controls.newTable SharedJudgmentNamedContext.Controls.after SharedJudgmentNamedContext.Controls.body)) frame false [] ≠
      run common SharedJudgmentNamedContext.Controls.newTable SharedJudgmentNamedContext.Controls.after SharedJudgmentNamedContext.Controls.body frame := by
  change run common SharedJudgmentNamedContext.Controls.newTable SharedJudgmentNamedContext.Controls.after SharedJudgmentNamedContext.Controls.body
    { frame with evaluation := frame.origin } ≠ _
  rw [run_eq_named, run_eq_named]
  change SharedJudgmentNamedContext.run common SharedJudgmentNamedContext.Controls.newTable SharedJudgmentNamedContext.Controls.after SharedJudgmentNamedContext.Controls.stable ≠
    SharedJudgmentNamedContext.run common SharedJudgmentNamedContext.Controls.newTable SharedJudgmentNamedContext.Controls.after SharedJudgmentNamedContext.Controls.live
  rw [SharedJudgmentNamedContext.Controls.stable_preserves_backend]
  exact SharedJudgmentNamedContext.Controls.live_update_changes_output

/-- Missing evaluation does not evaluate using a resolvable origin, and does
not manufacture an empty successful search. -/
theorem missing_evaluation_is_not_origin_fallback :
    run common SharedJudgmentNamedContext.Controls.oldTable SharedJudgmentNamedContext.Controls.before SharedJudgmentNamedContext.Controls.body
      ⟨.versioned SharedJudgmentNamedContext.Controls.oldVersion, .versioned SharedJudgmentNamedContext.Controls.newVersion⟩ = none ∧
    run common SharedJudgmentNamedContext.Controls.oldTable SharedJudgmentNamedContext.Controls.before SharedJudgmentNamedContext.Controls.body
      ⟨.versioned SharedJudgmentNamedContext.Controls.oldVersion, .versioned SharedJudgmentNamedContext.Controls.newVersion⟩ ≠ some [] := by
  rw [run_eq_named]
  have missing : SharedJudgmentNamedContext.run common SharedJudgmentNamedContext.Controls.oldTable
      SharedJudgmentNamedContext.Controls.before
      ⟨SharedJudgmentNamedContext.Controls.body,
        .versioned SharedJudgmentNamedContext.Controls.newVersion⟩ = none := rfl
  rw [missing]
  exact ⟨rfl, by intro impossible; cases impossible⟩

def identityTable (scope : Nat) : Table String Nat scope scope :=
  writeSource (fun _ => none) (SharedJudgmentNamedContext.Controls.newVersion, ids)

theorem identity_resolves (scope : Nat) :
    resolve (identityTable scope) SharedJudgmentNamedContext.Controls.before
      (.versioned SharedJudgmentNamedContext.Controls.newVersion) = some ids := by
  simp [resolve, identityTable, writeSource]

/-- A nonidentity typed native substitution is executed after source
substitution under relocation. The conclusion includes the actual output and
its independently admitted dependent result type, not only an abstract square. -/
theorem relocated_parameter_typed (value : Value) :
    observe (ContextualEvaluationReferences.atSpace
        (.versioned SharedJudgmentNamedContext.Controls.newVersion)
        (program common (identityTable 3) SharedJudgmentNamedContext.Controls.before
          (SharedJudgmentNamedContext.Controls.body.substitute
            OpaqueRelatorScopedComputation.Common.context (fillParameter value))))
      frame false [] =
        some [⟨⟨[], .value (quote (parameterValue value)), false, []⟩, []⟩] ∧
    FormationSensitive.Judgment common.rules OpaqueRelatorScopedComputation.Common.context
      (quote (parameterValue value))
      (subst ids (subst (fillParameter value) SharedJudgmentNamedContext.Controls.body.resultType)) := by
  have original := SharedJudgmentPublicContext.Controls.parameter_completion value
  have completed :
      (SharedJudgmentNamedContext.Controls.body.substitute
        OpaqueRelatorScopedComputation.Common.context (fillParameter value)).bind ids |>.Completes common
          [⟨⟨[], .value (quote (parameterValue value)), false, []⟩, []⟩] := by
    apply (SharedJudgmentServiceProgramBackend.completion_substitute_iff
      common ids (fillParameter value) SharedJudgmentNamedContext.Controls.body.code
      false [] _).mpr
    simpa only [subComp_ids_left, Input.Completes, Input.start,
      SharedJudgmentPublicContext.Controls.parameterInput,
      SharedJudgmentNamedContext.Controls.body] using original
  have executed := (scoped_backend_iff common (identityTable 3)
    SharedJudgmentNamedContext.Controls.before
    (SharedJudgmentNamedContext.Controls.body.substitute
      OpaqueRelatorScopedComputation.Common.context (fillParameter value))
    frame (.versioned SharedJudgmentNamedContext.Controls.newVersion) ids
    (identity_resolves 3) _).mpr completed
  refine ⟨executed, ?_⟩
  have admission := SharedJudgmentPublicContext.Controls.parameter_admitted value
  have identityTyped : FormationSensitive.CtxMor common.rules
      OpaqueRelatorScopedComputation.Common.context
      OpaqueRelatorScopedComputation.Common.context ids := by
    intro index
    simpa only [ids, subst_ids] using
      (FormationSensitive.Typing.var (R := common.rules)
        (Γ := OpaqueRelatorScopedComputation.Common.context) index)
  exact scoped_substitution_value_admitted common_qualified (identityTable 3)
    SharedJudgmentNamedContext.Controls.before SharedJudgmentNamedContext.Controls.body
    OpaqueRelatorScopedComputation.Common.context OpaqueRelatorScopedComputation.Common.context
    (fillParameter value) ids admission.1 admission.2.2 identityTyped admission.2.1
    frame (.versioned SharedJudgmentNamedContext.Controls.newVersion) (identity_resolves 3)
    _ executed (List.mem_singleton_self _) rfl

def holBody : Body 2 where
  sourceContext := ScopedComputation.NativeExamples.context
  code := SharedJudgmentServicePrograms.AdmissionExamples.matchingThenHOLIdentity
  resultType := SharedJudgmentServicePrograms.AdmissionExamples.nestedType
  initialState := false
  initialBranch := []

/-- Relocation also passes actual matching and HOL-induction service calls
through the existing backend, followed by native dependent-pair/reflexivity
construction. This is not restricted to a pure returned constant. -/
theorem relocated_hol_services :
    observe (ContextualEvaluationReferences.atSpace
      (.versioned SharedJudgmentNamedContext.Controls.newVersion)
      (program common (identityTable 2) SharedJudgmentNamedContext.Controls.before holBody))
      frame false [] = some [SharedJudgmentServiceProgramBackend.Controls.nestedOutput false []] ∧
    FormationSensitive.Judgment common.rules ScopedComputation.NativeExamples.context
      SharedJudgmentServicePrograms.AdmissionExamples.nestedValue
      SharedJudgmentServicePrograms.AdmissionExamples.nestedType := by
  have native := SharedJudgmentServiceProgramBackend.Controls.nested_completion_admitted false []
  refine ⟨?_, native.2⟩
  exact (scoped_backend_iff common (identityTable 2) SharedJudgmentNamedContext.Controls.before
    holBody frame (.versioned SharedJudgmentNamedContext.Controls.newVersion) ids
    (identity_resolves 2) _).mpr native.1

end Controls

#print axioms run_eq_named
#print axioms scoped_backend_iff
#print axioms scoped_program_substitution
#print axioms scoped_substitution_value_admitted
#print axioms publication_preserves_origin
#print axioms Controls.stable_origin_live_evaluation
#print axioms Controls.origin_cannot_replace_evaluation
#print axioms Controls.missing_evaluation_is_not_origin_fallback
#print axioms Controls.relocated_parameter_typed
#print axioms Controls.relocated_hol_services

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentEvaluationReferences
