import Mettapedia.TypeTheory.NamedValueContexts
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentPublicContext

/-!
# Named environments for the existing admitted service programs

A code object refers explicitly to a versioned or live context. Resolution
supplies the actual native substitution to the existing source interpreter;
it does not introduce another evaluator. Source admission, target formation
and typed substitution remain independently required. Pure inspection has no
assembly or handler argument and does not execute the program.

These laws qualify one candidate interface. They do not choose a default
reference mode, require a context copy or retained history, or assert that a
lexical snapshot freezes mutable handles reachable through its bindings.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNamedContext

open Mettapedia.TypeTheory.NamedValueContexts
open Mettapedia.Machines
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation SharedJudgmentFragment SharedJudgmentServicePrograms
open SharedJudgmentPublicContext
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.GSLT.Dynamics.ServiceResumption

variable {Name Revision : Type} {n m : Nat}

/-- The authored portion of the existing input, before resolving its native
environment. Metadata is not a typing certificate. -/
structure Body (n : Nat) where
  sourceContext : Tower.Ctx n
  code : Code n
  resultType : Tower.Tm n
  initialState : Bool
  initialBranch : BranchTrace

def Body.bind (body : Body n) (environment : Sub Tower.Head n m) : Input n m where
  sourceContext := body.sourceContext
  code := body.code
  resultType := body.resultType
  environment := environment
  initialState := body.initialState
  initialBranch := body.initialBranch

abbrev Object (Name Revision : Type) (n : Nat) := NamedCode Name Revision (Body n)
abbrev Table (Name Revision : Type) (n m : Nat) :=
  ContextTable Name Revision (Sub Tower.Head n m)

/-- Pure resolution. No service or evaluation assembly is available here. -/
def resolveInput (table : Table Name Revision n m)
    (current : RevisionEnvironment Name Revision) (object : Object Name Revision n) :
    Option (Input n m) :=
  (resolve table current object.context).map object.code.bind

/-- Inspect an explicit finite native-variable footprint, including the
original source. This performs no native substitution or execution. -/
def inspectInput (table : Table Name Revision n m)
    (current : RevisionEnvironment Name Revision) (object : Object Name Revision n)
    (footprint : List (Fin n)) : Option (Body n × List (Fin n × Option (Tower.Tm m))) :=
  inspect table current (fun environment index => some (environment index)) object footprint

/-- The only runner used is the existing source runner. A missing context
is distinct from any stopped or empty result returned by that runner. -/
def run (assembly : Assembly) (table : Table Name Revision n m)
    (current : RevisionEnvironment Name Revision) (object : Object Name Revision n) :
    Option (List (SharedJudgmentServiceProgramBackend.Output m)) :=
  (resolveInput table current object).map (fun input => input.run assembly)

/-- Named resolution reaches the independently authored backend with exactly
the source, resolved substitution and original initial world. -/
theorem run_backend_iff (assembly : Assembly) (table : Table Name Revision n m)
    (current : RevisionEnvironment Name Revision) (object : Object Name Revision n)
    (environment : Sub Tower.Head n m)
    (found : resolve table current object.context = some environment)
    (outputs : List (SharedJudgmentServiceProgramBackend.Output m)) :
    run assembly table current object = some outputs ↔
      (object.code.bind environment).Completes assembly outputs := by
  simp only [run, resolveInput, found, Option.map_some, Option.some.injEq]
  rw [completes_iff_run]
  exact eq_comm

/-- Named contexts do not bypass the existing logical admission boundary. -/
theorem run_value_admitted {assembly : Assembly}
    (qualified : specification.Satisfies assembly)
    (table : Table Name Revision n m) (current : RevisionEnvironment Name Revision)
    (object : Object Name Revision n) (environment : Sub Tower.Head n m)
    (found : resolve table current object.context = some environment)
    (target : Tower.Ctx m)
    (admitted : (object.code.bind environment).Admitted assembly target)
    (outputs : List (SharedJudgmentServiceProgramBackend.Output m))
    (completed : run assembly table current object = some outputs)
    {output : SharedJudgmentServiceProgramBackend.Output m} {value : Tower.Tm m}
    (member : output ∈ outputs) (isValue : output.world.answer = .value value) :
    FormationSensitive.Judgment assembly.rules target value
      (subst environment object.code.resultType) := by
  exact admitted_completion_value qualified (completion := ⟨object.code.bind environment, outputs⟩)
    admitted ((run_backend_iff assembly table current object environment found outputs).mp completed)
    member isValue

/-- Native source substitution remains the existing capture-avoiding
operation. Its new typing context is explicit, not inferred from a name. -/
def Body.substitute {k : Nat} (body : Body n) (target : Tower.Ctx k)
    (environment : Sub Tower.Head n k) : Body k where
  sourceContext := target
  code := body.code.substitute environment
  resultType := subst environment body.resultType
  initialState := body.initialState
  initialBranch := body.initialBranch

/-- Precompose the actual substitutions stored under the same context
references. This is a semantic table map, not a runtime copying algorithm. -/
def precompose {k : Nat} (environment : Sub Tower.Head n k)
    (table : Table Name Revision k m) : Table Name Revision n m :=
  fun version => (table version).map (fun later => subComp later environment)

theorem resolve_precompose {k : Nat} (environment : Sub Tower.Head n k)
    (table : Table Name Revision k m) (current : RevisionEnvironment Name Revision)
    (reference : Reference Name Revision) :
    resolve (precompose environment table) current reference =
      (resolve table current reference).map (fun later => subComp later environment) := by
  cases reference <;> rfl

/-- Translating the scoped source or precomposing its named environment
gives identical complete runs. No cross-scope handler law is assumed: both
sides execute at the same final native scope. -/
theorem named_substitution_square {k : Nat} (assembly : Assembly)
    (table : Table Name Revision k m) (current : RevisionEnvironment Name Revision)
    (body : Body n) (target : Tower.Ctx k) (environment : Sub Tower.Head n k)
    (reference : Reference Name Revision) :
    run assembly table current ⟨body.substitute target environment, reference⟩ =
      run assembly (precompose environment table) current ⟨body, reference⟩ := by
  simp only [run, resolveInput, resolve_precompose]
  cases found : resolve table current reference with
  | none => rfl
  | some later =>
      simp only [Option.map_some, Input.run, Body.bind, Body.substitute,
        Code.run, Code.interpret_substitute]

/-- Fresh publication and a changed live selector preserve the entire old
backend computation when this object explicitly retained an occupied version. -/
theorem versioned_run_preserved [DecidableEq Name] [DecidableEq Revision]
    (assembly : Assembly) (table updated : Table Name Revision n m)
    (before after : RevisionEnvironment Name Revision)
    (body : Body n) (oldVersion newVersion : StoreReadToken Name Revision)
    (oldEnvironment newEnvironment : Sub Tower.Head n m)
    (found : table oldVersion = some oldEnvironment)
    (published : publishVersion? table newVersion newEnvironment = some updated) :
    run assembly updated after ⟨body, .versioned oldVersion⟩ =
      run assembly table before ⟨body, .versioned oldVersion⟩ := by
  have preserved := publication_preserves_existing table updated newVersion oldVersion
    newEnvironment oldEnvironment published found
  simp only [run, resolveInput, resolve, preserved, found]

/-- The same preservation law also keeps logical admission, because the
resolved native substitution is unchanged. It does not re-run the checker. -/
theorem versioned_admission_preserved [DecidableEq Name] [DecidableEq Revision]
    (assembly : Assembly) (target : Tower.Ctx m) (table updated : Table Name Revision n m)
    (after : RevisionEnvironment Name Revision) (body : Body n)
    (oldVersion newVersion : StoreReadToken Name Revision)
    (oldEnvironment newEnvironment : Sub Tower.Head n m)
    (found : table oldVersion = some oldEnvironment)
    (published : publishVersion? table newVersion newEnvironment = some updated)
    (admitted : (body.bind oldEnvironment).Admitted assembly target) :
    ∃ input, resolveInput updated after ⟨body, .versioned oldVersion⟩ = some input ∧
      input.Admitted assembly target := by
  refine ⟨body.bind oldEnvironment, ?_, admitted⟩
  have preserved := publication_preserves_existing table updated newVersion oldVersion
    newEnvironment oldEnvironment published found
  simp only [resolveInput, resolve, preserved, Option.map_some]

namespace Controls

open NativeWireDataDenotation
open Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation

def body : Body 4 where
  sourceContext := NativeMatchedTransportDenotation.parameterContext
  code := .native (.returnValue parameterTerm)
  resultType := NativeWireData.dataType
  initialState := false
  initialBranch := []

theorem bind_parameter (value : Value) :
    body.bind (fillParameter value) = SharedJudgmentPublicContext.Controls.parameterInput value := rfl

def oldVersion : StoreReadToken String Nat := ⟨"C", 0⟩
def newVersion : StoreReadToken String Nat := ⟨"C", 1⟩
def before : RevisionEnvironment String Nat := ⟨fun _ => 0⟩
def after : RevisionEnvironment String Nat := ⟨fun _ => 1⟩
def oldTable : Table String Nat 4 3 :=
  writeSource (fun _ => none) (oldVersion, fillParameter (.natural 2))
def newTable : Table String Nat 4 3 :=
  writeSource oldTable (newVersion, fillParameter (.natural 3))
def stable : Object String Nat 4 := ⟨body, .versioned oldVersion⟩
def live : Object String Nat 4 := ⟨body, .live "C"⟩

theorem accepted_publication :
    publishVersion? oldTable newVersion (fillParameter (.natural 3)) = some newTable := by
  apply (publishVersion?_eq_some_iff _ _ _ _).mpr
  exact ⟨by decide, rfl⟩

theorem old_binding_resolves : oldTable oldVersion = some (fillParameter (.natural 2)) := by
  simp [oldTable, writeSource]

theorem stable_preserves_backend :
    run common newTable after stable = run common oldTable before stable :=
  versioned_run_preserved common oldTable newTable before after body oldVersion newVersion
    (fillParameter (.natural 2)) (fillParameter (.natural 3))
    old_binding_resolves accepted_publication

theorem stable_remains_admitted :
    ∃ input, resolveInput newTable after stable = some input ∧
      input.Admitted common OpaqueRelatorScopedComputation.Common.context := by
  exact versioned_admission_preserved common OpaqueRelatorScopedComputation.Common.context
    oldTable newTable after body oldVersion newVersion (fillParameter (.natural 2))
    (fillParameter (.natural 3)) old_binding_resolves accepted_publication
    (SharedJudgmentPublicContext.Controls.parameter_admitted _)

/-- The unchanged public code object has different actual backend outputs
when its deliberately live name resolves to the new typed binding. -/
theorem live_update_changes_output : run common oldTable before live ≠ run common newTable after live := by
  have different := (SharedJudgmentPublicContext.Controls.same_source_different_environment
    (.natural 2) (.natural 3) (by decide)).2
  change some ((SharedJudgmentPublicContext.Controls.parameterInput (.natural 2)).run common) ≠
    some ((SharedJudgmentPublicContext.Controls.parameterInput (.natural 3)).run common)
  exact fun equal => different (Option.some.inj equal)

/-- A name alone does not supply a context or authorize evaluation. -/
theorem missing_context_is_not_empty_success :
    run (m := 3) common (fun _ => none) before live = none ∧
      run (m := 3) common (fun _ => none) before live ≠ some [] := by
  constructor <;> simp [run, resolveInput, resolve, live]

end Controls

#print axioms run_backend_iff
#print axioms run_value_admitted
#print axioms named_substitution_square
#print axioms versioned_run_preserved
#print axioms versioned_admission_preserved
#print axioms Controls.stable_preserves_backend
#print axioms Controls.stable_remains_admitted
#print axioms Controls.live_update_changes_output

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNamedContext
