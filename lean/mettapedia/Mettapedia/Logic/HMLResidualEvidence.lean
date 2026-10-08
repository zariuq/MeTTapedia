import Mettapedia.Logic.FundedHMLVerdicts
import Mathlib.CategoryTheory.Types.Basic

/-!
# Residual calculation evidence at actual current configurations

The family is specified by the independent execution of each configuration's
own pending program and current stack. Actual occurrence paths transport that
evidence by the earned execution invariant. The witness retains its complete
output stack, and identity and composition laws give a genuine dependent
operational action on the existing occurrence category.

This construction concerns residual calculation evidence in the declared
instruction machine. It does not update an arbitrary initially supplied
predicate, nor lower its action to a process-calculus implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ModalMuCalculus.StackInspection.Funded

open Inspection
open _root_.CategoryTheory
open Mettapedia.GSLT.Causality.OccurrenceHistory

universe u v

variable {State : Type u} {Action : Type v} {n : Nat}

def ResidualEvidence (environment : BooleanEnv State n) (configuration : Configuration State n) : Type :=
  {output : List Bool // execute environment configuration.pending configuration.stack = some output}

def transportResidual (environment : BooleanEnv State n)
    {source target : Configuration State n} (path : Path environment source target)
    (evidence : ResidualEvidence environment source) : ResidualEvidence environment target :=
  ⟨evidence.val, (path_execution environment path).symm.trans evidence.property⟩

theorem transportResidual_output (environment : BooleanEnv State n)
    {source target : Configuration State n} (path : Path environment source target)
    (evidence : ResidualEvidence environment source) :
    (transportResidual environment path evidence).val = evidence.val := rfl

theorem transportResidual_identity (environment : BooleanEnv State n)
    (source : Configuration State n) (evidence : ResidualEvidence environment source) :
    transportResidual environment (.refl source) evidence = evidence := Subtype.ext rfl

theorem transportResidual_composition (environment : BooleanEnv State n)
    {source middle target : Configuration State n}
    (first : Path environment source middle) (second : Path environment middle target)
    (evidence : ResidualEvidence environment source) :
    transportResidual environment (OccurrencePath.append first second) evidence =
      transportResidual environment second (transportResidual environment first evidence) := Subtype.ext rfl

def residualEvidenceFunctor (environment : BooleanEnv State n) :
    OccurrenceCat (presentation environment) ⥤ Type where
  obj configuration := ResidualEvidence environment configuration
  map path := TypeCat.ofHom (transportResidual environment path)
  map_id configuration := by
    ext evidence
    exact transportResidual_identity environment configuration evidence
  map_comp first second := by
    ext evidence
    exact transportResidual_composition environment first second evidence

def compiledResidualEvidence (presentation : SuccessorPresentation State Action)
    (formula : Formula Action n) (admitted : formula.isHML = true)
    (environment : BooleanEnv State n) (state : State) (stack : List Bool) (budget spent : Nat) :
    ResidualEvidence environment ⟨compile presentation formula admitted state, stack, budget, spent⟩ :=
  ⟨(inspect presentation formula admitted environment state).1 :: stack,
    execute_compiled presentation formula admitted environment state stack⟩

/-- Every supplied actual prefix earns evidence for its current residual
configuration, rather than copying an initial-state predicate to that state. -/
theorem compiled_current_evidence (presentation : SuccessorPresentation State Action)
    (formula : Formula Action n) (admitted : formula.isHML = true)
    (environment : BooleanEnv State n) (state : State) (stack : List Bool) (budget spent : Nat)
    {target : Configuration State n}
    (path : Path environment ⟨compile presentation formula admitted state, stack, budget, spent⟩ target) :
    execute environment target.pending target.stack =
      some ((inspect presentation formula admitted environment state).1 :: stack) :=
  (transportResidual environment path
    (compiledResidualEvidence presentation formula admitted environment state stack budget spent)).property

theorem completed_evidence_readout (environment : BooleanEnv State n)
    (target : Configuration State n) (complete : target.pending = [])
    (evidence : ResidualEvidence environment target) : evidence.val = target.stack := by
  have computed := evidence.property
  simp only [complete, execute] at computed
  exact (Option.some.inj computed).symm

end Mettapedia.Logic.ModalMuCalculus.StackInspection.Funded
