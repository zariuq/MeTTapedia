import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingWorklist
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverSelect
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameRefutation

/-!
# Executable worklist with typed fresh-helper frame changes

Recoverable bindings, constructor imitation, flexible pairs and same-hole equalizers share one queue
driver. A fresh helper replaces its selected declaration, while all other
identities retain their interfaces. Equal maps still discharge their
equation. Each choice retains its typed case and exact queue location.
Fuel exhaustion and cases not implemented here retain the actual
equations. Rigid clashes, an unavailable ambient variable and finite-pattern
occurs obstructions return certified refutations. In the checked structural
fragment, contradictory first-order shapes are also certified refusals.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameWorklist

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualFrameUpdate

variable {S : Signature} {V : Type} [DecidableEq V] [DecidableEq S.Srt]
  [∀ sort, DecidableEq (S.Op sort)] {source : V → MetaArity S}

def ofBinding {problem : Problem source} (update : ContextualBindingWorklist.Update problem) : Update problem :=
  ⟨V, inferInstance, source, update.answer, update.remaining, update.valid⟩

def choose (problem : Problem source) : Option (Update problem) :=
  (ContextualSolverSelect.choose problem).map ContextualSolverCases.Choice.perform

def identity (problem : Problem source) : Update problem :=
  ofBinding (ContextualBindingWorklist.identity problem)

inductive Result (problem : Problem source)
  | residual (update : Update problem)
  | refuted (proof : ∀ {Next : Type} (next : Next → MetaArity S)
      (candidate : Assignment source next), ¬ Models candidate problem)

/-- Change only the proven equation-list presentation. No solver data or
residual equation is removed by this transport. -/
def Result.cast {first second : Problem source} (same : first = second) (result : Result first) : Result second :=
  same ▸ result

abbrev Refuter (S : Signature) :=
  {Variables : Type} → [DecidableEq Variables] → (declaration : Variables → MetaArity S) →
    (problem : Problem declaration) → Option (ContextualEquationRefutation.Refutation problem)

def normalizationUpdate {problem remaining : Problem source}
    (computed : ContextualRigidSolver.normalize problem = some remaining) : Update problem :=
  ⟨V, inferInstance, source, generator source, remaining, ContextualRigidSolver.normalization_reduction computed⟩

def Result.after {problem : Problem source} (first : Update problem) : Result first.remaining → Result problem
  | .residual last => .residual (first.then last)
  | .refuted impossible => .refuted fun next candidate solved => by
      obtain ⟨residual, restSolved, _⟩ := first.valid.complete next candidate solved
      exact impossible next residual restSolved

def runWithRefuter (refuter : Refuter S) : Nat → {Variables : Type} → [DecidableEq Variables] →
    (declaration : Variables → MetaArity S) → (problem : Problem declaration) → Result problem
  | 0, _, equality, declaration, problem => by
      letI := equality
      exact .residual (identity problem)
  | fuel + 1, Variables, equality, declaration, problem => by
      letI := equality
      exact match computed : ContextualRigidSolver.normalize problem with
      | none => .refuted fun _ candidate => ContextualRigidSolver.refused_has_no_solution computed candidate
      | some normalized =>
          let normalizedUpdate := normalizationUpdate computed
          match refuter declaration normalized with
          | some impossible => .refuted fun next candidate solved => by
              obtain ⟨residual, restSolved, _⟩ := normalizedUpdate.valid.complete next candidate solved
              exact impossible.noModel next residual restSolved
          | none =>
              match choose normalized with
              | none => .residual normalizedUpdate
              | some update =>
                  let first := normalizedUpdate.then update
                  letI := update.equality
                  Result.after first (runWithRefuter refuter fuel update.declaration update.remaining)

def run (fuel : Nat) {Variables : Type} [DecidableEq Variables]
    (declaration : Variables → MetaArity S) (problem : Problem declaration) : Result problem :=
  runWithRefuter (fun declaration problem => ContextualFrameRefutation.choose (S := S) (source := declaration) problem)
    fuel declaration problem

omit [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)] in
theorem refuter_none_of_model (refuter : Refuter S) (problem : Problem source)
    {Next : Type} (next : Next → MetaArity S) (candidate : Assignment source next) (solved : Models candidate problem) :
    refuter source problem = none := by
  cases computed : refuter source problem with
  | none => rfl
  | some impossible => exact False.elim (impossible.noModel next candidate solved)

theorem runWithRefuter_normalized (refuter : Refuter S) (fuel : Nat) (problem remaining : Problem source)
    (normalized : ContextualRigidSolver.normalize problem = some remaining) (unrefuted : refuter source remaining = none) :
    runWithRefuter refuter (fuel + 1) source problem =
      match choose remaining with
      | none => .residual (normalizationUpdate normalized)
      | some update => by
          let _ := update.equality
          exact Result.after ((normalizationUpdate normalized).then update)
            (runWithRefuter refuter fuel update.declaration update.remaining) := by
  simp only [runWithRefuter]
  split
  · rename_i computed
    cases normalized.symm.trans computed
  · rename_i rest computed
    have same : rest = remaining := Option.some.inj (computed.symm.trans normalized)
    subst rest
    split
    · rename_i impossible computed
      cases unrefuted.symm.trans computed
    · rfl

theorem runWithRefuter_agrees_on_model (first second : Refuter S) (fuel : Nat) :
    ∀ {Names : Type} [DecidableEq Names] (declaration : Names → MetaArity S) (problem : Problem declaration)
      {Next : Type} (next : Next → MetaArity S) (candidate : Assignment declaration next), Models candidate problem →
      runWithRefuter first fuel declaration problem = runWithRefuter second fuel declaration problem := by
  induction fuel with
  | zero => intro Names equality declaration problem Next next candidate solved; rfl
  | succ fuel earlier =>
      intro Names equality declaration problem Next next candidate solved
      cases normalized : ContextualRigidSolver.normalize problem with
      | none => exact False.elim (ContextualRigidSolver.refused_has_no_solution normalized candidate solved)
      | some remaining =>
          have equivalent := ContextualRigidSolver.models_normalize candidate problem
          rw [normalized] at equivalent
          have remainingSolved := equivalent.mpr solved
          have firstNone := refuter_none_of_model first remaining next candidate remainingSolved
          have secondNone := refuter_none_of_model second remaining next candidate remainingSolved
          rw [runWithRefuter_normalized first fuel problem remaining normalized firstNone,
            runWithRefuter_normalized second fuel problem remaining normalized secondNone]
          cases selected : choose remaining with
          | none => rfl
          | some update =>
              let _ := update.equality
              obtain ⟨residual, residualSolved, _⟩ := update.valid.complete next candidate remainingSolved
              exact congrArg (Result.after ((normalizationUpdate normalized).then update))
                (earlier update.declaration update.remaining next residual residualSolved)

theorem run_eq_local_on_model (fuel : Nat) (problem : Problem source)
    {Next : Type} (next : Next → MetaArity S) (candidate : Assignment source next) (solved : Models candidate problem) :
    run fuel source problem =
      runWithRefuter (fun declaration problem => ContextualEquationRefutation.choose (S := S) (source := declaration) problem)
        fuel source problem :=
  runWithRefuter_agrees_on_model _ _ fuel source problem next candidate solved

/-- Every actual model survives a bounded run as a model of its returned
residual, with its components factoring through the computed assignment. -/
theorem preserves_every_solution (fuel : Nat) (problem : Problem source)
    {Next : Type} (next : Next → MetaArity S) (candidate : Assignment source next)
    (solved : Models candidate problem) :
    ∃ update, run fuel source problem = .residual update ∧
      ∃ residual : Assignment update.declaration next, Models residual update.remaining ∧
        ∀ identity, candidate identity = instantiate residual (update.answer identity) := by
  cases computed : run fuel source problem with
  | refuted impossible => exact False.elim (impossible next candidate solved)
  | residual update => exact ⟨update, rfl, update.valid.complete next candidate solved⟩

/-- Continue an actual solver result with additional equations in its
original declaration family. An unfinished prefix keeps its residual queue;
the new equations travel through the returned assignment before solving.
The resulting update still certifies the full original concatenation. -/
def Result.resumeWithRefuter {problem : Problem source} (refuter : Refuter S) (prior : Result problem) (fuel : Nat)
    (extra : Problem source) : Result (problem ++ extra) :=
  match prior with
  | .refuted impossible => .refuted fun next candidate solved =>
      impossible next candidate ((models_append candidate problem extra).mp solved).1
  | .residual update => by
      letI := update.equality
      exact Result.after (update.keep_right extra)
        (runWithRefuter refuter fuel update.declaration (update.remaining ++ mapProblem update.answer extra))

def Result.resume {problem : Problem source} (prior : Result problem) (fuel : Nat)
    (extra : Problem source) : Result (problem ++ extra) :=
  prior.resumeWithRefuter
    (fun declaration problem => ContextualFrameRefutation.choose (S := S) (source := declaration) problem) fuel extra

/-- A two-stage execution of the same driver. The split is an explicit
input prefix, not permission to omit it from the resulting equation store. -/
def runIncremental (firstFuel nextFuel : Nat) (past extra : Problem source) : Result (past ++ extra) :=
  (run firstFuel source past).resume nextFuel extra

omit [DecidableEq V] in
theorem resume_preserves_every_solution {past : Problem source} (prior : Result past)
    (fuel : Nat) (extra : Problem source) {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment source next) (solved : Models candidate (past ++ extra)) :
    ∃ update, prior.resume fuel extra = .residual update ∧
      ∃ residual : Assignment update.declaration next, Models residual update.remaining ∧
        ∀ identity, candidate identity = instantiate residual (update.answer identity) := by
  cases computed : prior.resume fuel extra with
  | refuted impossible => exact False.elim (impossible next candidate solved)
  | residual update => exact ⟨update, rfl, update.valid.complete next candidate solved⟩

omit [DecidableEq V] in
theorem resumed_zero_keeps_the_actual_residual {past : Problem source} (update : Update past)
    (extra : Problem source) :
    ∃ result, (Result.residual update).resume 0 extra = .residual result ∧
      HEq result.remaining (update.remaining ++ mapProblem update.answer extra) := by
  let _ := update.equality
  let later : Update ((update.keep_right extra).remaining) := @identity S update.Variables update.equality update.declaration _
  refine ⟨(update.keep_right extra).then later, rfl, ?_⟩
  rfl

omit [DecidableEq V] in
theorem Result.resume_agrees_on_model (first second : Refuter S) {past : Problem source} (prior : Result past)
    (fuel : Nat) (extra : Problem source) {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment source next) (solved : Models candidate (past ++ extra)) :
    prior.resumeWithRefuter first fuel extra = prior.resumeWithRefuter second fuel extra := by
  cases prior with
  | refuted proof => rfl
  | residual update =>
      let _ := update.equality
      obtain ⟨residual, remainingSolved, _⟩ := (update.keep_right extra).valid.complete next candidate solved
      exact congrArg (Result.after (update.keep_right extra))
        (runWithRefuter_agrees_on_model first second fuel update.declaration _ next residual remainingSolved)

theorem runIncremental_eq_local_on_model (firstFuel nextFuel : Nat) (past extra : Problem source)
    {Next : Type} (next : Next → MetaArity S) (candidate : Assignment source next)
    (solved : Models candidate (past ++ extra)) :
    runIncremental firstFuel nextFuel past extra =
      (runWithRefuter (fun declaration problem => ContextualEquationRefutation.choose
        (S := S) (source := declaration) problem) firstFuel source past).resumeWithRefuter
        (fun declaration problem => ContextualEquationRefutation.choose
          (S := S) (source := declaration) problem) nextFuel extra := by
  unfold runIncremental
  rw [run_eq_local_on_model firstFuel past next candidate ((models_append _ _ _).mp solved).1]
  exact Result.resume_agrees_on_model _ _ _ nextFuel extra next candidate solved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameWorklist
