import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentScope
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDispatch
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentParameterExchange

/-!
# Solution-factorizing updates for equations under rigid parameters

Local parameters are abstracted with the checked universe choices before
the existing queue dispatcher runs. Closing preserves the interpretation
under every outer substitution. Therefore the returned update factors all
solutions of the original scoped constraints, not merely their displayed
lambda encodings. An unavailable universe join leaves the scoped input
unresolved; it cannot manufacture a negative judgment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentScopedDispatch

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentScope

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}

def Holds {Γ Δ : Context rules} (problem : List (Scoped Γ)) (solution : Δ ⟶ Γ) : Prop :=
  ∀ constraint ∈ problem, constraint.Holds solution

structure Closed (levels : LevelModel rules L) {Γ : Context rules} (problem : List (Scoped Γ)) where
  equations : EquationStore (TotalTerm Γ)
  models : ∀ {Δ : Context rules} (solution : Δ ⟶ Γ),
    (frames levels).Models solution equations ↔ Holds problem solution

variable (levels : LevelModel rules L) (choices : ExecutableChecking.HeadChoices rules)

def closeAll {Γ : Context rules} : (problem : List (Scoped Γ)) → Option (Closed levels problem)
  | [] => some ⟨[], fun solution => by simp only [Frames.Models, Holds, List.not_mem_nil, false_implies, implies_true]⟩
  | constraint :: rest => do
      match computed : constraint.closeWith levels choices with
      | none => none
      | some active =>
          let closed ← closeAll rest
          return ⟨active.equation :: closed.equations, fun solution => by
            have first := (Active.holds_iff_models levels active solution).symm.trans
              (Scoped.closeWith_holds_iff levels choices constraint computed solution)
            simp only [Frames.Models, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
              false_implies, implies_true, and_true] at first
            simp only [Frames.Models, Holds, List.mem_cons, forall_eq_or_imp]
            exact and_congr first (closed.models solution)⟩

theorem closeAll_exists
    (total : ∀ first second, rules.isUniverse first → rules.isUniverse second →
      ∃ result, choices.join first second = some result)
    {Γ : Context rules} (problem : List (Scoped Γ)) :
    ∃ closed, closeAll levels choices problem = some closed := by
  induction problem with
  | nil => exact ⟨_, rfl⟩
  | cons constraint rest ih =>
      obtain ⟨active, activeClosed⟩ := Scoped.closeWith_exists levels choices total constraint
      obtain ⟨closed, restClosed⟩ := ih
      unfold closeAll
      split
      · rename_i impossible
        rw [activeClosed] at impossible
        cases impossible
      · rw [restClosed]
        exact ⟨_, rfl⟩

structure Result {Γ : Context rules} (problem : List (Scoped Γ)) where
  closed : Closed levels problem
  update : Update levels closed.equations

namespace Result

variable {levels choices}

theorem sound {Γ : Context rules} {problem : List (Scoped Γ)} (result : Result levels problem)
    {Δ : Context rules} (residual : Δ ⟶ result.update.target)
    (solved : (frames levels).Models residual result.update.remaining) :
    Holds problem (residual ≫ result.update.answer) :=
  (result.closed.models _).mp (result.update.sound Δ residual solved)

theorem factors {Γ : Context rules} {problem : List (Scoped Γ)} (result : Result levels problem)
    {Δ : Context rules} (solution : Δ ⟶ Γ) (solved : Holds problem solution) :
    ∃ residual : Δ ⟶ result.update.target,
      (frames levels).Models residual result.update.remaining ∧
      ∀ term : TotalTerm Γ,
        (frames levels).E (term.reindex solution) (term.reindex (residual ≫ result.update.answer)) :=
  result.update.complete Δ solution ((result.closed.models solution).mpr solved)

theorem completed {Γ : Context rules} {problem : List (Scoped Γ)} (result : Result levels problem)
    (finished : result.update.remaining = []) :
    Holds problem result.update.answer ∧
      ∀ (Δ : Context rules) (solution : Δ ⟶ Γ), Holds problem solution →
        ∃ residual : Δ ⟶ result.update.target,
          ∀ term : TotalTerm Γ,
            (frames levels).E (term.reindex solution) (term.reindex (residual ≫ result.update.answer)) := by
  have principal := result.update.completed finished
  refine ⟨(result.closed.models _).mp principal.sound, fun Δ solution solved => ?_⟩
  exact principal.factors Δ solution ((result.closed.models solution).mpr solved)

theorem fixed_point_solutions_iff {Γ : Context rules} {problem : List (Scoped Γ)}
    (result : Result levels problem) (point : Context rules) :
    (∃ solution : point ⟶ Γ, Holds problem solution) ↔
      ∃ residual : point ⟶ result.update.target, (frames levels).Models residual result.update.remaining :=
  (exists_congr fun solution => (result.closed.models solution).symm).trans
    (result.update.fixed_point_solutions_iff point)

def rephrase {Γ : Context rules} {original transformed : List (Scoped Γ)}
    (result : Result levels transformed)
    (same : ∀ {Δ : Context rules} (solution : Δ ⟶ Γ), Holds original solution ↔ Holds transformed solution) :
    Result levels original :=
  ⟨⟨result.closed.equations, fun solution => (result.closed.models solution).trans (same solution).symm⟩,
    result.update⟩

end Result

variable {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (declared : DeclaredTypesFormed S.R)
variable (headChoices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

def solveNewest (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ)
    (problem : List (Scoped (extend Γ type))) : Option (Result S.levels problem) := do
  let closed ← closeAll S.levels headChoices problem
  return ⟨closed, ContextualDependentDispatch.step facts roots heads algebra declared headChoices reducer
    fuel type closed.equations⟩

/-- Reorder two independent rigid parameters before closing. The returned
factorization still concerns the original scoped problem. -/
def solveExchanged (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ)
    (first next : TypeOver (extend Γ type))
    (active : Active (ContextualDependentParameterExchange.context first next)) :
    Option (Result S.levels [ContextualDependentParameterExchange.problem first next active]) := do
  let result ← solveNewest facts roots heads algebra declared headChoices reducer fuel type
    [ContextualDependentParameterExchange.exchanged first next active]
  return result.rephrase (by
    intro Δ solution
    constructor
    · intro solved constraint member
      obtain rfl := List.mem_singleton.mp member
      exact (ContextualDependentParameterExchange.exchanged_holds_iff solution first next active).mpr
        (solved _ (List.mem_singleton_self _))
    · intro solved constraint member
      obtain rfl := List.mem_singleton.mp member
      exact (ContextualDependentParameterExchange.exchanged_holds_iff solution first next active).mp
        (solved _ (List.mem_singleton_self _)))

end ContextualDependentScopedDispatch
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
