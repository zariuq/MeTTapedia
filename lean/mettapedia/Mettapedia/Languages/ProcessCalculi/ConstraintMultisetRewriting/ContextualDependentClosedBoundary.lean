import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaLongReflection

/-!
# The symbolic/closed boundary of the dependent unifier

A store of the typed βη frame has a **closed solution** when it has a solution out of the empty
frame (`ClosedSolvable`). Its solvability (`Frames.Solvable`) is symbolic: a solution into some
later frame, whose variables are still open.

What the unifier's answers say:

* **A principal answer is symbolic**: it factors every solution into every later frame. Whether the
  store has a closed solution is then exactly whether the answer's frame has a closed point
  (`principal_closed_iff`). This is the only question that needs a closed witness.
* **A certified refutation is symbolic**: no solution in any later frame, so in particular no
  closed one (`not_closedSolvable_of_not_solvable`).
* **Pending asserts nothing**: a suspended run can be the run of a refutable store, and a solvable
  store can have no closed solution (the controls).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentClosedBoundary

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- A solution out of the empty frame: every variable of the store's frame is given a closed
value. -/
def ClosedSolvable {Γ : Context S.R} (K : EquationStore (TotalTerm Γ)) : Prop :=
  ∃ σ : empty S.R ⟶ Γ, (frames S.levels).Models σ K

/-- A frame has a closed point: a substitution of closed values for all its variables. -/
def ClosedPoint (m : Context S.R) : Prop := Nonempty (empty S.R ⟶ m)

theorem ClosedSolvable.solvable {Γ : Context S.R} {K : EquationStore (TotalTerm Γ)}
    (closed : ClosedSolvable K) : (frames S.levels).Solvable K :=
  let ⟨σ, solved⟩ := closed
  ⟨_, σ, solved⟩

/-- **A certified refutation excludes closed solutions.** -/
theorem not_closedSolvable_of_not_solvable {Γ : Context S.R} {K : EquationStore (TotalTerm Γ)}
    (refuted : ¬ (frames S.levels).Solvable K) : ¬ ClosedSolvable K :=
  fun closed => refuted closed.solvable

/-- **Closed solvability under a principal answer is closed inhabitation of its frame.** -/
theorem principal_closed_iff {a m : Context S.R} {K : EquationStore (TotalTerm a)} {σ : m ⟶ a}
    (principal : (frames S.levels).Principal (a := a) (m := m) K σ) :
    ClosedSolvable K ↔ ClosedPoint m := by
  constructor
  · rintro ⟨τ, solved⟩
    obtain ⟨residual, _⟩ := principal.factors _ τ solved
    exact ⟨residual⟩
  · rintro ⟨ρ⟩
    exact ⟨ρ ≫ σ, Frames.models_comp principal.sound ρ⟩

end ContextualDependentClosedBoundary
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
