import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FamilySolver

/-!
# Stopped runs of the families rules, as exact transitions

The rounds of `familySolver` read as a solver of exact transitions over the tree's frames (`familyTransitions`, a
`UnificationWithLevels.Solver`): a step is a progress of the round, and there is no refutation. Every step is exact
(through the driver's updates).

* **Every run from the fragment stays in it** (`reaches_inFragment`).
* **Every stopped run from the fragment is empty** (`stopped_empty`): a nonempty store of the fragment always has a
  step. So it is solved, and its composite answer is principal (`stopped_principal`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

section General

universe uO uT uH

/-- **An invariant kept by every step is kept by every run.** -/
theorem reaches_preserves {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} {X : Frames Tm Hom}
    {P : UnificationWithLevels.Solver X} (I : {a : Obj} → EquationStore (Tm a) → Prop)
    (keeps : ∀ {a m : Obj} {S : EquationStore (Tm a)} {σ : Hom a m} {S' : EquationStore (Tm m)},
      P.Step S m σ S' → I S → I S')
    {a m : Obj} {S : EquationStore (Tm a)} {σ : Hom a m} {R : EquationStore (Tm m)}
    (run : P.Reaches S m σ R) : I S → I R := by
  induction run with
  | refl _ => exact id
  | step first _ ih => exact fun inside => ih (keeps first inside)

end General

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L} [DecidableEq Head]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- **A step of the families rules**: a progress of their round, along its update. -/
inductive FamilyStep : {a : Context S.R} → EquationStore (TotalTerm a) → (m : Context S.R) → (m ⟶ a) →
    EquationStore (TotalTerm m) → Prop
  | round {a : Context S.R} {problem : EquationStore (TotalTerm a)} {update : Update S.levels problem}
      {smaller : ContextualDependentWorklist.Below (storeRank update.remaining) (storeRank problem)} :
      familyRound facts roots heads algebra rigid complete problem = .progress update smaller →
      FamilyStep problem update.target update.answer update.remaining

/-- **The families rules as exact transitions.** -/
def familyTransitions : UnificationWithLevels.Solver (frames S.levels) where
  Step := FamilyStep facts roots heads algebra rigid complete
  step_exact := by
    intro a m problem σ remaining step
    cases step with
    | round _ => exact DependentFibre.update_exact _
  Refutes := fun _ _ => False
  refutes_sound := fun absurd => absurd.elim

/-- **Every run from the fragment stays in it.** -/
theorem reaches_inFragment {a m : Context S.R} {problem : EquationStore (TotalTerm a)} {σ : m ⟶ a}
    {R : EquationStore (TotalTerm m)} :
    (familyTransitions facts roots heads algebra rigid complete).Reaches problem m σ R →
      InFragment problem → InFragment R :=
  reaches_preserves (fun store => InFragment store) fun step inside => by
    cases step with
    | round progressed => exact familyRound_stable facts roots heads algebra rigid complete inside progressed

/-- **Every stopped run from the fragment is empty.** -/
theorem stopped_empty {a m : Context S.R} {problem : EquationStore (TotalTerm a)} {σ : m ⟶ a}
    {R : EquationStore (TotalTerm m)} (inside : InFragment problem)
    (run : (familyTransitions facts roots heads algebra rigid complete).Reaches problem m σ R)
    (stopped : (familyTransitions facts roots heads algebra rigid complete).Stopped R) : R = [] := by
  have insideR := reaches_inFragment facts roots heads algebra rigid complete run inside
  by_contra nonempty
  have notStuck := familyRound_ne_stuck facts roots heads algebra rigid complete insideR nonempty
  cases h : familyRound facts roots heads algebra rigid complete R with
  | progress update smaller => exact stopped.1 update.target update.answer update.remaining (.round h)
  | refuted absent => exact familyRound_ne_refuted facts roots heads algebra rigid complete R absent h
  | stuck => exact notStuck h

/-- **A stopped run from the fragment ends with a principal answer.** -/
theorem stopped_principal {a m : Context S.R} {problem : EquationStore (TotalTerm a)} {σ : m ⟶ a}
    {R : EquationStore (TotalTerm m)} (inside : InFragment problem)
    (run : (familyTransitions facts roots heads algebra rigid complete).Reaches problem m σ R)
    (stopped : (familyTransitions facts roots heads algebra rigid complete).Stopped R) :
    (frames S.levels).Principal problem σ := by
  have empty := stopped_empty facts roots heads algebra rigid complete inside run stopped
  subst empty
  exact solved_principal run

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
