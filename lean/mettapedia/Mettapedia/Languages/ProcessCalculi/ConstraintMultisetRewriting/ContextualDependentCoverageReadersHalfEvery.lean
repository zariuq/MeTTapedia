import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCoverageReadersHalfChain
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance4EveryClosure

/-!
# The readers' half of coverage for the every-rule family

The every-rule round fires wherever the dead-binder round does, so every named reader of the dead-binder family reads
it too. Its own reader is **the front reader** (`everyRound_not_stuck_of_front`): the round is not stuck on a store one
of whose rotations has a first equation with a dead binder, read without which the round is not stuck. Reading a dead
binder removes one abstraction from the left sides of the store (`deadDepth_dead`), so the recursion depth of the
reduced store is one less, and the front reader applies again behind it.

`EveryReads` closes the named readers under the front reader, and **firing follows from eventual every-reading**
(`firing_of_everyReads`, `tower_every_decided_of_everyReads`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCoverageReadersHalf

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentIntersectionGeneral ContextualDependentMillerClosure
open ContextualDependentConversionBudget ContextualDependentAcceptance4

/-! ## Depth -/

section Depth

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

omit [UniverseLevel.LevelOrder L] in
/-- A renaming keeps the leading abstractions of a code. -/
theorem lamDepth_rename {n m : Nat} (ρ : Ren n m) (t : Tm Head n) :
    lamDepth (Presentation.rename ρ t) = lamDepth t := by
  induction t generalizing m with
  | lam body ih => simp only [Presentation.rename, lamDepth, ih]
  | _ => rfl

theorem deadDepth_perm {Θ : Context S.R} {problem problem' : EquationStore (TotalTerm Θ)}
    (perm : problem.Perm problem') : deadDepth problem = deadDepth problem' :=
  (perm.map _).sum_eq

/-- **Reading a dead binder removes one abstraction from the left sides of the store.** -/
theorem deadDepth_dead {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (dead : DeadBinder equation) : deadDepth (equation :: rest) = deadDepth (dead.reduced :: rest) + 1 := by
  simp only [deadDepth, List.map_cons, List.sum_cons, dead.leftTerm, lamDepth, lamDepth_rename]
  omega

end Depth

/-! ## The front reader -/

section General

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)
  (strengthening : EqualStrengthening S.R)

/-- The rotations in turn are not stuck once one of them is not. -/
theorem everySearch_not_stuck (fuel : Nat) {Θ : Context S.R}
    (inner : (stored : EquationStore (TotalTerm Θ)) →
      Round S.levels (weightRank facts roots heads algebra rigid complete) stored)
    (problem : EquationStore (TotalTerm Θ)) {k : Nat}
    (fires : everyAt facts roots heads algebra rigid complete declared choices reducer strengthening fuel inner
      (problem.rotate k) ≠ .stuck) :
    ∀ rotations : List Nat, k ∈ rotations →
      everySearch facts roots heads algebra rigid complete declared choices reducer strengthening fuel inner problem
        rotations ≠ .stuck
  | [], member => absurd member List.not_mem_nil
  | j :: js, member => by
      simp only [everySearch]
      cases computed : everyAt facts roots heads algebra rigid complete declared choices reducer strengthening fuel
          inner (problem.rotate j) with
      | stuck =>
          have other : k ≠ j := by
            rintro rfl
            exact fires computed
          exact everySearch_not_stuck fuel inner problem fires js ((List.mem_cons.mp member).resolve_left other)
      | progress update smaller =>
          intro stuck
          cases stuck
      | refuted absent =>
          intro stuck
          cases stuck

/-- **The front reader**: the every-rule round is not stuck on a store one of whose rotations has a first equation with
a dead binder, read without which the every-rule round is not stuck. -/
theorem everyRound_not_stuck_of_front (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    {k : Nat} (bound : k < problem.length) {equation : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (rotated : problem.rotate k = equation :: rest) {dead : DeadBinder equation}
    (read : deadBinder facts roots heads algebra declared choices reducer fuel equation = some dead)
    (behind : everyRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel (dead.reduced :: rest) ≠ .stuck) :
    everyRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ≠ .stuck := by
  have depth : deadDepth problem = deadDepth (dead.reduced :: rest) + 1 := by
    rw [deadDepth_perm (List.rotate_perm problem k).symm, rotated, deadDepth_dead dead]
  have fires : everyAt facts roots heads algebra rigid complete declared choices reducer strengthening fuel
      (fun stored => everyRoundAt facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening fuel (deadDepth (dead.reduced :: rest)) stored)
      (problem.rotate k) ≠ .stuck := by
    rw [rotated]
    simp only [everyAt, read]
    unfold undeadRound
    rw [Ne, transferRound_stuck]
    exact behind
  unfold everyRound
  rw [depth]
  change everyStep facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
    headTypingUnique rootComplete strengthening fuel
    (fun stored => everyRoundAt facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel (deadDepth (dead.reduced :: rest)) stored)
    problem ≠ .stuck
  unfold everyStep
  cases deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem with
  | stuck =>
      exact everySearch_not_stuck facts roots heads algebra rigid complete declared choices reducer strengthening fuel
        _ problem fires _ (List.mem_range.mpr bound)
  | progress update smaller =>
      intro stuck
      cases stuck
  | refuted absent =>
      intro stuck
      cases stuck

/-- The named readers move the dead-binder round. -/
theorem deadRound_not_stuck_of_fullReads (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (reads : FullReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem) :
    deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ≠ .stuck := by
  rcases reads with all | chain
  · rcases all with flexible | outer
    · exact deadRound_not_stuck_of_reads facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal headTypingUnique rootComplete strengthening fuel flexible
    · exact deadRound_not_stuck_of_outerReads facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal headTypingUnique rootComplete strengthening fuel outer
  · exact deadRound_not_stuck_of_chainReads facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening fuel chain

/-- **The named readers, closed under the front reader.** -/
inductive EveryReads (fuel : Nat) {Θ : Context S.R} : EquationStore (TotalTerm Θ) → Prop
  /-- A named reader of the dead-binder family. -/
  | full {problem : EquationStore (TotalTerm Θ)} :
      FullReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem → EveryReads fuel problem
  /-- A rotation whose first equation has a dead binder, read behind it. -/
  | front {problem : EquationStore (TotalTerm Θ)} {k : Nat} {equation : Equation (TotalTerm Θ)}
      {rest : EquationStore (TotalTerm Θ)} {dead : DeadBinder equation} :
      k < problem.length → problem.rotate k = equation :: rest →
      deadBinder facts roots heads algebra declared choices reducer fuel equation = some dead →
      EveryReads fuel (dead.reduced :: rest) → EveryReads fuel problem

/-- **Every-reading moves the every-rule round.** -/
theorem everyRound_not_stuck_of_everyReads (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (reads : EveryReads facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem) :
    everyRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ≠ .stuck := by
  induction reads with
  | full named =>
      exact everyRound_not_stuck_of_dead facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal headTypingUnique rootComplete strengthening fuel
        (deadRound_not_stuck_of_fullReads facts roots heads algebra rigid complete declared choices reducer root
          normalizes certifyNormal headTypingUnique rootComplete strengthening fuel named)
  | front bound rotated read _ behind =>
      exact everyRound_not_stuck_of_front facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal headTypingUnique rootComplete strengthening fuel bound rotated read behind

/-- **Firing of the every-rule round from eventual every-reading.** -/
theorem firing_of_everyReads
    (reads : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller S.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
        EveryReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
          headTypingUnique rootComplete strengthening larger problem)
    {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)} (permuted : PermutedMiller S.levels problem)
    (nonempty : problem ≠ []) :
    ∃ bound, ∀ larger, bound ≤ larger →
      everyRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening larger problem ≠ .stuck := by
  obtain ⟨bound, eventually⟩ := reads permuted nonempty
  exact ⟨bound, fun larger enough => everyRound_not_stuck_of_everyReads facts roots heads algebra rigid complete
    declared choices reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening larger
    (eventually larger enough)⟩

end General

/-! ## The tower -/

open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls
open ContextualDependentDynamicFragment

/-- Every-reading of the tower's every-rule family at one budget. -/
abbrev TowerEveryReads (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  EveryReads (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening fuel problem

/-- **Acceptance for the tower's every-rule family, reduced to eventual every-reading**, on every store of the dynamic
pattern fragment. -/
theorem tower_every_decided_of_everyReads
    (reads : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller setting.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger → TowerEveryReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (everyTower.solver larger) problem larger = run (everyTower.solver budget) problem budget ∧
      ((∃ state finished, run (everyTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (everyTower.solver larger) problem larger = .refuted absent)) :=
  tower_every_decided_of_firing
    (fun permuted nonempty => firing_of_everyReads (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
      TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none)
      ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
      ContextualDependentGeneralPattern.DispatchControls.certifyNormal
      ContextualDependentNormalCheckingTower.head_typing_unique
      (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening reads permuted
      nonempty)
    inside

end ContextualDependentCoverageReadersHalf
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
