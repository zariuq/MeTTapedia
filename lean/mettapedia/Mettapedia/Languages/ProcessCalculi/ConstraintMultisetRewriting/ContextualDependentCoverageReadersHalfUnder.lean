import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance4UnderFamily

/-!
# The readers' half of coverage for the under-binder family

The under-binder round fires wherever the dead-binder round does, so every named reader of the dead-binder family reads
it too. Its own reader is **the under-binder reader** (`underRound_not_stuck_of_dropsDead`): the round is not stuck on a
store one of whose rotations has a first equation from which a dead binder under live binders is read, behind which the
round is not stuck. Dropping removes one abstraction from the left side (`DropsDead.depth`), so the recursion depth of
the reduced store is one less.

`UnderReads` closes the named readers under this reader, and **firing follows from eventual under-reading**
(`firing_of_underReads`, `tower_under_decided_of_underReads`).
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

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **Dropping a dead binder under live binders removes one abstraction from the left sides of the store.** -/
theorem deadDepth_dropsDead {Θ : Context S.R} {equation reduced : Equation (TotalTerm Θ)}
    {rest : EquationStore (TotalTerm Θ)} (drops : DropsDead equation reduced) :
    deadDepth (equation :: rest) = deadDepth (reduced :: rest) + 1 := by
  simp only [deadDepth, List.map_cons, List.sum_cons, drops.depth]
  omega

section General

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
theorem underSearch_not_stuck (fuel : Nat) {Θ : Context S.R}
    (inner : (stored : EquationStore (TotalTerm Θ)) →
      Round S.levels (weightRank facts roots heads algebra rigid complete) stored)
    (problem : EquationStore (TotalTerm Θ)) {k : Nat}
    (fires : underAt facts roots heads algebra rigid complete declared choices reducer strengthening fuel inner
      (problem.rotate k) ≠ .stuck) :
    ∀ rotations : List Nat, k ∈ rotations →
      underSearch facts roots heads algebra rigid complete declared choices reducer strengthening fuel inner problem
        rotations ≠ .stuck
  | [], member => absurd member List.not_mem_nil
  | j :: js, member => by
      simp only [underSearch]
      cases computed : underAt facts roots heads algebra rigid complete declared choices reducer strengthening fuel
          inner (problem.rotate j) with
      | stuck =>
          have other : k ≠ j := by
            rintro rfl
            exact fires computed
          exact underSearch_not_stuck fuel inner problem fires js ((List.mem_cons.mp member).resolve_left other)
      | progress update smaller =>
          intro stuck
          cases stuck
      | refuted absent =>
          intro stuck
          cases stuck

/-- **The under-binder reader.** -/
theorem underRound_not_stuck_of_dropsDead (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    {k : Nat} (bound : k < problem.length) {equation : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (rotated : problem.rotate k = equation :: rest)
    {found : {reduced : Equation (TotalTerm Θ) // DropsDead equation reduced}}
    (read : readDead facts roots heads algebra declared choices reducer fuel (lamDepth equation.1.2.code) equation =
      some found)
    (behind : underRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel (found.val :: rest) ≠ .stuck) :
    underRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ≠ .stuck := by
  have depth : deadDepth problem = deadDepth (found.val :: rest) + 1 := by
    rw [deadDepth_perm (List.rotate_perm problem k).symm, rotated, deadDepth_dropsDead found.property]
  have fires : underAt facts roots heads algebra rigid complete declared choices reducer strengthening fuel
      (fun stored => underRoundAt facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening fuel (deadDepth (found.val :: rest)) stored)
      (problem.rotate k) ≠ .stuck := by
    rw [rotated]
    simp only [underAt, read]
    unfold dropRound
    rw [Ne, transferRound_stuck]
    exact behind
  unfold underRound
  rw [depth]
  change underStep facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
    headTypingUnique rootComplete strengthening fuel
    (fun stored => underRoundAt facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel (deadDepth (found.val :: rest)) stored)
    problem ≠ .stuck
  unfold underStep
  cases deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem with
  | stuck =>
      exact underSearch_not_stuck facts roots heads algebra rigid complete declared choices reducer strengthening fuel
        _ problem fires _ (List.mem_range.mpr bound)
  | progress update smaller =>
      intro stuck
      cases stuck
  | refuted absent =>
      intro stuck
      cases stuck

/-- **The named readers, closed under the under-binder reader.** -/
inductive UnderReads (fuel : Nat) {Θ : Context S.R} : EquationStore (TotalTerm Θ) → Prop
  /-- A named reader of the dead-binder family. -/
  | full {problem : EquationStore (TotalTerm Θ)} :
      FullReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem → UnderReads fuel problem
  /-- A rotation whose first equation drops a dead binder under live binders, read behind it. -/
  | under {problem : EquationStore (TotalTerm Θ)} {k : Nat} {equation : Equation (TotalTerm Θ)}
      {rest : EquationStore (TotalTerm Θ)} {found : {reduced : Equation (TotalTerm Θ) // DropsDead equation reduced}} :
      k < problem.length → problem.rotate k = equation :: rest →
      readDead facts roots heads algebra declared choices reducer fuel (lamDepth equation.1.2.code) equation =
        some found →
      UnderReads fuel (found.val :: rest) → UnderReads fuel problem

/-- **Under-reading moves the under-binder round.** -/
theorem underRound_not_stuck_of_underReads (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (reads : UnderReads facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem) :
    underRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ≠ .stuck := by
  induction reads with
  | full named =>
      exact underRound_not_stuck_of_dead facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal headTypingUnique rootComplete strengthening fuel
        (deadRound_not_stuck_of_fullReads facts roots heads algebra rigid complete declared choices reducer root
          normalizes certifyNormal headTypingUnique rootComplete strengthening fuel named)
  | under bound rotated read _ behind =>
      exact underRound_not_stuck_of_dropsDead facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal headTypingUnique rootComplete strengthening fuel bound rotated read behind

/-- **Firing of the under-binder round from eventual under-reading.** -/
theorem firing_of_underReads
    (reads : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller S.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
        UnderReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
          headTypingUnique rootComplete strengthening larger problem)
    {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)} (permuted : PermutedMiller S.levels problem)
    (nonempty : problem ≠ []) :
    ∃ bound, ∀ larger, bound ≤ larger →
      underRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening larger problem ≠ .stuck := by
  obtain ⟨bound, eventually⟩ := reads permuted nonempty
  exact ⟨bound, fun larger enough => underRound_not_stuck_of_underReads facts roots heads algebra rigid complete
    declared choices reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening larger
    (eventually larger enough)⟩

end General

/-! ## The tower -/

open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls
open ContextualDependentDynamicFragment

/-- Under-reading of the tower's under-binder family at one budget. -/
abbrev TowerUnderReads (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  UnderReads (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening fuel problem

/-- **Acceptance for the tower's under-binder family, reduced to eventual under-reading**, on every store of the
dynamic pattern fragment. -/
theorem tower_under_decided_of_underReads
    (reads : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller setting.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger → TowerUnderReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (underTower.solver larger) problem larger = run (underTower.solver budget) problem budget ∧
      ((∃ state finished, run (underTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (underTower.solver larger) problem larger = .refuted absent)) :=
  tower_under_decided_of_firing
    (fun permuted nonempty => firing_of_underReads (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
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
