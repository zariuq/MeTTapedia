import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance4Every
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance4Final

/-!
# Closure of the every-rule round, and acceptance for the every-rule family from firing

**Dropping a dead binder keeps the permuted Miller class** (`PermutedMiller.undead`): the reduced equation has closed
normal Miller reducts of both sides, since its sides weakened are the bodies of the original sides (`reduced_reduct`),
its annotations are equal outright, and it has the original equation's solutions where typed equality strengthens past
an unused variable.

So the every-rule round keeps the permuted class at every depth wherever the dead-binder round does
(`everyRoundAt_keeps`), and on a strongly normalizing package without root computation whose reducer returns reducts
it keeps the class at every budget (`everyRound_closure`). **Acceptance from firing** (`every_decided_of_firing`,
`tower_every_decided_of_firing`): if the every-rule round is eventually not stuck on nonempty `PermutedMiller` stores,
the every-rule family decides every store of the dynamic pattern fragment. The every-rule round fires wherever the
dead-binder round fires (`everyRound_not_stuck_of_dead`), and also on the pattern equation behind a dead binder
(`ContextualDependentAcceptance4.deadPattern_every_committed`), where the dead-binder round does not.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentAcceptance4

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentRank
open ContextualDependentMillerClosure ContextualDependentShortClosure ContextualDependentDynamicFragment
open ContextualDependentExecutableJoin ContextualDependentCumulativeClosure ContextualDependentOpenedNormal
open ContextualDependentConversionBudget ContextualDependentAcceptance3 ContextualDependentIntersectionGeneral

/-! ## The class without a dead binder -/

section Class

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **A typed code whose weakening sits under an abstraction with a closed normal Miller reduct has one too.** -/
theorem reduced_reduct (rigid : ∀ name, S.roles name = .rigid) (sn : StronglyNormalizing S.R) {Θ : Context S.R}
    {type : TypeOver Θ} (body : Term Θ type)
    (closed : MarkedReduct S.R (fun _ => true) (.lam (Presentation.rename wk body.code))) :
    MarkedReduct S.R (fun _ => true) body.code := by
  have empty := computation_empty rigid
  have lifted := MarkedReduct.of_lam empty closed
  obtain ⟨N, toN, normalN⟩ := term_normal sn body
  have renamed := star_rename (R := S.R) wk toN
  have normalRenamed : Normal S.R (Presentation.rename wk N) :=
    (ContextualDependentNormalizing.normal_rename_iff empty wk N).mpr normalN
  have millerRenamed := all_miller_of_one empty lifted _ renamed normalRenamed
  exact ⟨N, toN, normalN, miller_rename_reflect N (Fin.succ_injective _) (fun _ => rfl) millerRenamed⟩

/-- **The reduced equation of a dead binder has Miller sides** when the equation has. -/
theorem sides_reduced (rigid : ∀ name, S.roles name = .rigid) (sn : StronglyNormalizing S.R) {Θ : Context S.R}
    {equation : Equation (TotalTerm Θ)} (dead : DeadBinder equation) (sides : FragmentSidesMiller equation) :
    FragmentSidesMiller dead.reduced := by
  obtain ⟨left, right⟩ := side_reduct rigid sn sides
  rw [dead.leftTerm] at left
  rw [dead.rightTerm] at right
  exact sides_of_reducts (computation_empty rigid) (reduced_reduct rigid sn dead.reduced.1.2 left)
    (reduced_reduct rigid sn dead.reduced.2.2 right)

/-- **Dropping the dead binder of the first equation keeps the permuted Miller class**, where typed equality
strengthens past an unused variable. -/
theorem PermutedMiller.undead (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
    (rigid : ∀ name, S.roles name = .rigid) (sn : StronglyNormalizing S.R) (strengthening : EqualStrengthening S.R)
    {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (dead : DeadBinder equation) (permuted : PermutedMiller S.levels (equation :: rest)) :
    PermutedMiller S.levels (dead.reduced :: rest) :=
  permuted.splice_of (pieces := [dead.reduced]) fun before after stratified =>
    StratifiedMiller.splice stratified
      (fun σ => ⟨fun solved => solves_of_reduced dead σ (solved _ (List.mem_singleton_self _)),
        fun solved piece member => by
          obtain rfl := List.mem_singleton.mp member
          exact reduced_of_solves facts roots strengthening dead σ solved⟩)
      (fun piece member => by
        obtain rfl := List.mem_singleton.mp member
        exact sides_reduced rigid sn dead (stratified before after equation rfl).1)
      (fun first last piece split => by
        intro Δ σ _
        have member : piece ∈ [dead.reduced] := by
          rw [split]
          simp
        obtain rfl := List.mem_singleton.mp member
        change TypeEq S.R _ (subst σ.substitution dead.reduced.1.1.code) (subst σ.substitution dead.reduced.2.1.code)
        rw [dead.sameType]
        exact (dead.reduced.1.1.reindex σ).isType.refl)

end Class

/-! ## Closure -/

section Closure

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

/-- A round over one context keeps the permuted Miller class. -/
def KeepsAt {Θ : Context S.R}
    (round : (stored : EquationStore (TotalTerm Θ)) →
      Round S.levels (weightRank facts roots heads algebra rigid complete) stored) : Prop :=
  ∀ (stored : EquationStore (TotalTerm Θ)) (update : Update S.levels stored)
    (smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
      (weightRank facts roots heads algebra rigid complete stored)),
    PermutedMiller S.levels stored → round stored = .progress update smaller → PermutedMiller S.levels update.remaining

variable (sn : StronglyNormalizing S.R)

include sn in
theorem everyAt_keeps (fuel : Nat) {Θ : Context S.R}
    (inner : (stored : EquationStore (TotalTerm Θ)) →
      Round S.levels (weightRank facts roots heads algebra rigid complete) stored)
    (keeps : KeepsAt facts roots heads algebra rigid complete inner) :
    KeepsAt facts roots heads algebra rigid complete
      (everyAt facts roots heads algebra rigid complete declared choices reducer strengthening fuel inner) := by
  intro stored update smaller permuted fired
  cases stored with
  | nil => cases fired
  | cons equation rest =>
      simp only [everyAt] at fired
      split at fired
      · cases fired
      · rename_i dead _
        exact transferRound_keeps facts roots heads algebra rigid complete (fun problem => PermutedMiller S.levels problem)
          (fun first firstSmaller computed => keeps _ first firstSmaller
            (PermutedMiller.undead facts roots rigid sn strengthening dead permuted) computed) fired

include sn in
theorem everySearch_keeps (fuel : Nat) {Θ : Context S.R}
    (inner : (stored : EquationStore (TotalTerm Θ)) →
      Round S.levels (weightRank facts roots heads algebra rigid complete) stored)
    (keeps : KeepsAt facts roots heads algebra rigid complete inner) (problem : EquationStore (TotalTerm Θ)) :
    ∀ (rotations : List Nat) (update : Update S.levels problem)
      (smaller : ContextualDependentWorklist.Below
        (weightRank facts roots heads algebra rigid complete update.remaining)
        (weightRank facts roots heads algebra rigid complete problem)),
      PermutedMiller S.levels problem →
      everySearch facts roots heads algebra rigid complete declared choices reducer strengthening fuel inner problem
        rotations = .progress update smaller → PermutedMiller S.levels update.remaining
  | [], _, _, _, fired => by cases fired
  | k :: ks, update, smaller, permuted, fired => by
      simp only [everySearch] at fired
      cases computed : everyAt facts roots heads algebra rigid complete declared choices reducer strengthening fuel
          inner (problem.rotate k) with
      | stuck =>
          rw [computed] at fired
          exact everySearch_keeps fuel inner keeps problem ks update smaller permuted fired
      | progress first firstSmaller =>
          rw [computed] at fired
          exact transferRound_keeps facts roots heads algebra rigid complete (fun problem => PermutedMiller S.levels problem)
            (fun first' firstSmaller' same => by
              cases same
              exact everyAt_keeps facts roots heads algebra rigid complete declared choices reducer strengthening sn
                fuel inner keeps _ first firstSmaller (permuted.perm (List.rotate_perm problem k).symm) computed)
            fired
      | refuted absent =>
          rw [computed] at fired
          cases fired

include sn in
theorem everyStep_keeps (fuel : Nat) {Θ : Context S.R}
    (lower : (stored : EquationStore (TotalTerm Θ)) →
      Round S.levels (weightRank facts roots heads algebra rigid complete) stored)
    (keepsLower : KeepsAt facts roots heads algebra rigid complete lower)
    (keepsDead : KeepsAt facts roots heads algebra rigid complete (Θ := Θ) fun stored =>
      deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel stored) :
    KeepsAt facts roots heads algebra rigid complete
      (everyStep facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel lower) := by
  intro problem update smaller permuted fired
  unfold everyStep at fired
  cases computed : deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem with
  | stuck =>
      rw [computed] at fired
      exact everySearch_keeps facts roots heads algebra rigid complete declared choices reducer strengthening sn fuel
        lower keepsLower problem _ update smaller permuted fired
  | progress first firstSmaller =>
      rw [computed] at fired
      cases fired
      exact keepsDead problem _ _ permuted computed
  | refuted absent =>
      rw [computed] at fired
      cases fired

include sn in
/-- **The every-rule round keeps the permuted class at every depth** wherever the dead-binder round does. -/
theorem everyRoundAt_keeps (fuel : Nat)
    (keepsDead : ∀ {Θ : Context S.R}, KeepsAt facts roots heads algebra rigid complete (Θ := Θ) fun stored =>
      deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel stored) :
    ∀ (depth : Nat) {Θ : Context S.R}, KeepsAt facts roots heads algebra rigid complete (Θ := Θ) fun stored =>
      everyRoundAt facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel depth stored
  | 0, _ => keepsDead
  | depth + 1, _ => fun problem update smaller permuted fired =>
      everyStep_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening sn fuel _ (everyRoundAt_keeps fuel keepsDead depth) keepsDead
        problem update smaller permuted fired

variable (directed : ∀ (fuel : Nat) {n : Nat} (term : Tm Head n) (result : ExecutableReduction.Result S.R term),
  reducer fuel term = some result → ContextualDependentExecutableJoin.Star (R := S.R) term result.val)

include sn directed in
/-- **Closure of the every-rule round**: on a strongly normalizing package without root computation whose reducer
returns reducts, and where typed equality strengthens past an unused variable, the every-rule round keeps the permuted
Miller class at every budget. -/
theorem everyRound_closure (fuel : Nat) :
    RoundKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      everyRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem := by
  have keepsDead : ∀ {Θ : Context S.R}, KeepsAt facts roots heads algebra rigid complete (Θ := Θ) fun stored =>
      deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel stored := fun {_} =>
    (keepsPermutedNormal_iff facts roots heads algebra rigid complete sn _).mp
      (deadRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening fuel
        (cumulativeRound_keepsPermutedNormal facts roots heads algebra rigid complete declared choices reducer root
          normalizes certifyNormal headTypingUnique rootComplete sn directed fuel))
  intro Θ problem update smaller permuted fired
  exact everyRoundAt_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening sn fuel keepsDead (deadDepth problem) problem update
    smaller permuted fired

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n), Keeps (reducer fuel term) (reducer (fuel + 1) term))

include sn directed stable in
/-- **Acceptance for the every-rule family from firing**: on the same packages, with a reducer monotone in its budget,
the family decides every store of the dynamic pattern fragment, with a principal answer or a certified refutation,
constant at every larger budget, as soon as its round is eventually not stuck on nonempty stores of the permuted
class. -/
theorem every_decided_of_firing
    (firing : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller S.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
        everyRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening larger problem ≠ .stuck)
    {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run ((everyFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
        run ((everyFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening).solver budget) problem budget ∧
      ((∃ state finished, run ((everyFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
              .solved state finished ∧ (frames S.levels).Principal problem state.answer) ∨
        (∃ absent, run ((everyFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
              .refuted absent)) :=
  (everySettledOfConst facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening stable (fun problem => PermutedMiller S.levels problem)
    (fun held nonempty => by
      obtain ⟨bound, fires⟩ := firing held nonempty
      exact ⟨bound, fun larger enough => ⟨fires larger enough, fun {update} {smaller} fired =>
        everyRound_closure facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening sn directed larger _ update smaller held
          fired⟩⟩)).decided
    (permutedMiller_of_fragment inside)

end Closure

/-! ## The tower -/

open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls

/-- The every-rule family of the tower controls. -/
noncomputable def everyTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  everyFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening

/-- **Acceptance for the tower's every-rule family from firing**, on every store of the dynamic pattern fragment: no
rule obligation remains. -/
theorem tower_every_decided_of_firing
    (firing : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller setting.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger → everyTower.round larger problem ≠ .stuck)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (everyTower.solver larger) problem larger = run (everyTower.solver budget) problem budget ∧
      ((∃ state finished, run (everyTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (everyTower.solver larger) problem larger = .refuted absent)) :=
  every_decided_of_firing (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening
    tower_stronglyNormalizing tower_reducer_directed ContextualDependentDecisiveFragment.Controls.stable firing inside

/-- **The tower's every-rule round fires wherever its dead-binder round does.** -/
theorem tower_every_not_stuck_of_dead (fuel : Nat) {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : deadTower.round fuel problem ≠ .stuck) : everyTower.round fuel problem ≠ .stuck :=
  everyRound_not_stuck_of_dead (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening fuel moving

end ContextualDependentAcceptance4
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
