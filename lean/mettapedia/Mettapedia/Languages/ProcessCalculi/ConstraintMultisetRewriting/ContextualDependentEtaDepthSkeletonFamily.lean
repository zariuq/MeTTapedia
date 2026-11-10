import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthSkeleton

/-!
# The skeleton family

**The skeleton round** (`skeletonRound`) is the η-long prepared round; when that is stuck, the skeleton clash rule on
the η-long store of the prepared store with homogeneous twins (`flexRefuted`), whose certified refutation refutes the
store. The rule only refutes, so the family keeps every progress of the η-long prepared family and needs no new closure
obligation.

The family is conservative over the η-long prepared family (`skeleton_run_of_eta`), eventually constant
(`skeletonRound_const`), closed in the permuted Miller class (`skeletonRound_closure`), and so decides every store of
the dynamic pattern fragment as soon as its round is eventually not stuck on nonempty stores of the class
(`skeleton_decided_of_firing`, `tower_skeleton_decided_of_firing`), in particular as soon as one of its readers reads
(`SkeletonReads`, `tower_skeleton_decided_of_skeletonReads`). A census head whose η-expanded sides have distinct
skeletons, at any base type, is read (`tower_skeletonReads_of_clash`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentConversionBudget ContextualDependentDynamicFragment
open ContextualDependentIntersectionGeneral ContextualDependentMillerClosure ContextualDependentOpenedNormal
open ContextualDependentAcceptance4 ContextualDependentCoverageReadersHalf ContextualDependentTwinsUnder
open ContextualDependentConstantHeads ContextualDependentCumulativeClosure

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- A refutation, or nothing, as a round. -/
def refutedRound {rank : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Nat × Nat} {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} :
    Option (PLift (¬ (frames S.levels).Solvable problem)) → Round S.levels rank problem
  | some absent => .refuted absent.down
  | none => .stuck

/-- The η-long store has the solutions of the store. -/
theorem expand_solvable (facts : FormFacts S.R S.roles) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (solvable : (frames S.levels).Solvable problem) : (frames S.levels).Solvable (expandStore facts problem) := by
  obtain ⟨Δ, σ, solved⟩ := solvable
  exact ⟨Δ, σ, (expand_equivalent facts problem Δ σ).mp solved⟩

section Rule

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

/-- The skeleton clash rule on the η-long store of an update of the store, read back as a refutation of the store. -/
def refutedOf {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (twins : Update S.levels problem) :
    Option (PLift (¬ (frames S.levels).Solvable problem)) :=
  (skeletonSearch facts rigid complete (expandStore facts twins.remaining)).map fun absent =>
    ⟨fun solvable => absent.down (expand_solvable facts (twins.solvable_iff.mp solvable))⟩

/-- **The skeleton clash rule on the η-long prepared store.** -/
def flexRefuted (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Option (PLift (¬ (frames S.levels).Solvable problem)) :=
  refutedOf facts rigid complete (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem)

/-- **The skeleton round**: the η-long prepared round; when it is stuck, the skeleton clash rule on the η-long
prepared store. -/
noncomputable def skeletonRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  orElse (etaRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem)
    (refutedRound (flexRefuted facts roots heads algebra rigid complete reducer root rootComplete fuel problem))

/-- **The skeleton family**, at the weight rank. -/
noncomputable def skeletonFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := skeletonRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening fuel

/-! ## Conservativity and readers -/

theorem skeletonRound_eq_of_eta (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : etaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem ≠ .stuck) :
    skeletonRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem =
      etaRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem := by
  unfold skeletonRound
  cases computed : etaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => rfl
  | refuted absent => rfl

/-- **Every run that the η-long prepared family decides, the skeleton family decides with the same outcome.** -/
theorem skeleton_run_of_eta (fuel rounds : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (decided : (run ((etaFamily facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds).Decided) :
    run ((skeletonFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds =
      run ((etaFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds :=
  ContextualDependentAcceptance.drive_conservative (weightRank facts roots heads algebra rigid complete)
    (fun problem => etaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (fun problem => skeletonRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (fun _ moving => skeletonRound_eq_of_eta facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel moving)
    rounds _ decided

/-- **The skeleton reader**: the round moves wherever the skeleton clash rule refutes the η-long prepared store. -/
theorem skeletonRound_not_stuck_of_refuted (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (read : (flexRefuted facts roots heads algebra rigid complete reducer root rootComplete fuel problem).isSome) :
    skeletonRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ≠ .stuck := by
  unfold skeletonRound
  obtain ⟨absent, computed⟩ := Option.isSome_iff_exists.mp read
  cases etaRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem with
  | stuck =>
      change refutedRound (flexRefuted facts roots heads algebra rigid complete reducer root rootComplete fuel
        problem) ≠ .stuck
      rw [computed]
      exact fun impossible => by cases impossible
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-- **The skeleton family's readers**: a reader of the η-long prepared family, or the skeleton clash rule. -/
def SkeletonReads (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  EtaReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ∨
    (flexRefuted facts roots heads algebra rigid complete reducer root rootComplete fuel problem).isSome

theorem skeletonRound_not_stuck_of_skeletonReads (fuel : Nat) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)}
    (reads : SkeletonReads facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem) :
    skeletonRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ≠ .stuck := by
  rcases reads with eta | refuted
  · have moving := etaRound_not_stuck_of_etaReads facts roots heads algebra rigid complete declared choices reducer
      root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel eta
    rw [skeletonRound_eq_of_eta facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel moving]
    exact moving
  · exact skeletonRound_not_stuck_of_refuted facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening fuel refuted

/-! ## Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
/-- **The skeleton round is eventually constant on every store.** -/
theorem skeletonRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => skeletonRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening fuel problem :=
  EventuallyConst.of_eq (fun _ => rfl)
    (EventuallyConst.comp (fun pair : Round S.levels (weightRank facts roots heads algebra rigid complete) problem ×
        Update S.levels problem => orElse pair.1 (refutedRound (refutedOf facts rigid complete pair.2)))
      (EventuallyConst.pair
        (etaRound_const facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening stable problem)
        (preparedTwins_const facts roots heads algebra reducer root rootComplete stable problem)))

include stable in
/-- **The skeleton family settles** on every class on which, from some budget on, its round is not stuck and keeps
the class. -/
noncomputable def skeletonSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        skeletonRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete strengthening larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          skeletonRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete strengthening larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (skeletonFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening) :=
  Settled.ofConst _ (fun problem => skeletonRound_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening stable problem) holds eventual

/-! ## Closure -/

variable (sn : StronglyNormalizing S.R)
  (directed : ∀ (fuel : Nat) {n : Nat} (term : Tm Head n) (result : ExecutableReduction.Result S.R term),
    reducer fuel term = some result → ContextualDependentExecutableJoin.Star (R := S.R) term result.val)

include sn directed in
/-- **Closure of the skeleton round** at every budget: its progress is the η-long prepared round's. -/
theorem skeletonRound_closure (fuel : Nat) :
    RoundKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      skeletonRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem := by
  intro Θ problem update smaller permuted fired
  change orElse (etaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (refutedRound (flexRefuted facts roots heads algebra rigid complete reducer root rootComplete fuel problem)) =
      .progress update smaller at fired
  cases computed : etaRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem with
  | stuck =>
      rw [computed] at fired
      change refutedRound (flexRefuted facts roots heads algebra rigid complete reducer root rootComplete fuel
        problem) = .progress update smaller at fired
      cases refuted : flexRefuted facts roots heads algebra rigid complete reducer root rootComplete fuel problem with
      | none =>
          rw [refuted] at fired
          cases fired
      | some absent =>
          rw [refuted] at fired
          cases fired
  | progress first firstSmaller =>
      rw [computed] at fired
      cases fired
      exact etaRound_closure facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening sn directed fuel _ _ _ permuted computed
  | refuted absent =>
      rw [computed] at fired
      cases fired

include sn directed stable in
/-- **Acceptance for the skeleton family from firing**: on a strongly normalizing package without root computation
whose reducer returns reducts and is monotone in its budget, and where typed equality strengthens past an unused
variable, the family decides every store of the dynamic pattern fragment, with a principal answer or a certified
refutation, constant at every larger budget, as soon as its round is eventually not stuck on nonempty stores of the
permuted class. -/
theorem skeleton_decided_of_firing
    (firing : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller S.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
        skeletonRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening larger problem ≠ .stuck)
    {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run ((skeletonFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
        run ((skeletonFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening).solver budget) problem budget ∧
      ((∃ state finished, run ((skeletonFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
              .solved state finished ∧ (frames S.levels).Principal problem state.answer) ∨
        (∃ absent, run ((skeletonFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
              .refuted absent)) :=
  (skeletonSettledOfConst facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening stable (fun problem => PermutedMiller S.levels problem)
    (fun held nonempty => by
      obtain ⟨bound, fires⟩ := firing held nonempty
      exact ⟨bound, fun larger enough => ⟨fires larger enough, fun {update} {smaller} fired =>
        skeletonRound_closure facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening sn directed larger _ update smaller held
          fired⟩⟩)).decided
    (permutedMiller_of_fragment inside)

end Rule

/-! ## The tower -/

open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls

/-- The skeleton family of the tower controls. -/
noncomputable def skeletonTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  skeletonFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening

/-- Readers of the tower's skeleton family at one budget. -/
abbrev TowerSkeletonReads (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  SkeletonReads (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening fuel problem

/-- **Acceptance for the tower's skeleton family from firing**, on every store of the dynamic pattern fragment. -/
theorem tower_skeleton_decided_of_firing
    (firing : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller setting.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger → skeletonTower.round larger problem ≠ .stuck)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (skeletonTower.solver larger) problem larger = run (skeletonTower.solver budget) problem budget ∧
      ((∃ state finished, run (skeletonTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (skeletonTower.solver larger) problem larger = .refuted absent)) :=
  skeleton_decided_of_firing (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening
    ContextualDependentDecisiveFragment.Controls.stable tower_stronglyNormalizing tower_reducer_directed firing inside

/-- **Acceptance for the tower's skeleton family from eventual reading**, on every store of the dynamic pattern
fragment. -/
theorem tower_skeleton_decided_of_skeletonReads
    (reads : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller setting.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger → TowerSkeletonReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (skeletonTower.solver larger) problem larger = run (skeletonTower.solver budget) problem budget ∧
      ((∃ state finished, run (skeletonTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (skeletonTower.solver larger) problem larger = .refuted absent)) :=
  tower_skeleton_decided_of_firing (fun permuted nonempty => by
      obtain ⟨bound, eventually⟩ := reads permuted nonempty
      exact ⟨bound, fun larger enough => skeletonRound_not_stuck_of_skeletonReads (S := setting) TowerModel.facts
        TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentPiSpine.Controls.rigid
        TowerModel.complete ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
        ContextualDependentInversion.Controls.reducer (fun _ => none)
        ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
        ContextualDependentGeneralPattern.DispatchControls.certifyNormal
        ContextualDependentNormalCheckingTower.head_typing_unique
        (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening larger
        (eventually larger enough)⟩)
    inside

/-! ## The census row of distinct skeletons at any base -/

/-- **A census head whose η-expanded sides have distinct skeletons is read** by the skeleton clash rule from some
budget on, at any base type. -/
theorem tower_skeletonReads_of_clash {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {threshold : Nat}
    (constant : ∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem)
    {equation : Equation (TotalTerm (towerPrepare threshold problem).target)}
    (member : equation ∈ (towerPrepare threshold problem).remaining)
    (types : TypeEq setting.R (towerPrepare threshold problem).target.raw equation.1.1.code equation.2.1.code)
    (clash : SkeletonClash 0 equation.1.1.code (expandTo (piCount equation.1.1.code) equation.1.2.code)
      (expandTo (piCount equation.1.1.code) equation.2.2.code)) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerSkeletonReads larger problem := by
  obtain ⟨bound, twins⟩ := tower_twins_keep constant member types
    (fun A l r => SkeletonClash 0 A (expandTo (piCount A) l) (expandTo (piCount A) r)) clash
  refine ⟨bound, fun larger enough => Or.inr ?_⟩
  obtain ⟨twin, twinMember, same, twinClash⟩ := twins larger enough
  have expandedMember := longUpdate_mem (S := setting) TowerModel.facts twinMember
  have shape : SkeletonShape (expandSide TowerModel.facts twin.1, expandSide TowerModel.facts twin.2) := by
    refine ⟨same, ?_⟩
    change SkeletonClash 0 twin.1.1.code (expandTo (piCount twin.1.1.code) twin.1.2.code)
      (expandTo (piCount twin.2.1.code) twin.2.2.code)
    rw [same]
    exact twinClash
  have found := skeletonSearch_isSome TowerModel.facts ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    expandedMember shape
  change ((skeletonSearch TowerModel.facts ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (expandStore TowerModel.facts (towerPreparedTwins larger problem).remaining)).map _).isSome
  rw [Option.isSome_map]
  exact found

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
