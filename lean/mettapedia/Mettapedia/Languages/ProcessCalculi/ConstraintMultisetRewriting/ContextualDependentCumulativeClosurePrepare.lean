import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosureRules

/-!
# Closure of the cumulative round: preparation

Preparation (`ContextualDependentNormalizing.prepare`) normalizes the context's declarations, then every annotation and
side of the store. It keeps the permuted Miller class on a strongly normalizing package (`prepare_keeps`):

* **the context step** reindexes the store along the identity substitution into the normalized context, so the codes do
  not change (`PermutedMiller.applyStore_of_sides`, `contextStep_keeps`);
* **the store step** replaces each annotation and side by an equivalent directed reduct (`termAt_star`). The solutions
  are the same, the annotations stay equal under every substitution, and the sides stay Miller: a reduct of a side has
  the side's normal forms, and opening it deeper adds distinct rigid locals (`fragmentSidesMiller_of_star`, through
  `lamDepth_star`, R116's `miller_deeper` and confluence).

The Miller transfer along reducts (`fragmentSidesMiller_of_star`) is the tool for every rule whose answers or pieces
are reducts of normal Miller codes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCumulativeClosure

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentRank
open ContextualDependentMillerClosure ContextualDependentShortClosure ContextualDependentClosure
open ContextualDependentDynamicFragment ExecutableReduction ContextualDependentExecutableJoin

/-! ## Opening depth and Miller sides along reduction -/

section Raw

variable {Head : Type} {R : Rules Head} (empty : R.computation = RootComputation.empty)
include empty

/-- **A directed step never removes a leading abstraction.** -/
theorem lamDepth_step : ∀ {n : Nat} {t u : Tm Head n}, StrongNormalization.Reduces R t u → lamDepth t ≤ lamDepth u
  | _, .lam _, _, step => by
      cases step with
      | congLam inner => exact Nat.succ_le_succ (lamDepth_step inner)
      | root rootStep => exact absurd rootStep (no_root empty)
  | _, .var _, _, _ | _, .const _, _, _ | _, .head _, _, _ | _, .pi _ _, _, _ | _, .sigma _ _, _, _
  | _, .id _ _ _, _, _ | _, .app _ _, _, _ | _, .pair _ _, _, _ | _, .fst _, _, _ | _, .snd _, _, _
  | _, .refl _, _, _ => Nat.zero_le _

theorem lamDepth_star {n : Nat} {t u : Tm Head n} (steps : Star (R := R) t u) : lamDepth t ≤ lamDepth u := by
  induction steps with
  | refl => exact le_rfl
  | tail _ step earlier => exact earlier.trans (lamDepth_step empty step)

/-- A Miller normal form of an opening is a normal form of the opening of every reduct. -/
theorem miller_of_reduct {n d : Nat} {code code' : Tm Head n} (steps : Star (R := R) code code')
    (inside : ∀ opened, Star (R := R) (openCode d code) opened → Normal R opened →
      miller (openedFlexible d) opened = true)
    (normalizes : ∃ opened, Star (R := R) (openCode d code) opened ∧ Normal R opened) :
    ∃ opened, Star (R := R) (openCode d code') opened ∧ Normal R opened ∧ miller (openedFlexible d) opened = true := by
  obtain ⟨N, toN, normalN⟩ := normalizes
  exact ⟨N, star_to_normal empty toN normalN (ContextualDependentOpenedNormal.star_openCode steps d), normalN,
    inside N toN normalN⟩

end Raw

section Equations

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}

/-- **Miller sides along reduction**: replacing both sides of an equation by directed reducts keeps Miller sides, when
the opened sides have normal forms. -/
theorem fragmentSidesMiller_of_star (empty : rules.computation = RootComputation.empty) {Θ : Context rules}
    {equation equation' : Equation (TotalTerm Θ)}
    (left : Star (R := rules) equation.1.2.code equation'.1.2.code)
    (right : Star (R := rules) equation.2.2.code equation'.2.2.code) (sides : FragmentSidesMiller equation)
    (normalLeft : ∃ opened, Star (R := rules) (openCode (lamDepth equation.1.2.code) equation.1.2.code) opened ∧
      Normal rules opened)
    (normalRight : ∃ opened, Star (R := rules) (openCode (lamDepth equation.1.2.code) equation.2.2.code) opened ∧
      Normal rules opened) :
    FragmentSidesMiller equation' := by
  obtain ⟨k, deeper⟩ := Nat.exists_eq_add_of_le (lamDepth_star empty left)
  unfold FragmentSidesMiller
  rw [deeper]
  exact ⟨all_miller_of_one empty (miller_deeper empty k (miller_of_reduct empty left sides.1 normalLeft)),
    all_miller_of_one empty (miller_deeper empty k (miller_of_reduct empty right sides.2 normalRight))⟩

/-- **Reindexing keeps the stratified Miller class wherever it keeps Miller sides.** -/
theorem stratifiedMiller_applyStore_of_sides {Θ Δ : Context rules} (σ : Δ ⟶ Θ)
    {problem : EquationStore (TotalTerm Θ)} (stratified : StratifiedMiller levels problem)
    (sides : ∀ equation ∈ problem, FragmentSidesMiller (equation.1.reindex σ, equation.2.reindex σ)) :
    StratifiedMiller levels ((frames levels).applyStore σ problem) := by
  intro before' after' later split
  change problem.map (fun equation => (equation.1.reindex σ, equation.2.reindex σ)) =
    before' ++ later :: after' at split
  obtain ⟨prefix', rest, hsplit, rfl, mapped⟩ := List.map_eq_append_iff.mp split
  obtain ⟨equation, suffix, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.mp mapped
  have member : equation ∈ problem := by
    rw [hsplit]
    exact List.mem_append_right _ List.mem_cons_self
  refine ⟨sides equation member, ?_⟩
  intro Δ' τ solvedPrefix
  have pulled : (frames levels).Models (τ ≫ σ) prefix' :=
    (Frames.models_applyStore (X := frames levels) σ τ prefix').mp solvedPrefix
  have annotations := (stratified prefix' suffix equation hsplit).2 _ pulled
  have leftSame : subst τ.substitution (equation.1.reindex σ).1.code =
      subst (τ ≫ σ).substitution equation.1.1.code :=
    (congrArg TypeOver.code (TypeOver.reindex_comp equation.1.1 τ σ)).symm
  have rightSame : subst τ.substitution (equation.2.reindex σ).1.code =
      subst (τ ≫ σ).substitution equation.2.1.code :=
    (congrArg TypeOver.code (TypeOver.reindex_comp equation.2.1 τ σ)).symm
  change TypeEq rules Δ'.raw (subst τ.substitution (equation.1.reindex σ).1.code)
    (subst τ.substitution (equation.2.reindex σ).1.code)
  rw [leftSame, rightSame]
  exact annotations

theorem PermutedMiller.applyStore_of_sides {Θ Δ : Context rules} (σ : Δ ⟶ Θ)
    {problem : EquationStore (TotalTerm Θ)} (permuted : PermutedMiller levels problem)
    (sides : ∀ equation ∈ problem, FragmentSidesMiller (equation.1.reindex σ, equation.2.reindex σ)) :
    PermutedMiller levels ((frames levels).applyStore σ problem) := by
  obtain ⟨ordered, perm, stratified⟩ := permuted
  exact ⟨(frames levels).applyStore σ ordered, perm.map _,
    stratifiedMiller_applyStore_of_sides σ stratified fun equation member => sides equation (perm.subset member)⟩

/-- **An equation-wise replacement by equivalent terms keeps the permuted class**, wherever it keeps Miller sides. -/
theorem PermutedMiller.map_equivalent {Θ : Context rules} {problem : EquationStore (TotalTerm Θ)}
    (permuted : PermutedMiller levels problem) (f : TotalTerm Θ → TotalTerm Θ)
    (equivalent : ∀ term, (frames levels).E term (f term))
    (sides : ∀ equation ∈ problem, FragmentSidesMiller equation → FragmentSidesMiller (f equation.1, f equation.2)) :
    PermutedMiller levels (problem.map fun equation => (f equation.1, f equation.2)) := by
  refine permuted.map _ (fun equation Δ σ => ?_) sides (fun equation _ before stratified Δ σ solved => ?_)
  · have first := (frames levels).preserves σ (equivalent equation.1)
    have second := (frames levels).preserves σ (equivalent equation.2)
    have eqv := (frames levels).equivalence Δ
    exact ⟨fun solved => eqv.trans first (eqv.trans solved (eqv.symm second)),
      fun solved => eqv.trans (eqv.symm first) (eqv.trans solved second)⟩
  · have annotations := stratified σ solved
    have first := ((frames levels).preserves σ (equivalent equation.1)).1
    have second := ((frames levels).preserves σ (equivalent equation.2)).1
    exact TypeEq.trans levels (TypeEq.trans levels first.symm annotations) second

end Equations

/-! ## The executable normalizer reduces by directed steps -/

section Normalizer

variable {Head : Type} (rules : Rules Head) (root : RootEvaluator rules)

/-- **The executable normalizer's result is a directed reduct.** -/
theorem normalize_star {n : Nat} : ∀ (fuel : Nat) {term : Tm Head n} {result : Result rules term},
    ExecutableReduction.normalize rules root fuel term = some result → Star (R := rules) term result.val
  | 0, _, _, accepted => by cases accepted
  | fuel + 1, term, result, accepted => by
      cases current : step rules root term with
      | none =>
          simp only [ExecutableReduction.normalize, current, Option.some.injEq] at accepted
          subst accepted
          exact .refl
      | some next =>
          cases later : ExecutableReduction.normalize rules root fuel next.val with
          | none =>
              simp only [ExecutableReduction.normalize, current, later] at accepted
              cases accepted
          | some answer =>
              simp only [ExecutableReduction.normalize, current, later, Option.some.injEq] at accepted
              subst accepted
              exact Relation.ReflTransGen.head
                (ContextualDependentReductionBudget.step_directed rules root term next current)
                (normalize_star fuel later)

end Normalizer

/-! ## Preparation -/

section Prepare

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (root : ExecutableReduction.RootEvaluator S.R)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)
  (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)

/-- **Store normalization replaces each annotation and side by a directed reduct.** -/
theorem termAt_star (fuel : Nat) {Γ : Context S.R} (original : TotalTerm Γ) :
    Star (R := S.R) original.1.code (ContextualDependentNormalization.termAt root facts roots heads fuel original).1.code ∧
      Star (R := S.R) original.2.code
        (ContextualDependentNormalization.termAt root facts roots heads fuel original).2.code := by
  unfold ContextualDependentNormalization.termAt
  cases computed : ContextualDependentNormalization.reduceTerm root facts roots heads fuel original with
  | none => exact ⟨.refl, .refl⟩
  | some reduced =>
      dsimp only
      unfold ContextualDependentNormalization.reduceTerm at computed
      split at computed
      · cases computed
      · rename_i annotation annotationRun
        split at computed
        · cases computed
        · rename_i value valueRun
          cases computed
          exact ⟨normalize_star S.R root fuel annotationRun, normalize_star S.R root fuel valueRun⟩

/-- **The context step keeps the permuted class**: the store is reindexed along the identity substitution. -/
theorem contextStep_keeps (fuel : Nat) :
    UpdateKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      ContextualDependentNormalizing.contextStep root rootComplete facts roots heads fuel problem := by
  intro Θ problem permuted
  dsimp only
  unfold ContextualDependentNormalizing.contextStep
  split
  · exact permuted
  · rename_i normalized _
    refine PermutedMiller.applyStore_of_sides normalized.iso.hom permuted fun equation member => ?_
    have sides := permuted.sides_of_mem member
    unfold FragmentSidesMiller at sides ⊢
    change (∀ code, Star (R := S.R) (openCode (lamDepth (subst ids equation.1.2.code)) (subst ids equation.1.2.code))
        code → Normal S.R code → miller (openedFlexible (lamDepth (subst ids equation.1.2.code))) code = true) ∧
      (∀ code, Star (R := S.R) (openCode (lamDepth (subst ids equation.1.2.code)) (subst ids equation.2.2.code))
        code → Normal S.R code → miller (openedFlexible (lamDepth (subst ids equation.1.2.code))) code = true)
    rw [subst_ids equation.1.2.code, subst_ids equation.2.2.code]
    exact sides

/-- **Preparation keeps the permuted class** on a strongly normalizing package. -/
theorem prepare_keeps (rigid : ∀ name, S.roles name = .rigid) (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R)
    (fuel : Nat) :
    PrepareKeeps (holds := fun problem => PermutedMiller S.levels problem) facts roots heads root rootComplete fuel := by
  intro Θ problem permuted
  have context := contextStep_keeps root rootComplete facts roots heads fuel problem permuted
  change PermutedMiller S.levels (ContextualDependentNormalization.storeAt root facts roots heads fuel
    (ContextualDependentNormalizing.contextStep root rootComplete facts roots heads fuel problem).remaining)
  unfold ContextualDependentNormalization.storeAt
  refine PermutedMiller.map_equivalent context _
    (ContextualDependentNormalization.termAt_equivalent root facts roots heads fuel)
    fun equation _ sides => ?_
  have empty := computation_empty rigid
  exact fragmentSidesMiller_of_star empty (termAt_star root facts roots heads fuel equation.1).2
    (termAt_star root facts roots heads fuel equation.2).2 sides
    (ContextualDependentOpenedNormal.opens_normal_of_reduct empty
      (ContextualDependentOpenedNormal.term_normal sn equation.1.2) _)
    (ContextualDependentOpenedNormal.opens_normal_of_reduct empty
      (ContextualDependentOpenedNormal.term_normal sn equation.2.2) _)

end Prepare

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
