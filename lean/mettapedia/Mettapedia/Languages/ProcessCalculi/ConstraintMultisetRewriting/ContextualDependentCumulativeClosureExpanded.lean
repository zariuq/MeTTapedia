import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosureBinder

/-!
# Closure of the cumulative round: R112's η for Σ

The pairs round expands, under the common abstractions, a pair against a rigid neutral side `n` (a spine whose head is
a bound local or a constant) into the pair of its projections (`ContextualDependentCensusPairEta.expandOne`). On a
strongly normalizing package an equation has Miller sides exactly when both its codes have closed normal reducts with
Miller occurrences (`side_reduct`, `sides_of_reducts`). Reduction keeps a rigid neutral spine rigid
(`fixedSkeleton_star`), the projections of a rigid neutral normal form are normal and Miller (`pairEta_reduct`), so the
expansion keeps Miller sides (`expandOne_sides`), its annotations are equal to the original ones, and the prepared
expansion keeps the permuted class (`expanded_keeps`).
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
open ContextualDependentMillerClosure ContextualDependentShortClosure ContextualDependentDynamicFragment
open ContextualDependentExecutableJoin ContextualDependentConstantHeads ContextualDependentCensusPairEta
open ContextualDependentClosure
open ContextualDependentGeneralPattern (liftFlexible)

/-! ## Rigid neutral spines along reduction -/

section Raw

variable {Head : Type} {R : Rules Head} (empty : R.computation = RootComputation.empty)
include empty

theorem star_lam_inv {n : Nat} {body : Tm Head (n + 1)} {X : Tm Head n} (steps : Star (R := R) (.lam body) X) :
    ∃ body', X = .lam body' ∧ Star (R := R) body body' := by
  induction steps with
  | refl => exact ⟨body, rfl, .refl⟩
  | tail _ step ih =>
      obtain ⟨body', rfl, inner⟩ := ih
      cases step with
      | root impossible => exact False.elim (no_root empty impossible)
      | congLam inner' => exact ⟨_, rfl, inner.tail inner'⟩

theorem MarkedReduct.of_lam {n : Nat} {mark : Fin n → Bool} {t : Tm Head (n + 1)}
    (outer : MarkedReduct R mark (.lam t)) : MarkedReduct R (liftFlexible mark) t := by
  obtain ⟨X, toX, normalX, millerX⟩ := outer
  obtain ⟨t', rfl, toT⟩ := star_lam_inv empty toX
  exact ⟨t', toT, (normal_lam_iff empty).mp normalX, millerX⟩

/-- **A directed step keeps a rigid neutral spine rigid**, with the same skeleton. -/
theorem fixedSkeleton_step {depth : Nat} : ∀ {n : Nat} {t u : Tm Head n} {s : Skeleton},
    fixedSkeleton depth t = some s → StrongNormalization.Reduces R t u → fixedSkeleton depth u = some s
  | _, .var _, _, _, _, step => by
      cases step with
      | root impossible => exact False.elim (no_root empty impossible)
  | _, .const _, _, _, _, step => by
      cases step with
      | root impossible => exact False.elim (no_root empty impossible)
  | _, .app f a, _, s, skel, step => by
      simp only [fixedSkeleton, Option.map_eq_some_iff] at skel
      obtain ⟨inner, innerSkel, rfl⟩ := skel
      cases step with
      | root impossible => exact False.elim (no_root empty impossible)
      | betaPi body _ => simp [fixedSkeleton] at innerSkel
      | congAppFun inner' =>
          simp only [fixedSkeleton, Option.map_eq_some_iff]
          exact ⟨inner, fixedSkeleton_step innerSkel inner', rfl⟩
      | congAppArg _ =>
          simp only [fixedSkeleton, Option.map_eq_some_iff]
          exact ⟨inner, innerSkel, rfl⟩
  | _, .fst p, _, s, skel, step => by
      simp only [fixedSkeleton, Option.map_eq_some_iff] at skel
      obtain ⟨inner, innerSkel, rfl⟩ := skel
      cases step with
      | root impossible => exact False.elim (no_root empty impossible)
      | betaSigmaFst _ _ => simp [fixedSkeleton] at innerSkel
      | congFst inner' =>
          simp only [fixedSkeleton, Option.map_eq_some_iff]
          exact ⟨inner, fixedSkeleton_step innerSkel inner', rfl⟩
  | _, .snd p, _, s, skel, step => by
      simp only [fixedSkeleton, Option.map_eq_some_iff] at skel
      obtain ⟨inner, innerSkel, rfl⟩ := skel
      cases step with
      | root impossible => exact False.elim (no_root empty impossible)
      | betaSigmaSnd _ _ => simp [fixedSkeleton] at innerSkel
      | congSnd inner' =>
          simp only [fixedSkeleton, Option.map_eq_some_iff]
          exact ⟨inner, fixedSkeleton_step innerSkel inner', rfl⟩
  | _, .head _, _, _, skel, _ | _, .pi _ _, _, _, skel, _ | _, .sigma _ _, _, _, skel, _
  | _, .id _ _ _, _, _, skel, _ | _, .lam _, _, _, skel, _ | _, .pair _ _, _, _, skel, _
  | _, .refl _, _, _, skel, _ => by simp [fixedSkeleton] at skel

theorem fixedSkeleton_star {depth n : Nat} {t u : Tm Head n} {s : Skeleton} (skel : fixedSkeleton depth t = some s)
    (steps : Star (R := R) t u) : fixedSkeleton depth u = some s := by
  induction steps with
  | refl => exact skel
  | tail _ step ih => exact fixedSkeleton_step empty ih step

omit empty in
/-- **A rigid neutral spine has a rigid head** at a marking with its bound locals rigid. -/
theorem flexHead_of_skeleton {depth : Nat} : ∀ {n : Nat} {t : Tm Head n} {s : Skeleton} (mark : Fin n → Bool),
    fixedSkeleton depth t = some s → (∀ i : Fin n, i.val < depth → mark i = false) →
    flexHead mark (spineHead t) = false
  | _, .var i, _, mark, skel, locals => by
      simp only [fixedSkeleton] at skel
      split at skel
      · rename_i bound
        exact locals i bound
      · cases skel
  | _, .const _, _, _, _, _ => rfl
  | _, .app f _, _, mark, skel, locals => by
      simp only [fixedSkeleton, Option.map_eq_some_iff] at skel
      obtain ⟨inner, innerSkel, _⟩ := skel
      change flexHead mark (spineHead f) = false
      exact flexHead_of_skeleton mark innerSkel locals
  | _, .fst _, _, _, _, _ => rfl
  | _, .snd _, _, _, _, _ => rfl
  | _, .head _, _, _, skel, _ | _, .pi _ _, _, _, skel, _ | _, .sigma _ _, _, _, skel, _
  | _, .id _ _ _, _, _, skel, _ | _, .lam _, _, _, skel, _ | _, .pair _ _, _, _, skel, _
  | _, .refl _, _, _, skel, _ => by simp [fixedSkeleton] at skel

theorem normal_fst_of_skeleton {depth n : Nat} {p : Tm Head n} {s : Skeleton} (skel : fixedSkeleton depth p = some s)
    (normal : Normal R p) : Normal R (.fst p) := by
  intro u step
  cases step with
  | root impossible => exact no_root empty impossible
  | betaSigmaFst _ _ => simp [fixedSkeleton] at skel
  | congFst inner => exact normal _ inner

theorem normal_snd_of_skeleton {depth n : Nat} {p : Tm Head n} {s : Skeleton} (skel : fixedSkeleton depth p = some s)
    (normal : Normal R p) : Normal R (.snd p) := by
  intro u step
  cases step with
  | root impossible => exact no_root empty impossible
  | betaSigmaSnd _ _ => simp [fixedSkeleton] at skel
  | congSnd inner => exact normal _ inner

/-- **The η-expansion of a pair against a rigid neutral side keeps Miller normal reducts.** -/
theorem pairEta_reduct {n : Nat} (depth : Nat) (A pairSide other : Tm Head n) {code : Tm Head n}
    (mark : Fin n → Bool) (found : pairEtaCode depth A pairSide other = some code)
    (locals : ∀ i : Fin n, i.val < depth → mark i = false) (reduct : MarkedReduct R mark other) :
    MarkedReduct R mark code := by
  induction depth, A, pairSide, other using pairEtaCode.induct with
  | case1 n depth _ T pairSide' other' ih =>
      simp only [pairEtaCode, Option.map_eq_some_iff] at found
      obtain ⟨inner, innerFound, rfl⟩ := found
      refine MarkedReduct.lam empty (ih (liftFlexible mark) innerFound (fun i bound => ?_)
        (MarkedReduct.of_lam empty reduct))
      refine Fin.cases (fun _ => rfl) (fun j hj => ?_) i bound
      change mark j = false
      exact locals j (by simp only [Fin.val_succ] at hj; omega)
  | case2 n depth _ _ _ _ other' =>
      simp only [pairEtaCode, Option.map_eq_some_iff] at found
      obtain ⟨skel, skelFound, rfl⟩ := found
      obtain ⟨O, toO, normalO, millerO⟩ := reduct
      have skelO := fixedSkeleton_star empty skelFound toO
      have rigidHead := flexHead_of_skeleton mark skelO locals
      refine ⟨.pair (.fst O) (.snd O), star_pair (star_fst toO) (star_snd toO),
        (normal_pair_iff empty).mpr ⟨normal_fst_of_skeleton empty skelO normalO, normal_snd_of_skeleton empty skelO normalO⟩,
        ?_⟩
      simp only [miller, rigidHead, millerO, Bool.not_false, Bool.and_self]
  | case3 => simp_all [pairEtaCode]

end Raw

/-! ## Miller sides are closed Miller normal reducts -/

section Sides

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **On a strongly normalizing package, Miller sides give closed normal Miller reducts of both codes.** -/
theorem side_reduct (rigid : ∀ name, S.roles name = .rigid)
    (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) {Θ : Context S.R}
    {equation : Equation (TotalTerm Θ)} (sides : FragmentSidesMiller equation) :
    MarkedReduct S.R (fun _ => true) equation.1.2.code ∧ MarkedReduct S.R (fun _ => true) equation.2.2.code := by
  have empty := computation_empty rigid
  have one : ∀ {type : TypeOver Θ} (term : Term Θ type),
      (∀ N, Star (R := S.R) (openCode (lamDepth equation.1.2.code) term.code) N → Normal S.R N →
        miller (openedFlexible (lamDepth equation.1.2.code)) N = true) →
      MarkedReduct S.R (fun _ => true) term.code := by
    intro type term inside
    obtain ⟨T, toT, normalT⟩ := ContextualDependentOpenedNormal.term_normal sn term
    obtain ⟨N, toN, normalN⟩ := opens_normal empty normalT (lamDepth equation.1.2.code)
    exact ⟨T, toT, normalT, closed_of_sides empty normalT _ toN normalN
      (inside N ((ContextualDependentOpenedNormal.star_openCode toT _).trans toN) normalN)⟩
  exact ⟨one equation.1.2 sides.1, one equation.2.2 sides.2⟩

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

/-- **A certified re-expression has the candidate code.** -/
theorem reexpress_code (fuel : Nat) {Θ : Context S.R} (term : TotalTerm Θ) (code : Tm Head Θ.arity)
    {other : {other : TotalTerm Θ // (frames S.levels).E term other}}
    (found : reexpress facts roots heads algebra declared choices reducer fuel term code = some other) :
    other.val.2.code = code := by
  unfold reexpress reexpressWith at found
  split at found
  · obtain ⟨same, _, rfl⟩ := Option.map_eq_some_iff.mp found
    rfl
  · cases found

include rigid in
/-- **η for Σ keeps Miller sides.** -/
theorem expandOne_sides (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (sides : FragmentSidesMiller equation) :
    FragmentSidesMiller (expandOne facts roots heads algebra declared choices reducer fuel equation) := by
  have empty := computation_empty rigid
  obtain ⟨leftReduct, rightReduct⟩ := side_reduct rigid sn sides
  unfold expandOne
  split
  · rename_i right found
    obtain ⟨code, codeFound, reexpressed⟩ := Option.bind_eq_some_iff.mp found
    refine sides_of_reducts empty leftReduct ?_
    change MarkedReduct S.R (fun _ => true) right.val.2.code
    rw [reexpress_code facts roots heads algebra declared choices reducer fuel _ _ reexpressed]
    exact pairEta_reduct empty 0 _ _ _ _ codeFound (fun _ bound => absurd bound (Nat.not_lt_zero _)) rightReduct
  · split
    · rename_i left found
      obtain ⟨code, codeFound, reexpressed⟩ := Option.bind_eq_some_iff.mp found
      refine sides_of_reducts empty ?_ rightReduct
      change MarkedReduct S.R (fun _ => true) left.val.2.code
      rw [reexpress_code facts roots heads algebra declared choices reducer fuel _ _ reexpressed]
      exact pairEta_reduct empty 0 _ _ _ _ codeFound (fun _ bound => absurd bound (Nat.not_lt_zero _)) leftReduct
    · exact sides

/-- **η for Σ keeps stratified annotations**: the re-expressed side is equal to the old one. -/
theorem expandOne_annotations (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (before : EquationStore (TotalTerm Θ)) (stratified : StratifiedAt S.levels before equation) :
    StratifiedAt S.levels before (expandOne facts roots heads algebra declared choices reducer fuel equation) := by
  intro Δ σ solved
  have annotations := stratified σ solved
  unfold expandOne
  split
  · rename_i right _
    exact TypeEq.trans S.levels annotations ((frames S.levels).preserves σ right.property).1
  · split
    · rename_i left _
      exact TypeEq.trans S.levels ((frames S.levels).preserves σ left.property).1.symm annotations
    · exact annotations

variable (root : ExecutableReduction.RootEvaluator S.R)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)

include rigid in
/-- **R112's η for Σ on the prepared store keeps the permuted class** on a strongly normalizing package. -/
theorem expanded_keeps (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat) :
    UpdateKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      preparedExpanded facts roots heads algebra declared choices reducer root rootComplete fuel problem := by
  intro Θ problem permuted
  have prepared := prepare_keeps root rootComplete facts roots heads rigid sn fuel problem permuted
  change PermutedMiller S.levels ((ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel
    problem).remaining.map (expandOne facts roots heads algebra declared choices reducer fuel))
  exact prepared.map _ (fun equation _ σ => expandOne_solves facts roots heads algebra declared choices reducer fuel
      σ equation)
    (fun equation _ sides => expandOne_sides facts roots heads algebra rigid declared choices reducer sn fuel equation
      sides)
    (fun equation _ before stratified => expandOne_annotations facts roots heads algebra declared choices reducer fuel
      equation before stratified)

end Sides

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
