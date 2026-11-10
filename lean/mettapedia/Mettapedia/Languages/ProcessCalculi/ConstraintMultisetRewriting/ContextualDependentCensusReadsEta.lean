import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthPrepared

/-!
# The census half of coverage: distinct rigid heads at any abstraction depths

`ContextualDependentCensusReads` reads distinct rigid heads only when the right side has at least the left side's
abstractions, at the left side's depth. The η-long prepared family reads every depth: it η-expands both sides of the
prepared store with homogeneous twins to the annotation's Π count, and the clash reader reads the expanded sides.

The census head is carried there in four steps:

* twin collapse leaves it in place, homogeneous, from some budget on (`tower_twins_keep`);
* η-expansion maps it to an equation of the η-long store (`longUpdate_mem`), with normal codes when its codes are
  normal (`normal_expandTo`);
* preparation leaves every equation with normal codes in place, at every budget: context normalization substitutes
  the identity (`contextStep_codes`), and bounded normalization returns a reduct, hence the code itself
  (`termAt_normal`, `tower_prepare_keeps_codes`);
* twin collapse leaves a homogeneous equation unchanged (`collapseOne_homogeneous_self`), so R110's first row reads it
  (`tower_underReads_of_preparedClash`).

Hence **a census head whose η-expanded sides clash is read by the η-long prepared family from some budget on**
(`tower_etaReads_of_clash`), and through `headClash_of_opened` at the full depth (`lamDepth_expandTo`), every opened
clash of the η-long sides (`tower_etaReads_of_openedClash`) and every pair of distinct skeletons at a rigid base
(`tower_etaReads_of_skeletons`). This covers `λ g. g ≐ λ g x. x`, `λ g x. x ≐ λ g. g` and `λ g h. g ≐ λ g h x. h x`;
at a flexible base (`ContextualDependentEtaDepth.Controls.flexibleStore`) the clash reader does not apply.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentCoverageReadersHalf ContextualDependentTwinsUnder ContextualDependentConstantHeads
open ContextualDependentExecutableJoin ContextualDependentIntersectionGeneral ContextualDependentCensus

section Depth

variable {Head : Type}

/-- η-expansion reaches its depth. -/
theorem lamDepth_expandTo : ∀ (count : Nat) {n : Nat} (t : Tm Head n),
    count ≤ ContextualDependentPatternSolver.lamDepth (expandTo count t)
  | 0, _, _ => Nat.zero_le _
  | count + 1, _, t => by
      by_cases abstraction : ∃ body, t = .lam body
      · obtain ⟨body, rfl⟩ := abstraction
        have inner := lamDepth_expandTo count body
        simp only [expandTo, ContextualDependentPatternSolver.lamDepth]
        omega
      · have unfolds : expandTo (count + 1) t =
            .lam (expandTo count (.app (Presentation.rename wk t) (.var 0))) := by
          cases t <;> first | rfl | exact absurd ⟨_, rfl⟩ abstraction
        have inner := lamDepth_expandTo count (.app (Presentation.rename wk t) (.var 0))
        rw [unfolds]
        simp only [ContextualDependentPatternSolver.lamDepth]
        omega

end Depth

section General

variable {Head : Type} {R : Rules Head} (empty : R.computation = RootComputation.empty)
include empty

/-- **η-expansion keeps normal codes normal.** -/
theorem normal_expandTo : ∀ (count : Nat) {n : Nat} {t : Tm Head n}, Normal R t → Normal R (expandTo count t)
  | 0, _, _, normal => normal
  | count + 1, _, t, normal => by
      cases t
      case lam body =>
        exact (normal_lam_iff empty).mpr (normal_expandTo count ((normal_lam_iff empty).mp normal))
      all_goals
        exact (normal_lam_iff empty).mpr (normal_expandTo count ((normal_app_iff empty).mpr
          ⟨rfl, (ContextualDependentNormalizing.normal_rename_iff empty wk _).mpr normal, normal_var empty 0⟩))

end General

section Collapse

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]

/-- Twin collapse leaves a homogeneous equation unchanged. -/
theorem collapseOne_homogeneous_self (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
    (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (reducer : ExecutableReduction.Reducer S.R)
    (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (same : equation.2.1.code = equation.1.1.code) :
    collapseOne facts roots heads algebra reducer fuel equation = equation := by
  unfold collapseOne
  rw [if_pos same]

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq] in
/-- The η-expansion of an equation of a store is an equation of its η-long store. -/
theorem longUpdate_mem (facts : FormFacts S.R S.roles) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    {twin : Equation (TotalTerm Θ)} (member : twin ∈ problem) :
    (expandSide facts twin.1, expandSide facts twin.2) ∈ expandStore facts problem :=
  List.mem_map_of_mem member

variable [DecidableRel S.R.cumulative]
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

/-- **Reading the η-long prepared store**: an under-binder reader of the η-long store of the prepared store with
homogeneous twins reads the η-long prepared store. -/
theorem etaReads_of_expanded (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (reads : UnderReads facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel
      (expandStore facts (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).remaining)) :
    EtaReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem :=
  .inr reads

end Collapse

section Tower

open ContextualDependentPatternFiring.Controls ContextualDependentIntersectionGeneral.DeadControls

/-- The four codes of an equation are normal. -/
def NormalCodes {Γ : Context setting.R} (equation : Equation (TotalTerm Γ)) : Prop :=
  Normal Tower.rules equation.1.1.code ∧ Normal Tower.rules equation.1.2.code ∧
    Normal Tower.rules equation.2.1.code ∧ Normal Tower.rules equation.2.2.code

theorem red_normal (fuel : Nat) {n : Nat} {x : Tower.Tm n} (normal : Normal Tower.rules x)
    {result : ExecutableReduction.Result Tower.rules x}
    (computed : ExecutableReduction.normalize Tower.rules (fun _ => none) fuel x = some result) : result.val = x :=
  normal.star_eq (ContextualDependentExecutableConversion.normalize_star fuel computed)

/-- **Bounded normalization keeps normal codes.** -/
theorem termAt_normal (fuel : Nat) {Γ : Context setting.R} (term : TotalTerm Γ)
    (normalType : Normal Tower.rules term.1.code) (normalTerm : Normal Tower.rules term.2.code) :
    (ContextualDependentNormalization.termAt (S := setting) (fun _ => none) TowerModel.facts TowerModel.roots
        TowerModel.heads fuel term).1.code = term.1.code ∧
      (ContextualDependentNormalization.termAt (S := setting) (fun _ => none) TowerModel.facts TowerModel.roots
        TowerModel.heads fuel term).2.code = term.2.code := by
  unfold ContextualDependentNormalization.termAt
  cases computed : ContextualDependentNormalization.reduceTerm (S := setting) (fun _ => none) TowerModel.facts
      TowerModel.roots TowerModel.heads fuel term with
  | none => exact ⟨rfl, rfl⟩
  | some reduced =>
      unfold ContextualDependentNormalization.reduceTerm at computed
      split at computed
      · cases computed
      · split at computed
        · cases computed
        · rename_i annotation annotationRun value valueRun
          cases computed
          exact ⟨red_normal fuel normalType annotationRun, red_normal fuel normalTerm valueRun⟩

/-- **Context normalization leaves the codes of every equation in place.** -/
theorem contextStep_codes (fuel : Nat) {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {equation : Equation (TotalTerm Θ)} (member : equation ∈ problem)
    (holds : ∀ {n : Nat}, Tower.Tm n → Tower.Tm n → Tower.Tm n → Tower.Tm n → Prop)
    (shape : holds equation.1.1.code equation.1.2.code equation.2.1.code equation.2.2.code) :
    ∃ moved ∈ (ContextualDependentNormalizing.contextStep (S := setting) (fun _ => none)
        (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) TowerModel.facts TowerModel.roots
        TowerModel.heads fuel problem).remaining,
      holds moved.1.1.code moved.1.2.code moved.2.1.code moved.2.2.code := by
  unfold ContextualDependentNormalizing.contextStep
  split
  · exact ⟨equation, member, shape⟩
  · rename_i normalized _
    refine ⟨_, List.mem_map_of_mem member, ?_⟩
    change holds (subst ids equation.1.1.code) (subst ids equation.1.2.code) (subst ids equation.2.1.code)
      (subst ids equation.2.2.code)
    rw [subst_ids, subst_ids, subst_ids, subst_ids]
    exact shape

/-- **Preparation leaves every equation with normal codes in place**, at every budget. -/
theorem tower_prepare_keeps_codes (fuel : Nat) {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {equation : Equation (TotalTerm Θ)} (member : equation ∈ problem) (normal : NormalCodes equation)
    (holds : ∀ {n : Nat}, Tower.Tm n → Tower.Tm n → Tower.Tm n → Tower.Tm n → Prop)
    (shape : holds equation.1.1.code equation.1.2.code equation.2.1.code equation.2.2.code) :
    ∃ prepared ∈ (towerPrepare fuel problem).remaining,
      holds prepared.1.1.code prepared.1.2.code prepared.2.1.code prepared.2.2.code := by
  obtain ⟨moved, movedMember, movedNormal, movedShape⟩ := contextStep_codes fuel member
    (fun A l A' r => (Normal Tower.rules A ∧ Normal Tower.rules l ∧ Normal Tower.rules A' ∧ Normal Tower.rules r) ∧
      holds A l A' r) ⟨normal, shape⟩
  refine ⟨_, List.mem_map_of_mem movedMember, ?_⟩
  obtain ⟨leftType, leftTerm⟩ := termAt_normal fuel moved.1 movedNormal.1 movedNormal.2.1
  obtain ⟨rightType, rightTerm⟩ := termAt_normal fuel moved.2 movedNormal.2.2.1 movedNormal.2.2.2
  dsimp only
  rw [leftType, leftTerm, rightType, rightTerm]
  exact movedShape

/-- **A homogeneous clash on a prepared store is read** by R110's first row. -/
theorem tower_underReads_of_preparedClash {Γ : Context setting.R} (store : EquationStore (TotalTerm Γ)) (fuel : Nat)
    {prepared : Equation (TotalTerm (towerPrepare fuel store).target)}
    (member : prepared ∈ (towerPrepare fuel store).remaining) (same : prepared.2.1.code = prepared.1.1.code)
    (clash : HeadClash setting.R 0 prepared.1.1.code prepared.1.2.code prepared.2.2.code) :
    TowerUnderReads fuel store := by
  have inTwins := collapseOne_mem (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.reducer fuel member
  rw [collapseOne_homogeneous_self (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.reducer fuel prepared same] at inTwins
  exact .full (.inl (.inl (.inl ⟨prepared, inTwins, same, clash⟩)))

/-- **The clash reader reads a census head on the η-long prepared store**: a census head of a constant preparation,
with normal codes and equal annotations, whose sides, η-expanded to the annotation's Π count, clash at their heads, is
read by R110's first row on the η-long prepared store from some budget on. -/
theorem tower_etaReads_of_clash {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} {threshold : Nat}
    (constant : ∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem)
    {equation : Equation (TotalTerm (towerPrepare threshold problem).target)}
    (member : equation ∈ (towerPrepare threshold problem).remaining)
    (normal : ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation)
    (types : TypeEq setting.R (towerPrepare threshold problem).target.raw equation.1.1.code equation.2.1.code)
    (clash : HeadClash setting.R 0 equation.1.1.code (expandTo (piCount equation.1.1.code) equation.1.2.code)
      (expandTo (piCount equation.1.1.code) equation.2.2.code)) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerEtaReads larger problem := by
  have empty := ContextualDependentMillerClosure.computation_empty ContextualDependentPiSpine.Controls.rigid
  obtain ⟨bound, twins⟩ := tower_twins_keep constant member types
    (fun A l r => (Normal Tower.rules A ∧ Normal Tower.rules l ∧ Normal Tower.rules r) ∧
      HeadClash setting.R 0 A (expandTo (piCount A) l) (expandTo (piCount A) r))
    ⟨⟨normal.1, normal.2.1, normal.2.2.2⟩, clash⟩
  refine ⟨bound, fun larger enough => etaReads_of_expanded (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening larger ?_⟩
  obtain ⟨twin, twinMember, same, ⟨normalA, normalLeft, normalRight⟩, twinClash⟩ := twins larger enough
  have expandedMember := longUpdate_mem (S := setting) TowerModel.facts twinMember
  have expandedNormal : NormalCodes (expandSide TowerModel.facts twin.1, expandSide TowerModel.facts twin.2) := by
    refine ⟨normalA, normal_expandTo empty _ normalLeft, ?_, normal_expandTo empty _ normalRight⟩
    change Normal Tower.rules twin.2.1.code
    rw [same]
    exact normalA
  obtain ⟨prepared, preparedMember, preparedSame, preparedClash⟩ := tower_prepare_keeps_codes larger expandedMember
    expandedNormal (fun A l A' r => A' = A ∧ HeadClash setting.R 0 A l r)
    ⟨same, by
      change HeadClash setting.R 0 twin.1.1.code (expandTo (piCount twin.1.1.code) twin.1.2.code)
        (expandTo (piCount twin.2.1.code) twin.2.2.code)
      rw [same]
      exact twinClash⟩
  exact tower_underReads_of_preparedClash _ larger preparedMember preparedSame preparedClash

/-- **Distinct rigid heads of the η-long sides at the opened annotation are read** by the η-long prepared family:
the census row of distinct rigid heads at any abstraction depths of the two sides. -/
theorem tower_etaReads_of_openedClash {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {threshold : Nat}
    (constant : ∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem)
    {equation : Equation (TotalTerm (towerPrepare threshold problem).target)}
    (member : equation ∈ (towerPrepare threshold problem).remaining)
    (normal : ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation)
    (types : TypeEq setting.R (towerPrepare threshold problem).target.raw equation.1.1.code equation.2.1.code)
    (clash : HeadClash setting.R (piCount equation.1.1.code)
      (piOpen (piCount equation.1.1.code) equation.1.1.code)
      (openNormal (piCount equation.1.1.code) (expandTo (piCount equation.1.1.code) equation.1.2.code))
      (openNormal (piCount equation.1.1.code) (expandTo (piCount equation.1.1.code) equation.2.2.code))) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerEtaReads larger problem :=
  tower_etaReads_of_clash constant member normal types
    (headClash_of_opened le_rfl (lamDepth_expandTo _ _) (lamDepth_expandTo _ _) clash)

/-- **Distinct skeletons of the η-long sides at a rigid base are read** by the η-long prepared family. -/
theorem tower_etaReads_of_skeletons {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {threshold : Nat}
    (constant : ∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem)
    {equation : Equation (TotalTerm (towerPrepare threshold problem).target)}
    (member : equation ∈ (towerPrepare threshold problem).remaining)
    (normal : ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation)
    (types : TypeEq setting.R (towerPrepare threshold problem).target.raw equation.1.1.code equation.2.1.code)
    (base : ContextualDependentSpinesMany.rigidBase (piCount equation.1.1.code)
      (piOpen (piCount equation.1.1.code) equation.1.1.code) = true)
    {s s' : Skeleton}
    (leftSkeleton : fixedSkeleton (piCount equation.1.1.code)
      (openNormal (piCount equation.1.1.code) (expandTo (piCount equation.1.1.code) equation.1.2.code)) = some s)
    (rightSkeleton : fixedSkeleton (piCount equation.1.1.code)
      (openNormal (piCount equation.1.1.code) (expandTo (piCount equation.1.1.code) equation.2.2.code)) = some s')
    (differ : s ≠ s') :
    ∃ bound, ∀ larger, bound ≤ larger → TowerEtaReads larger problem :=
  tower_etaReads_of_openedClash constant member normal types (.base base leftSkeleton rightSkeleton differ)

end Tower

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
