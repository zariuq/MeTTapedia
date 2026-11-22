import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentWorklist
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalizingSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPermutation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidDecompositionRule

/-!
# Every round of the dependent solver is eventually constant

Building on the worklist round:

* **decomposition**: the decomposition of one scoped equation reads one type formation, at the
  domain of a rigid local; it is eventually constant uniformly over the locals of the telescope.
  The decomposition of a store equation, the search through the store and the **decomposition
  round** are eventually constant;
* **rotation**: the context checker keeps its results, so every rotation, the rotation rule and the
  **permuting round** are eventually constant;
* **preparation**: context normalization keeps its results and endpoint normalization is eventually
  constant, so preparation, and the **normalizing round**, are eventually constant.

The **fragment round** composes all of them: prepare the store, then the decomposition round on the
prepared store, then, when that is stuck, rotation. It is again a worklist solver, with certified
refutations, and it is eventually constant on every store. Hence it settles on every class where,
from some budget on, it is not stuck and keeps its residual stores in the class.

A round is compared through its **view**: the update it commits, a refutation, or nothing. Two
rounds with the same view are equal, because the rank decrease and the refutation are proofs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFragment

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist ContextualDependentScope
open ContextualDependentPiSpine ContextualDependentPatternSolver
open ContextualDependentDecisiveFragment ContextualDependentConversionBudget

/-! ## The view of a round -/

section View

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}
variable {rank : {Γ : Context rules} → EquationStore (TotalTerm Γ) → Nat × Nat}

/-- What a round commits: an update, a refutation (`some none`), or nothing. -/
def roundView {Γ : Context rules} {problem : EquationStore (TotalTerm Γ)} :
    Round levels rank problem → Option (Option (Update levels problem))
  | .progress update _ => some (some update)
  | .refuted _ => some none
  | .stuck => none

theorem roundView_injective {Γ : Context rules} {problem : EquationStore (TotalTerm Γ)} :
    Function.Injective (roundView (levels := levels) (rank := rank) (problem := problem)) := by
  intro first second same
  cases first <;> cases second <;> simp_all [roundView]

/-- A round is eventually constant when its view is. -/
theorem round_const_of_view {Γ : Context rules} {problem : EquationStore (TotalTerm Γ)}
    {round : Nat → Round levels rank problem} (constant : EventuallyConst fun fuel => roundView (round fuel)) :
    EventuallyConst round :=
  EventuallyConst.of_injective roundView_injective constant

end View

/-! ## Uniform constancy of type formation over a telescope -/

section Uniform

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
variable (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))
include stable

/-- **Type formation at the domains of a context's Π-typed declarations is eventually constant,
uniformly**: one budget serves every declaration. -/
theorem formType_uniform (Γ : Context S.R) :
    ∃ threshold, ∀ fuel, threshold ≤ fuel →
      ∀ (index : Fin Γ.arity) (domain : Tm Head Γ.arity) (codomain : Tm Head (Γ.arity + 1)),
        Ctx.lookup Γ.raw index = .pi domain codomain →
        ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ domain =
          ContextualDependentPruning.formType facts roots heads algebra declared choices reducer threshold Γ domain := by
  have each : ∀ index : Fin Γ.arity, ∃ t, ∀ fuel, t ≤ fuel →
      ∀ (domain : Tm Head Γ.arity) (codomain : Tm Head (Γ.arity + 1)), Ctx.lookup Γ.raw index = .pi domain codomain →
        ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ domain =
          ContextualDependentPruning.formType facts roots heads algebra declared choices reducer t Γ domain := by
    intro index
    by_cases isPi : ∃ domain codomain, Ctx.lookup Γ.raw index = .pi domain codomain
    · obtain ⟨domain, codomain, shape⟩ := isPi
      obtain ⟨t, same⟩ := (formType_const facts roots heads algebra declared choices reducer stable
        (Γ := Γ) domain).spec
      refine ⟨t, fun fuel enough domain' codomain' found => ?_⟩
      rw [shape] at found
      cases found
      exact same fuel enough
    · exact ⟨0, fun _ _ domain codomain found => absurd ⟨domain, codomain, found⟩ isPi⟩
  choose t ht using each
  refine ⟨Finset.univ.sup t, fun fuel enough index domain codomain found => ?_⟩
  have le : t index ≤ Finset.univ.sup t := Finset.le_sup (Finset.mem_univ index)
  rw [ht index fuel (le.trans enough) domain codomain found, ht index _ le domain codomain found]

end Uniform

/-! ## Decomposition -/

section Decomposition

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (rigid : ∀ name, S.roles name = .rigid) (facts : FormFacts S.R S.roles)
  (complete : AlgorithmicComplete S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

/-- Decomposition of one scoped equation reads the budget only through one type formation, at the
domain of a rigid local. -/
theorem decomposeActive_congr {fuel larger : Nat} {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (active : Active scope.target)
    (same : ∀ (index : Fin scope.target.arity) (domain : Tm Head scope.target.arity)
      (codomain : Tm Head (scope.target.arity + 1)), Ctx.lookup scope.target.raw index = .pi domain codomain →
      ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel scope.target domain =
        ContextualDependentPruning.formType facts roots heads algebra declared choices reducer larger scope.target
          domain) :
    ContextualDependentRigidDecomposition.decomposeActive facts complete roots heads algebra declared choices reducer
        fuel scope active =
      ContextualDependentRigidDecomposition.decomposeActive facts complete roots heads algebra declared choices reducer
        larger scope active := by
  unfold ContextualDependentRigidDecomposition.decomposeActive
  split
  · rename_i head left head' right leftFound rightFound
    split
    · rename_i sameHead
      split
      · rename_i domain codomain headShape
        split
        · rename_i base
          rw [same _ domain codomain headShape]
        · rfl
      · rfl
    · rfl
  · rfl

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))
include stable

/-- **Decomposition of one scoped equation is eventually constant.** -/
theorem decomposeActive_const {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (active : Active scope.target) :
    EventuallyConst fun fuel =>
      ContextualDependentRigidDecomposition.decomposeActive facts complete roots heads algebra declared choices reducer
        fuel scope active := by
  obtain ⟨threshold, uniform⟩ := formType_uniform facts roots heads algebra declared choices reducer stable scope.target
  exact ⟨threshold, fun fuel enough => decomposeActive_congr facts complete roots heads algebra declared choices reducer
    scope active (uniform fuel enough)⟩

/-- **Decomposition of one store equation, continued by the distinct-locals and pattern rules, is
eventually constant.** -/
theorem decomposeEquation_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (rest : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      ContextualDependentRigidDecomposition.decomposeEquation rigid facts complete roots heads algebra declared choices
        reducer root normalizes certifyNormal fuel equation rest := by
  obtain ⟨t₁, viewed⟩ := (viewEquation_const facts roots heads algebra declared choices reducer root stable
    equation).spec
  cases viewRun : viewEquation facts roots heads algebra declared choices reducer root t₁ equation with
  | none =>
      refine ⟨t₁, fun fuel enough => ?_⟩
      dsimp only
      unfold ContextualDependentRigidDecomposition.decomposeEquation
      erw [viewed fuel enough, viewRun]
  | some reading =>
      obtain ⟨scope, active, view⟩ := reading
      obtain ⟨t₂, decomposed⟩ := (decomposeActive_const facts complete roots heads algebra declared choices reducer stable
        scope active).spec
      cases decomposeRun : ContextualDependentRigidDecomposition.decomposeActive facts complete roots heads algebra
          declared choices reducer t₂ scope active with
      | none =>
          refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
          dsimp only
          unfold ContextualDependentRigidDecomposition.decomposeEquation
          erw [viewed fuel (le_of_max_le_left enough), viewRun, viewed _ (le_max_left _ _), viewRun]
          dsimp only
          erw [decomposed fuel (le_of_max_le_right enough), decomposeRun, decomposed _ (le_max_right _ _), decomposeRun]
      | some found =>
          obtain ⟨argument, sameSolutions⟩ := found
          cases closing : (scope.toScoped argument).closeWith S.levels choices with
          | none =>
              refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
              dsimp only
              unfold ContextualDependentRigidDecomposition.decomposeEquation
              erw [viewed fuel (le_of_max_le_left enough), viewRun, viewed _ (le_max_left _ _), viewRun]
              dsimp only
              erw [decomposed fuel (le_of_max_le_right enough), decomposeRun, decomposed _ (le_max_right _ _),
                decomposeRun]
              dsimp only
              split
              · rfl
              · rename_i closed computed
                rw [computed] at closing
                cases closing
          | some closed₀ =>
              obtain ⟨t₃, localsSame⟩ := (localsRule_const facts roots heads algebra declared choices reducer root stable
                rigid complete (closed₀.equation :: rest)).spec
              obtain ⟨t₄, patternSame⟩ := (patternRule_const rigid facts complete roots heads algebra declared choices
                reducer root normalizes certifyNormal stable (closed₀.equation :: rest)).spec
              refine ⟨max (max t₁ t₂) (max t₃ t₄), fun fuel enough => ?_⟩
              have e₁ : t₁ ≤ fuel := by omega
              have e₂ : t₂ ≤ fuel := by omega
              have e₃ : t₃ ≤ fuel := by omega
              have e₄ : t₄ ≤ fuel := by omega
              have f₁ : t₁ ≤ max (max t₁ t₂) (max t₃ t₄) := by omega
              have f₂ : t₂ ≤ max (max t₁ t₂) (max t₃ t₄) := by omega
              have f₃ : t₃ ≤ max (max t₁ t₂) (max t₃ t₄) := by omega
              have f₄ : t₄ ≤ max (max t₁ t₂) (max t₃ t₄) := by omega
              dsimp only
              unfold ContextualDependentRigidDecomposition.decomposeEquation
              erw [viewed fuel e₁, viewRun, viewed _ f₁, viewRun]
              dsimp only
              erw [decomposed fuel e₂, decomposeRun, decomposed _ f₂, decomposeRun]
              dsimp only
              split
              · rfl
              · rename_i closed computed
                rw [computed] at closing
                cases closing
                erw [localsSame fuel e₃, localsSame _ f₃, patternSame fuel e₄, patternSame _ f₄]

/-- **The decomposition search through the store is eventually constant.** -/
theorem decomposeSearch_const {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), EventuallyConst fun fuel =>
      ContextualDependentRigidDecomposition.decomposeSearch rigid facts complete roots heads algebra declared choices
        reducer root normalizes certifyNormal fuel problem
  | [] => EventuallyConst.const _
  | equation :: rest => by
      obtain ⟨t₁, first⟩ := (decomposeEquation_const rigid facts complete roots heads algebra declared choices reducer
        root normalizes certifyNormal stable equation rest).spec
      obtain ⟨t₂, later⟩ := (decomposeSearch_const rest).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      dsimp only
      simp only [ContextualDependentRigidDecomposition.decomposeSearch]
      erw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), later fuel (le_of_max_le_right enough),
        later _ (le_max_right _ _)]

/-- **The decomposition round is eventually constant on every store**: decomposition, then the
rigid round. -/
theorem decomposeRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      ContextualDependentRigidDecomposition.decomposeRound rigid facts complete roots heads algebra declared choices
        reducer root normalizes certifyNormal headTypingUnique fuel problem := by
  obtain ⟨t₁, searched⟩ := (decomposeSearch_const rigid facts complete roots heads algebra declared choices reducer root
    normalizes certifyNormal stable problem).spec
  obtain ⟨t₂, rigidSame⟩ := (rigidRound_const rigid facts complete roots heads algebra declared choices reducer root
    normalizes certifyNormal headTypingUnique stable problem).spec
  refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
  dsimp only
  unfold ContextualDependentRigidDecomposition.decomposeRound
  erw [searched fuel (le_of_max_le_left enough), searched _ (le_max_left _ _)]
  cases ContextualDependentRigidDecomposition.decomposeSearch rigid facts complete roots heads algebra declared choices
      reducer root normalizes certifyNormal t₁ problem with
  | some found => cases found <;> rfl
  | none =>
      dsimp only
      rw [rigidSame fuel (le_of_max_le_right enough), rigidSame _ (le_max_right _ _)]

/-! ## Rotation -/

/-- The context checker keeps its results. -/
theorem formContext_const {n : Nat} (raw : Ctx Head n) :
    EventuallyConst fun fuel => ExecutableChecking.formContext S.R choices reducer fuel raw :=
  EventuallyConst.of_mono fun {fuel larger result} computed enough => by
    induction enough with
    | refl => exact computed
    | step _ ih => exact ContextualDependentCheckingBudget.formContext_succ S.R choices reducer stable _ raw result ih

/-- **One rotation is eventually constant.** -/
theorem rotateAt_const (depth : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      ContextualDependentPermutation.rotateAt rigid complete facts roots heads algebra declared choices reducer root
        normalizes certifyNormal fuel depth problem := by
  cases rotated : ContextualDependentPermutation.rotateRaw Θ.raw depth with
  | none =>
      refine ⟨0, fun fuel _ => ?_⟩
      dsimp only
      unfold ContextualDependentPermutation.rotateAt
      rw [rotated]
  | some raw =>
      obtain ⟨t₁, formed⟩ := (formContext_const choices reducer stable raw).spec
      cases formRun : ExecutableChecking.formContext S.R choices reducer t₁ raw with
      | none =>
          refine ⟨t₁, fun fuel enough => ?_⟩
          dsimp only
          unfold ContextualDependentPermutation.rotateAt
          rw [rotated]
          dsimp only
          erw [formed fuel enough, formRun]
      | some checked =>
          by_cases forth : CtxRen Θ.raw raw (ContextualDependentPermutation.rotRen Θ.arity depth)
          · by_cases back : CtxRen raw Θ.raw (ContextualDependentPermutation.rotInv Θ.arity depth)
            · by_cases inverse : ∀ i, ContextualDependentPermutation.rotInv Θ.arity depth
                  (ContextualDependentPermutation.rotRen Θ.arity depth i) = i
              · let rotatedContext : Context S.R :=
                  ⟨Θ.arity, raw, ExecutableChecking.ContextAlgorithm.sound facts roots heads algebra declared checked.down⟩
                let moved := ContextualDependentPermutation.ofRenamingIso S.levels problem (Θ' := rotatedContext)
                  (ContextualDependentPermutation.rotRen Θ.arity depth)
                  (ContextualDependentPermutation.rotInv Θ.arity depth) forth back inverse
                obtain ⟨t₂, patternSame⟩ := (patternRule_const rigid facts complete roots heads algebra declared choices
                  reducer root normalizes certifyNormal stable moved.remaining).spec
                refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
                dsimp only
                unfold ContextualDependentPermutation.rotateAt
                rw [rotated]
                dsimp only
                erw [formed fuel (le_of_max_le_left enough), formRun, formed _ (le_max_left _ _), formRun]
                dsimp only
                rw [dif_pos forth, dif_pos forth, dif_pos back, dif_pos back, dif_pos inverse, dif_pos inverse]
                erw [patternSame fuel (le_of_max_le_right enough), patternSame _ (le_max_right _ _)]
              · refine ⟨t₁, fun fuel enough => ?_⟩
                dsimp only
                unfold ContextualDependentPermutation.rotateAt
                rw [rotated]
                dsimp only
                erw [formed fuel enough, formRun]
                dsimp only
                rw [dif_pos forth, dif_pos forth, dif_pos back, dif_pos back, dif_neg inverse, dif_neg inverse]
            · refine ⟨t₁, fun fuel enough => ?_⟩
              dsimp only
              unfold ContextualDependentPermutation.rotateAt
              rw [rotated]
              dsimp only
              erw [formed fuel enough, formRun]
              dsimp only
              rw [dif_pos forth, dif_pos forth, dif_neg back, dif_neg back]
          · refine ⟨t₁, fun fuel enough => ?_⟩
            dsimp only
            unfold ContextualDependentPermutation.rotateAt
            rw [rotated]
            dsimp only
            erw [formed fuel enough, formRun]
            dsimp only
            rw [dif_neg forth, dif_neg forth]

/-- The rotations at a list of depths, tried in turn, are eventually constant. -/
theorem rotateSearch_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    ∀ depths : List Nat, EventuallyConst fun fuel =>
      ContextualDependentPermutation.rotateSearch rigid complete facts roots heads algebra declared choices reducer root
        normalizes certifyNormal fuel problem depths
  | [] => EventuallyConst.const _
  | depth :: rest => by
      obtain ⟨t₁, first⟩ := (rotateAt_const rigid facts complete roots heads algebra declared choices reducer root
        normalizes certifyNormal stable depth problem).spec
      obtain ⟨t₂, later⟩ := (rotateSearch_const problem rest).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      dsimp only
      simp only [ContextualDependentPermutation.rotateSearch]
      erw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), later fuel (le_of_max_le_right enough),
        later _ (le_max_right _ _)]

/-- **The rotation rule is eventually constant on every store.** -/
theorem rotateRule_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      ContextualDependentPermutation.rotateRule rigid complete facts roots heads algebra declared choices reducer root
        normalizes certifyNormal fuel problem :=
  rotateSearch_const rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
    stable problem _

/-- **The permuting round is eventually constant on every store.** -/
theorem permutingRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      ContextualDependentPermutation.permutingRound rigid complete facts roots heads algebra declared choices reducer
        root normalizes certifyNormal headTypingUnique fuel problem := by
  obtain ⟨t₁, rigidSame⟩ := (rigidRound_const rigid facts complete roots heads algebra declared choices reducer root
    normalizes certifyNormal headTypingUnique stable problem).spec
  obtain ⟨t₂, rotatedSame⟩ := (rotateRule_const rigid facts complete roots heads algebra declared choices reducer root
    normalizes certifyNormal stable problem).spec
  refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
  dsimp only
  unfold ContextualDependentPermutation.permutingRound
  erw [rigidSame fuel (le_of_max_le_left enough), rigidSame _ (le_max_left _ _)]
  cases ContextualDependentRigidDecomposition.rigidRound rigid complete facts roots heads algebra declared choices
      reducer root normalizes certifyNormal headTypingUnique t₁ problem with
  | progress update smaller => rfl
  | refuted absent => rfl
  | stuck =>
      dsimp only
      erw [rotatedSame fuel (le_of_max_le_right enough), rotatedSame _ (le_max_right _ _)]

end Decomposition

/-! ## Preparation and the normalizing round -/

section Preparation

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (root : ExecutableReduction.RootEvaluator S.R)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)
  (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)

/-- Store normalization is eventually constant. -/
theorem storeAt_const {Γ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Γ),
      EventuallyConst fun fuel => ContextualDependentNormalization.storeAt root facts roots heads fuel problem
  | [] => EventuallyConst.const _
  | equation :: rest => by
      obtain ⟨t₁, left⟩ := (termAt_const root facts roots heads equation.1).spec
      obtain ⟨t₂, right⟩ := (termAt_const root facts roots heads equation.2).spec
      obtain ⟨t₃, later⟩ := (storeAt_const rest).spec
      refine ⟨max t₁ (max t₂ t₃), fun fuel enough => ?_⟩
      have e₁ : t₁ ≤ fuel := by omega
      have e₂ : t₂ ≤ fuel := by omega
      have e₃ : t₃ ≤ fuel := by omega
      have f₁ : t₁ ≤ max t₁ (max t₂ t₃) := by omega
      have f₂ : t₂ ≤ max t₁ (max t₂ t₃) := by omega
      have f₃ : t₃ ≤ max t₁ (max t₂ t₃) := by omega
      have restSame : ContextualDependentNormalization.storeAt root facts roots heads fuel rest =
          ContextualDependentNormalization.storeAt root facts roots heads (max t₁ (max t₂ t₃)) rest :=
        (later fuel e₃).trans (later _ f₃).symm
      simp only [ContextualDependentNormalization.storeAt, List.map_cons] at restSame ⊢
      rw [restSame]
      erw [left fuel e₁, left _ f₁, right fuel e₂, right _ f₂]

/-- The normalization update is determined by its store. -/
theorem normalizationUpdate_const {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) :
    EventuallyConst fun fuel => ContextualDependentNormalization.update root facts roots heads fuel problem := by
  obtain ⟨threshold, same⟩ := (storeAt_const root facts roots heads problem).spec
  exact ⟨threshold, fun fuel enough => Update.ext' rfl HEq.rfl (heq_of_eq (same fuel enough))⟩

/-- **Preparation is eventually constant on every store.** -/
theorem prepare_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem := by
  have normalizeConst : EventuallyConst fun fuel =>
      ContextualDependentContextNormalization.normalize root rootComplete facts roots heads fuel Θ.raw Θ.formed :=
    EventuallyConst.of_mono fun computed enough =>
      ContextualDependentNormalizing.contextNormalize_mono root rootComplete facts roots heads computed enough
  have stepConst : EventuallyConst fun fuel =>
      ContextualDependentNormalizing.contextStep root rootComplete facts roots heads fuel problem := by
    obtain ⟨threshold, same⟩ := normalizeConst.spec
    refine ⟨threshold, fun fuel enough => ?_⟩
    dsimp only
    unfold ContextualDependentNormalizing.contextStep
    erw [same fuel enough]
  refine EventuallyConst.of_eq (fun fuel => rfl) ?_
  exact EventuallyConst.dep (h := fun fuel =>
      ContextualDependentNormalizing.contextStep root rootComplete facts roots heads fuel problem)
    (k := fun fuel step => step.then (ContextualDependentNormalization.update root facts roots heads fuel step.remaining))
    stepConst
    (fun step => EventuallyConst.comp (fun normalized => step.then normalized)
      (normalizationUpdate_const root facts roots heads step.remaining))

end Preparation

section Normalizing

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (rigid : ∀ name, S.roles name = .rigid) (facts : FormFacts S.R S.roles)
  (complete : AlgorithmicComplete S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

/-- The normalizing round, read through its view: the rigid round's view on the prepared store,
composed with preparation. -/
theorem normalizingRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (ContextualDependentNormalizing.normalizingRound rigid complete facts roots heads algebra declared choices
        reducer root rootComplete normalizes certifyNormal headTypingUnique fuel problem) =
      (roundView (ContextualDependentRigidDecomposition.rigidRound rigid complete facts roots heads algebra declared
          choices reducer root normalizes certifyNormal headTypingUnique fuel
          (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining)).map
        (Option.map fun update =>
          (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).then update) := by
  unfold ContextualDependentNormalizing.normalizingRound
  split <;> rename_i computed <;> simp only [computed, roundView, Option.map_some, Option.map_none]

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))
include stable

/-- **The normalizing round is eventually constant on every store.** -/
theorem normalizingRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      ContextualDependentNormalizing.normalizingRound rigid complete facts roots heads algebra declared choices reducer
        root rootComplete normalizes certifyNormal headTypingUnique fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => normalizingRound_view rigid facts complete roots heads algebra declared
    choices reducer root rootComplete normalizes certifyNormal headTypingUnique fuel problem) ?_
  exact EventuallyConst.dep (h := fun fuel =>
      ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem)
    (k := fun fuel prepared =>
      (roundView (ContextualDependentRigidDecomposition.rigidRound rigid complete facts roots heads algebra declared
          choices reducer root normalizes certifyNormal headTypingUnique fuel prepared.remaining)).map
        (Option.map fun update => prepared.then update))
    (prepare_const root rootComplete facts roots heads problem)
    (fun prepared => EventuallyConst.comp (fun round => (roundView round).map (Option.map fun update => prepared.then update))
      (rigidRound_const rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
        headTypingUnique stable prepared.remaining))

end Normalizing

end ContextualDependentFragment
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
