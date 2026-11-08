import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentMillerClosureRotation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentMillerClosureReorderOutside

/-!
# The permuted Miller class

`StratifiedMiller` reads the store in its order: each equation's annotations are equal under every solution of the
equations **before** it. R86's in-place step reorders the store, and the reorder witness
(`ReorderControls.inPlace_not_closed`) leaves the class that way. The corrected class asks for the stratification up to
the order of the store:

  `PermutedMiller levels problem := ∃ ordered, ordered ~ problem ∧ StratifiedMiller levels ordered`.

* It contains `StratifiedMiller` (`PermutedMiller.of_stratifiedMiller`), hence the dynamic pattern fragment
  (`permutedMiller_of_fragment`), and it is closed under every permutation of the store (`PermutedMiller.perm`).
* It contains the witness's residual store (`ReorderControls.reorder_residual_permuted`), which `StratifiedMiller` does
  not: its two equations in the other order are the intersection, then the twin, stratified after it.
* Solutions do not see the order (`models_perm`).
* **Dropping an equation under a pattern answer keeps the class**, wherever the equation sits in the stratified order
  (`permutedMiller_of_headDrop`), by R116's answer closure and drop at any position. So the class is closed under every
  progress of general intersection, of rotation then intersection, and of in-place intersection.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentMillerClosure

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentIntersection ContextualDependentIntersectionGeneral
open ContextualDependentDynamicFragment ContextualDependentShortClosure ContextualDependentHereditary
open ContextualDependentClosure

/-! ## The class -/

section Class

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}

/-- **The permuted Miller class**: some order of the store is in the stratified Miller class. -/
def PermutedMiller (levels : LevelModel rules L) {Θ : Context rules} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  ∃ ordered : EquationStore (TotalTerm Θ), ordered.Perm problem ∧ StratifiedMiller levels ordered

variable {levels : LevelModel rules L}

theorem PermutedMiller.of_stratifiedMiller {Θ : Context rules} {problem : EquationStore (TotalTerm Θ)}
    (stratified : StratifiedMiller levels problem) : PermutedMiller levels problem :=
  ⟨problem, List.Perm.refl _, stratified⟩

/-- **The permuted Miller class contains the dynamic pattern fragment.** -/
theorem permutedMiller_of_fragment {Θ : Context rules} {problem : EquationStore (TotalTerm Θ)}
    (inside : InFragmentStore problem) : PermutedMiller levels problem :=
  .of_stratifiedMiller (stratifiedMiller_of_fragment inside)

theorem PermutedMiller.perm {Θ : Context rules} {problem problem' : EquationStore (TotalTerm Θ)}
    (permuted : PermutedMiller levels problem) (perm : problem.Perm problem') : PermutedMiller levels problem' := by
  obtain ⟨ordered, first, stratified⟩ := permuted
  exact ⟨ordered, first.trans perm, stratified⟩

/-- Solutions do not see the order of a store. -/
theorem models_perm {Θ Δ : Context rules} (σ : Δ ⟶ Θ) {problem problem' : EquationStore (TotalTerm Θ)}
    (perm : problem.Perm problem') : (frames levels).Models σ problem ↔ (frames levels).Models σ problem' :=
  ⟨fun solved equation member => solved equation (perm.symm.subset member),
    fun solved equation member => solved equation (perm.subset member)⟩

end Class

/-! ## Dropping an equation under a pattern answer -/

section Drop

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

theorem OpenedNormal.perm {Θ : Context S.R} {problem problem' : EquationStore (TotalTerm Θ)}
    (opened : OpenedNormal problem) (perm : problem'.Perm problem) : OpenedNormal problem' :=
  fun equation member => opened equation (perm.subset member)

/-- **Dropping an equation under a pattern answer keeps the permuted class**, wherever that equation sits in the
stratified order. -/
theorem permutedMiller_answer_drop (rigid : ∀ name, S.roles name = .rigid) {Θ Δ : Context S.R} (σ : Δ ⟶ Θ)
    (answer : PatternAnswer S.R (bodyFlexible (o := Θ.arity) 0) (bodyFlexible (o := Δ.arity) 0) σ.substitution)
    {first : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (permuted : PermutedMiller S.levels (first :: rest)) (opened : OpenedNormal (first :: rest))
    (valid : ∀ {Δ' : Context S.R} (τ : Δ' ⟶ Δ), (frames S.levels).Solves τ (first.1.reindex σ, first.2.reindex σ)) :
    PermutedMiller S.levels ((frames S.levels).applyStore σ rest) := by
  obtain ⟨ordered, perm, stratified⟩ := permuted
  obtain ⟨before, after, rfl⟩ := List.append_of_mem (perm.symm.subset List.mem_cons_self)
  have restPerm : (before ++ after).Perm rest := (List.perm_middle.symm.trans perm).cons_inv
  have applied := stratifiedMiller_applyStore (levels := S.levels) (computation_empty rigid) σ answer stratified
    (opened.perm perm)
  have split : (frames S.levels).applyStore σ (before ++ first :: after) =
      (frames S.levels).applyStore σ before ++ (first.1.reindex σ, first.2.reindex σ) ::
        (frames S.levels).applyStore σ after := by
    simp only [Interface.Frames.applyStore, List.map_append, List.map_cons]
    rfl
  rw [split] at applied
  refine ⟨_, ?_, stratifiedMiller_drop applied valid⟩
  have mapped := restPerm.map fun equation : Equation (TotalTerm Θ) => (equation.1.reindex σ, equation.2.reindex σ)
  simp only [List.map_append] at mapped
  exact mapped

/-- **Dropping the first equation under a pattern answer keeps the permuted class**, wherever that equation sits in
the stratified order. -/
theorem permutedMiller_of_headDrop (rigid : ∀ name, S.roles name = .rigid) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} {update : Update S.levels problem}
    (permuted : PermutedMiller S.levels problem) (opened : OpenedNormal problem) (drops : HeadDrop problem update) :
    PermutedMiller S.levels update.remaining := by
  obtain ⟨first, rest, σ, rfl, _, remaining, valid, ⟨answer⟩⟩ := drops
  rw [remaining]
  exact permutedMiller_answer_drop rigid σ answer permuted opened valid

/-- Every equation of a store of the permuted class has Miller sides. -/
theorem PermutedMiller.sides_of_mem {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (permuted : PermutedMiller S.levels problem) {equation : Equation (TotalTerm Θ)} (member : equation ∈ problem) :
    FragmentSidesMiller equation := by
  obtain ⟨ordered, perm, stratified⟩ := permuted
  exact StratifiedMiller.sides_of_mem stratified (perm.symm.subset member)

end Drop

/-! ## The intersection rules -/

section Rules

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
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

include rigid in
/-- **The permuted class is closed under every progress of the general intersection rule.** -/
theorem permutedMiller_generalIntersectRule (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (permuted : PermutedMiller S.levels problem) (opened : OpenedNormal problem)
    {found : Progress facts roots heads algebra rigid complete problem}
    (fired : generalIntersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel problem = some found) :
    PermutedMiller S.levels found.val.remaining :=
  permutedMiller_of_headDrop rigid permuted opened
    (generalIntersectRule_headDrop facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel problem fired)

include rigid in
/-- **The permuted class is closed under every progress of the older intersection rule.** -/
theorem permutedMiller_olderIntersectRule (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (permuted : PermutedMiller S.levels problem) (opened : OpenedNormal problem)
    {found : Progress facts roots heads algebra rigid complete problem}
    (fired : olderIntersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel problem = some found) :
    PermutedMiller S.levels found.val.remaining :=
  permutedMiller_of_headDrop rigid permuted opened
    (rotateIntersectSearch_headDrop facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel problem _ fired)

include rigid in
/-- **The permuted class is closed under every in-place intersection progress.** -/
theorem permutedMiller_inPlaceIntersectAt (fuel depth : Nat) {Θ : Context S.R}
    (problem : EquationStore (TotalTerm Θ)) (permuted : PermutedMiller S.levels problem)
    (opened : OpenedNormal problem) {found : SitedProgress facts roots heads algebra rigid complete problem}
    (fired : inPlaceIntersectAt facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel depth problem = some found) :
    PermutedMiller S.levels found.val.remaining :=
  permutedMiller_of_headDrop rigid permuted opened
    (inPlaceIntersectAt_headDrop facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel depth problem fired)

end Rules

/-! ## The witness's residual store is in the permuted class -/

namespace ReorderControls

open ContextualDependentPatternFiring.Controls ContextualDependentIntersectionGeneral.InPlaceControls
open ContextualDependentShortClosure.Controls

/-- The twin's annotations are `G a b` and `G b a` for variables `a b` of `U0`, and the other equation is
`λ x y. G x y ≐ λ x y. G y x` at `U0 → U0 → U0`. -/
def symmetricTwin {Θ : Context setting.R} (symmetric twin : Equation (TotalTerm Θ)) : Bool :=
  match binaryNeutral twin.1.1.code with
  | some (g, a, b) => decide (twin.2.1.code = .app (.app (.var g) (.var b)) (.var a) ∧
      symmetric.1.1.code = binaryFamily ∧
      symmetric.1.2.code = .lam (.lam (.app (.app (Presentation.rename wk (Presentation.rename wk (.var g)))
        (.var 1)) (.var 0))) ∧
      symmetric.2.2.code = .lam (.lam (.app (.app (Presentation.rename wk (Presentation.rename wk (.var g)))
        (.var 0)) (.var 1))) ∧
      Ctx.lookup Θ.raw a = .head (.sort Tower.zero) ∧ Ctx.lookup Θ.raw b = .head (.sort Tower.zero))
  | none => false

/-- **A twin at `G a b` and `G b a` is stratified after `λ x y. G x y ≐ λ x y. G y x`.** -/
theorem symmetricTwin_sound {Θ : Context setting.R} {symmetric twin : Equation (TotalTerm Θ)}
    (check : symmetricTwin symmetric twin = true) : StratifiedAt setting.levels [symmetric] twin := by
  unfold symmetricTwin at check
  split at check
  · rename_i g a b read
    obtain ⟨rightCode, binaryCode, leftTerm, rightTerm, lookupA, lookupB⟩ := of_decide_eq_true check
    have leftCode := binaryNeutral_eq read
    intro Δ σ solved
    have held := ((models_iff setting.levels σ [symmetric]).mp solved symmetric List.mem_cons_self).2
    rw [binaryCode, leftTerm, rightTerm] at held
    rw [leftCode, rightCode]
    change Equal setting.R Δ.raw
        (.lam (.lam (.app (.app (Presentation.rename wk (Presentation.rename wk (σ.substitution g))) (.var 1))
          (.var 0))))
        (.lam (.lam (.app (.app (Presentation.rename wk (Presentation.rename wk (σ.substitution g))) (.var 0))
          (.var 1))))
        (.pi (.head (.sort Tower.zero)) (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero)))) at held
    change TypeEq setting.R Δ.raw (.app (.app (σ.substitution g) (σ.substitution a)) (σ.substitution b))
      (.app (.app (σ.substitution g) (σ.substitution b)) (σ.substitution a))
    have ta : Typed setting.R Δ.raw (σ.substitution a) (.head (.sort Tower.zero)) := by
      have typed := σ.typed a
      rw [lookupA] at typed
      exact typed
    have tb : Typed setting.R Δ.raw (σ.substitution b) (.head (.sort Tower.zero)) := by
      have typed := σ.typed b
      rw [lookupB] at typed
      exact typed
    have applied := Derivable.appCong (Derivable.appCong held (.refl ta)) (.refl tb)
    change Equal setting.R Δ.raw _ _ (.head (.sort Tower.zero)) at applied
    obtain ⟨leftBeta, rightBeta⟩ := beta_two (σ.substitution g) (σ.substitution a) (σ.substitution b)
    have leftRed : WhRed setting.R setting.roles
        (.app (.app (.lam (.lam (.app (.app (Presentation.rename wk (Presentation.rename wk (σ.substitution g)))
          (.var 1)) (.var 0)))) (σ.substitution a)) (σ.substitution b))
        (.app (.app (σ.substitution g) (σ.substitution a)) (σ.substitution b)) := by
      rw [← leftBeta]
      exact (Relation.ReflTransGen.single (WhStep.appFun (WhStep.beta _ _))).tail (WhStep.beta _ _)
    have rightRed : WhRed setting.R setting.roles
        (.app (.app (.lam (.lam (.app (.app (Presentation.rename wk (Presentation.rename wk (σ.substitution g)))
          (.var 0)) (.var 1)))) (σ.substitution a)) (σ.substitution b))
        (.app (.app (σ.substitution g) (σ.substitution b)) (σ.substitution a)) := by
      rw [← rightBeta]
      exact (Relation.ReflTransGen.single (WhStep.appFun (WhStep.beta _ _))).tail (WhStep.beta _ _)
    have left := (WhRed.preserve TowerModel.facts TowerModel.roots Δ.formed leftRed
      (Equal.typed applied Δ.formed).1).2
    have right := (WhRed.preserve TowerModel.facts TowerModel.roots Δ.formed rightRed
      (Equal.typed applied Δ.formed).2).2
    exact ⟨.sort Tower.zero, .sort _, left.symm.trans (applied.trans right)⟩
  · cases check

/-- A store of a twin then the intersection it depends on, both with Miller sides. -/
def twinThenSymmetric {Θ : Context setting.R} : EquationStore (TotalTerm Θ) → Bool
  | [twin, symmetric] => sidesMiller twin && sidesMiller symmetric &&
      decide (symmetric.1.1.code = symmetric.2.1.code) && symmetricTwin symmetric twin
  | _ => false

theorem permutedMiller_of_twinThenSymmetric {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (check : twinThenSymmetric problem = true) : PermutedMiller setting.levels problem := by
  match problem, check with
  | [twin, symmetric], check =>
      simp only [twinThenSymmetric, Bool.and_eq_true, decide_eq_true_eq] at check
      obtain ⟨⟨⟨millerTwin, millerSymmetric⟩, annotations⟩, stratifiedTwin⟩ := check
      exact ⟨[symmetric, twin], List.Perm.swap twin symmetric [],
        stratifiedMiller_pair symmetric twin (sidesMiller_sound millerSymmetric) (sidesMiller_sound millerTwin)
          annotations (symmetricTwin_sound stratifiedTwin)⟩

noncomputable def residualPermuted : Bool :=
  match run inPlaceOnly reorderStore 1 with
  | .cutoff state => twinThenSymmetric state.remaining
  | _ => false

theorem residualPermuted_true : residualPermuted = true := by decide +kernel

/-- **The witness's residual store is in the permuted class and outside `StratifiedMiller`.** -/
theorem reorder_residual_permuted :
    ∃ state : ContextualDependentUpdate.Update setting.levels reorderStore,
      run inPlaceOnly reorderStore 1 = .cutoff state ∧ PermutedMiller setting.levels state.remaining ∧
        ¬ StratifiedMiller setting.levels state.remaining := by
  have key := residualPermuted_true
  have outside := outsideAfterOne_true
  unfold residualPermuted at key
  unfold outsideAfterOne at outside
  generalize ran : run inPlaceOnly reorderStore 1 = outcome at key outside
  cases outcome with
  | cutoff state => exact ⟨state, rfl, permutedMiller_of_twinThenSymmetric key, not_stratifiedMiller_of_check outside⟩
  | solved _ _ => simp at key
  | refuted _ => simp at key
  | stuck _ => simp at key

end ReorderControls
end ContextualDependentMillerClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
