import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentWorklistFamily

/-!
# Preparation leaves a stopped store unchanged

A code is **stopped** when the executable reducer proposes no step for it. The executable
normalizer returns a stopped code itself, at every budget at which it returns anything. Hence:

* context normalization returns the same declarations on a context whose declarations are stopped;
* endpoint normalization returns the endpoint itself when its annotation and value are stopped;
* **preparation is the pending update** on a store whose context declarations, annotations and
  sides are all stopped (`prepare_stopped`), at every budget.

On such a store the fragment round is the decomposition round followed by rotation
(`fragmentRound_view_stopped`): preparation adds nothing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFragment

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist ContextualDependentScope
open ContextualDependentPatternSolver
open ContextualDependentDecisiveFragment ContextualDependentConversionBudget

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (root : ExecutableReduction.RootEvaluator S.R)

/-- **A context whose declarations are stopped.** -/
def StoppedContext : {n : Nat} → Ctx Head n → Prop
  | _, .nil => True
  | _, .snoc raw type => StoppedContext raw ∧ ExecutableReduction.step S.R root type = none

/-- **An endpoint whose annotation and value are stopped.** -/
def StoppedTerm {Γ : Context S.R} (term : TotalTerm Γ) : Prop :=
  ExecutableReduction.step S.R root term.1.code = none ∧ ExecutableReduction.step S.R root term.2.code = none

/-- **The normalizer returns a stopped code itself.** -/
theorem normalize_stopped {n : Nat} {code : Tm Head n} (stopped : ExecutableReduction.step S.R root code = none) :
    ∀ {fuel : Nat} {result : ExecutableReduction.Result S.R code},
      ExecutableReduction.normalize S.R root fuel code = some result → result.val = code
  | 0, _, computed => by simp [ExecutableReduction.normalize] at computed
  | fuel + 1, result, computed => by
      simp only [ExecutableReduction.normalize, stopped] at computed
      cases computed
      rfl

variable (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)
  (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)

/-- **Context normalization returns a stopped context's own declarations.** -/
theorem contextNormalize_stopped (fuel : Nat) {n : Nat} :
    ∀ (raw : Ctx Head n) (formed : CtxFormed S.R raw), StoppedContext root raw →
      ∀ {result : ContextualDependentContextNormalization.Normalized (S := S) raw},
        ContextualDependentContextNormalization.normalize root rootComplete facts roots heads fuel raw formed =
          some result → result.raw = raw
  | .nil, _, _, result, computed => by
      simp only [ContextualDependentContextNormalization.normalize] at computed
      cases computed
      rfl
  | .snoc raw type, formed, stopped, result, computed => by
      simp only [ContextualDependentContextNormalization.normalize] at computed
      split at computed
      · cases computed
      · rename_i prior priorRun
        have priorRaw := contextNormalize_stopped fuel raw _ stopped.1 priorRun
        split at computed
        · cases computed
        · rename_i reduced reducedRun
          cases computed
          change Ctx.snoc prior.raw reduced.val = Ctx.snoc raw type
          rw [priorRaw, normalize_stopped root stopped.2 reducedRun]

/-- Two endpoints with the same codes and annotation level are equal. -/
theorem totalTerm_ext {Γ : Context S.R} {first second : TotalTerm Γ} (type : first.1.code = second.1.code)
    (level : first.1.level = second.1.level) (value : first.2.code = second.2.code) : first = second := by
  obtain ⟨⟨code, levelA, universeA, formedA⟩, ⟨valueA, typedA⟩⟩ := first
  obtain ⟨⟨code', levelB, universeB, formedB⟩, ⟨valueB, typedB⟩⟩ := second
  change code = code' at type
  change levelA = levelB at level
  change valueA = valueB at value
  subst type level value
  rfl

/-- **Endpoint normalization returns a stopped endpoint itself.** -/
theorem termAt_stopped (fuel : Nat) {Γ : Context S.R} (term : TotalTerm Γ) (stopped : StoppedTerm root term) :
    ContextualDependentNormalization.termAt root facts roots heads fuel term = term := by
  unfold ContextualDependentNormalization.termAt
  cases computed : ContextualDependentNormalization.reduceTerm root facts roots heads fuel term with
  | none => rfl
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
          exact totalTerm_ext (normalize_stopped root stopped.1 annotationRun) rfl
            (normalize_stopped root stopped.2 valueRun)

/-- **Store normalization returns a stopped store itself.** -/
theorem storeAt_stopped (fuel : Nat) {Γ : Context S.R} :
    ∀ (problem : EquationStore (TotalTerm Γ)), (∀ equation ∈ problem, StoppedTerm root equation.1 ∧
      StoppedTerm root equation.2) →
      ContextualDependentNormalization.storeAt root facts roots heads fuel problem = problem
  | [], _ => rfl
  | equation :: rest, stopped => by
      simp only [ContextualDependentNormalization.storeAt, List.map_cons]
      have first := stopped equation List.mem_cons_self
      rw [termAt_stopped root facts roots heads fuel equation.1 first.1,
        termAt_stopped root facts roots heads fuel equation.2 first.2]
      have later := storeAt_stopped fuel rest (fun other member => stopped other (List.mem_cons_of_mem _ member))
      simp only [ContextualDependentNormalization.storeAt] at later
      rw [later]

/-- Reindexing along an identity-variable substitution leaves an endpoint unchanged. -/
theorem reindex_ids {Γ : Context S.R} (morphism : Γ ⟶ Γ) (identity : morphism.substitution = ids)
    (term : TotalTerm Γ) : term.reindex morphism = term := by
  apply totalTerm_ext
  · change subst morphism.substitution term.1.code = term.1.code
    rw [identity, subst_ids]
  · rfl
  · change subst morphism.substitution term.2.code = term.2.code
    rw [identity, subst_ids]

/-- **Preparation is the pending update on a stopped store**, at every budget. -/
theorem prepare_stopped (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (context : StoppedContext root Θ.raw)
    (codes : ∀ equation ∈ problem, StoppedTerm root equation.1 ∧ StoppedTerm root equation.2) :
    ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem =
      Update.pending S.levels problem := by
  obtain ⟨arity, raw, formed⟩ := Θ
  unfold ContextualDependentNormalizing.prepare ContextualDependentNormalizing.contextStep
  cases computed : ContextualDependentContextNormalization.normalize root rootComplete facts roots heads fuel raw formed with
  | none =>
    dsimp only
    refine Update.ext' rfl ?_ ?_
    · apply heq_of_eq
      exact Category.id_comp _
    · exact heq_of_eq (storeAt_stopped root facts roots heads fuel problem codes)
  | some normalized =>
    dsimp only
    have sameRaw := contextNormalize_stopped root rootComplete facts roots heads fuel raw formed context computed
    obtain ⟨raw', formed', normal', forward', backward'⟩ := normalized
    change raw' = raw at sameRaw
    subst sameRaw
    refine Update.ext' rfl ?_ ?_
    · apply heq_of_eq
      exact Hom.ext (subComp_ids_left _)
    · change HEq (ContextualDependentNormalization.storeAt root facts roots heads fuel
          ((frames S.levels).applyStore _ problem)) problem
      have each : ∀ equation ∈ problem, (equation.1.reindex
            (ContextualDependentContextNormalization.Normalized.iso
              (⟨raw', formed', normal', forward', backward'⟩ :
                ContextualDependentContextNormalization.Normalized (S := S) raw')).hom,
          equation.2.reindex (ContextualDependentContextNormalization.Normalized.iso
              (⟨raw', formed', normal', forward', backward'⟩ :
                ContextualDependentContextNormalization.Normalized (S := S) raw')).hom) = equation := by
        intro equation _
        exact Prod.ext (reindex_ids _ rfl equation.1) (reindex_ids _ rfl equation.2)
      have mapped : (frames S.levels).applyStore
          (ContextualDependentContextNormalization.Normalized.iso
            (⟨raw', formed', normal', forward', backward'⟩ :
              ContextualDependentContextNormalization.Normalized (S := S) raw')).hom problem = problem := by
        change problem.map _ = problem
        conv_rhs => rw [← List.map_id problem]
        exact List.map_congr_left each
      exact heq_of_eq ((congrArg (ContextualDependentNormalization.storeAt root facts roots heads fuel) mapped).trans
        (storeAt_stopped root facts roots heads fuel problem codes))

section Round

variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)
  (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

/-- **On a stopped store the fragment round is stuck exactly when the decomposition round is
stuck and no rotation fires.** -/
theorem fragmentRound_stuck_of_stopped (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (context : StoppedContext root Θ.raw)
    (codes : ∀ equation ∈ problem, StoppedTerm root equation.1 ∧ StoppedTerm root equation.2)
    (decomposed : ContextualDependentRigidDecomposition.decomposeRound rigid facts complete roots heads algebra declared
      choices reducer root normalizes certifyNormal headTypingUnique fuel problem = .stuck)
    (rotated : ContextualDependentPermutation.rotateRule rigid complete facts roots heads algebra declared choices
      reducer root normalizes certifyNormal fuel problem = none) :
    fragmentRound rigid facts complete roots heads algebra declared choices reducer root rootComplete normalizes
      certifyNormal headTypingUnique fuel problem = .stuck := by
  apply roundView_injective
  rw [fragmentRound_view, prepare_stopped root rootComplete facts roots heads fuel problem context codes]
  change ((roundView (ContextualDependentRigidDecomposition.decomposeRound rigid facts complete roots heads algebra
      declared choices reducer root normalizes certifyNormal headTypingUnique fuel problem)).or
    (foundView (ContextualDependentPermutation.rotateRule rigid complete facts roots heads algebra declared choices
      reducer root normalizes certifyNormal fuel problem))).map _ = _
  rw [decomposed, rotated]
  rfl

end Round

end ContextualDependentFragment
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
