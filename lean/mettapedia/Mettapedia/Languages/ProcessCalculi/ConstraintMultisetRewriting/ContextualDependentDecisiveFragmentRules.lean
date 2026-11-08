import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDecisiveFragmentPattern

/-!
# The prune and exchange rules are eventually constant

The prune rule reads two newest declarations, recognizes a pattern for the newest, discovers the
older metavariable's spine, forms the pruned type and its spine, and runs the pattern search after
exchanging; the exchange rule strengthens the newest declaration, forms it, and runs the pattern
search after exchanging. Every budget-dependent step is eventually constant and every other step is
a budget-free reader, so both rules are **eventually constant on every store**.

Hence the rigid round settles on every class on which, at each nonempty store, one of the
distinct-locals, pattern, prune or exchange rules fires at every large enough budget, and on which
every progressing answer stays in the class.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentDecisiveFragment

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiSpine ContextualDependentScope ContextualDependentConversionBudget
open ContextualDependentGeneralPattern ContextualDependentWorklist ContextualDependentPatternSolver
open ContextualDependentUpdate

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
variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))
include stable

/-- **The exchange rule at the two newest declarations is eventually constant.** -/
theorem exchangeAt_const {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    (problem : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) :
    EventuallyConst fun fuel =>
      exchangeAt rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal fuel
        older newer problem := by
  cases problem with
  | nil => exact ⟨0, fun _ _ => rfl⟩
  | cons equation rest =>
      cases inverted : ContextualDependentInversion.invert (withoutNewest Γ₀.arity) newer.code with
      | none =>
          refine ⟨0, fun fuel _ => ?_⟩
          dsimp only
          unfold exchangeAt
          simp only [inverted]
      | some code =>
          obtain ⟨t₁, formed⟩ := (formType_const facts roots heads algebra declared choices reducer stable
            (Γ := Γ₀) code).spec
          cases next : ContextualDependentPruning.formType facts roots heads algebra declared choices reducer t₁ Γ₀ code with
          | none =>
              refine ⟨t₁, fun fuel enough => ?_⟩
              dsimp only
              unfold exchangeAt
              simp only [inverted]
              erw [formed fuel enough, next]
          | some formedType =>
              by_cases same : newer.code = (ContextualDependentParameterExchange.second older formedType.val).code ∧
                  newer.level = (ContextualDependentParameterExchange.second older formedType.val).level
              · have independent : newer = ContextualDependentParameterExchange.second older formedType.val :=
                  TypeOver.ext same.1 same.2
                subst independent
                obtain ⟨t₂, searched⟩ := (searchStore_const rigid facts complete roots heads algebra declared choices
                  reducer root normalizes certifyNormal stable (ContextualDependentParameterExchange.second formedType.val older)
                  (ContextualDependentPrune.exchange S.levels older formedType.val (equation :: rest)).remaining).spec
                refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
                dsimp only
                unfold exchangeAt
                simp only [inverted]
                erw [formed fuel (le_of_max_le_left enough), next, formed _ (le_max_left _ _), next]
                dsimp only
                rw [dif_pos same, dif_pos same]
                erw [searched fuel (le_of_max_le_right enough), searched _ (le_max_right _ _)]
              · refine ⟨t₁, fun fuel enough => ?_⟩
                dsimp only
                unfold exchangeAt
                simp only [inverted]
                erw [formed fuel enough, next]
                dsimp only
                rw [dif_neg same, dif_neg same]

omit stable [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative] in
theorem throughTwo_const {Θ : Context S.R} (outer : Newest Θ) (inner : Newest outer.base)
    (problem : EquationStore (TotalTerm Θ))
    (solve : Nat → {Γ₀ : Context S.R} → (older : TypeOver Γ₀) → (newer : TypeOver (extend Γ₀ older)) →
      (stored : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) → Option (Found stored))
    (constant : ∀ {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older)) stored,
      EventuallyConst fun fuel => solve fuel older newer stored) :
    EventuallyConst fun fuel => throughTwo outer inner problem (solve fuel) := by
  cases outer with
  | mk base newer same =>
      cases inner with
      | mk base₀ older same₀ =>
          change base = extend base₀ older at same₀
          subst same₀
          subst same
          exact constant older newer problem

/-- **The exchange rule is eventually constant on every store.** -/
theorem exchangeRule_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      exchangeRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal fuel
        problem := by
  obtain ⟨t₁, outerSame⟩ := (newestOf_const facts roots heads algebra declared choices reducer stable Θ).spec
  cases outer : newestOf facts roots heads algebra declared choices reducer t₁ Θ with
  | none =>
      refine ⟨t₁, fun fuel enough => ?_⟩
      dsimp only
      unfold exchangeRule
      erw [outerSame fuel enough, outer]
  | some outerView =>
      obtain ⟨t₂, innerSame⟩ := (newestOf_const facts roots heads algebra declared choices reducer stable
        outerView.base).spec
      cases inner : newestOf facts roots heads algebra declared choices reducer t₂ outerView.base with
      | none =>
          refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
          dsimp only
          unfold exchangeRule
          erw [outerSame fuel (le_of_max_le_left enough), outer, outerSame _ (le_max_left _ _), outer]
          dsimp only
          erw [innerSame fuel (le_of_max_le_right enough), inner, innerSame _ (le_max_right _ _), inner]
      | some innerView =>
          obtain ⟨t₃, through⟩ := (throughTwo_const outerView innerView problem
            (fun fuel {_} older newer stored => exchangeAt rigid facts complete roots heads algebra declared choices reducer
              root normalizes certifyNormal fuel older newer stored)
            (fun older newer stored => exchangeAt_const rigid facts complete roots heads algebra declared choices reducer
              root normalizes certifyNormal stable older newer stored)).spec
          refine ⟨max t₁ (max t₂ t₃), fun fuel enough => ?_⟩
          have e₁ : t₁ ≤ fuel := by omega
          have e₂ : t₂ ≤ fuel := by omega
          have e₃ : t₃ ≤ fuel := by omega
          dsimp only
          unfold exchangeRule
          erw [outerSame fuel e₁, outer, outerSame _ (by omega), outer]
          dsimp only
          erw [innerSame fuel e₂, inner, innerSame _ (by omega), inner]
          dsimp only
          exact (through fuel e₃).trans (through _ (by omega)).symm

end ContextualDependentDecisiveFragment
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
