import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosureCarryRule

/-!
# Closure of the cumulative round: R107's inversion in place and flex–flex across a declaration

R107's inversion in place (`ContextualDependentPatternFiring.placedRule`) is R86's in-place rule with R107's conversion
pattern rule at depth `0`; that rule is a drop under a reducing answer, so it is shaped (`patternRuleConv_shape`) and
every depth is (`placedAt_shape`).

The reorder rule (`ContextualDependentFlexReorder.reorderRule`) exchanges the two newest declarations when the newest
does not depend on the one below it, separates past the moved declaration, solves below it and carries the outcome
back, composed with the exchange (`exchangeThen`). The exchange reindexes the whole store along a renaming, so every
depth is shaped (`exchangeThen_shape`, `reorderAt_shape`).

Both rules are therefore stable, and they keep the permuted class (`placedRule_keeps`, `reorderRule_keeps`).
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
open ContextualDependentInPlace (separate separation carry)
open ContextualDependentParameterExchange (second)

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

/-! ## Inversion in place -/

include rigid in
theorem patternRuleConv_shape (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    SolvedShape (ContextualDependentRecognitionConversion.patternRuleConv facts roots heads algebra declared choices
      reducer rigid complete root normalizes certifyNormal fuel problem) := by
  unfold ContextualDependentRecognitionConversion.patternRuleConv
  split
  · exact SolvedShape.none
  · rename_i view _
    rcases view with ⟨base, newer, same⟩
    subst same
    exact fun update smaller fired sides => shape_of_drop
      (searchStoreConv_drops facts roots heads algebra declared choices reducer rigid complete root normalizes
        certifyNormal sn fuel newer problem sides update smaller fired)

include rigid in
theorem placedAt_shape (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat) :
    ∀ (depth : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)),
      SolvedShape (ContextualDependentPatternFiring.placedAt facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal fuel depth problem)
  | 0, _, problem => patternRuleConv_shape facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal sn fuel problem
  | depth + 1, Θ, problem => by
      simp only [ContextualDependentPatternFiring.placedAt]
      split
      · exact SolvedShape.none
      · rename_i view _
        exact SolvedShape.throughNewest view problem _ fun stored =>
          carry_shape view.type (separation facts roots heads algebra declared choices reducer fuel view.type
            stored).property
            (separate_codes facts roots heads algebra declared choices reducer fuel view.type stored)
            (separate_sides facts roots heads algebra rigid declared choices reducer sn fuel view.type stored)
            (placedAt_shape sn fuel depth _)

include rigid in
theorem placedSearch_shape (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    ∀ depths : List Nat, SolvedShape (ContextualDependentPatternFiring.placedSearch facts roots heads algebra rigid
      complete declared choices reducer root normalizes certifyNormal fuel problem depths)
  | [] => SolvedShape.none
  | depth :: rest => by
      intro update smaller fired
      simp only [ContextualDependentPatternFiring.placedSearch] at fired
      split at fired
      · rename_i found computed
        cases fired
        exact placedAt_shape facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal sn fuel depth problem update smaller computed
      · exact placedSearch_shape sn fuel problem rest update smaller fired

include rigid in
/-- **R107's inversion in place keeps the permuted class** on a strongly normalizing package. -/
theorem placedRule_keeps (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat) :
    RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      ContextualDependentPatternFiring.placedRule facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal fuel problem :=
  fun _ problem permuted => foundKeeps_of_stable permuted (SolvedShape.stable rigid sn
    (placedSearch_shape facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      sn fuel problem _))

/-! ## Flex–flex across a declaration -/

include rigid in
theorem exchangeThen_shape (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    (solve : {Γ : Context S.R} → (stored : EquationStore (TotalTerm Γ)) → Option (Found stored))
    (shaped : ∀ {Γ : Context S.R} (stored : EquationStore (TotalTerm Γ)), SolvedShape (solve stored))
    {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    (problem : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) :
    SolvedShape (ContextualDependentFlexReorder.exchangeThen facts roots heads algebra declared choices reducer fuel
      solve older newer problem) := by
  intro update smaller fired sides
  unfold ContextualDependentFlexReorder.exchangeThen at fired
  cases inverted : ContextualDependentInversion.invert (withoutNewest Γ₀.arity) newer.code with
  | none =>
      rw [inverted] at fired
      cases fired
  | some code =>
      rw [inverted] at fired
      dsimp only at fired
      split at fired
      · cases fired
      · rename_i next _
        split at fired
        · rename_i same
          obtain ⟨sameCode, sameLevel⟩ := same
          have independent := TypeOver.ext sameCode sameLevel
          subst independent
          dsimp only at fired
          unfold ContextualDependentFlexReorder.afterExchange at fired
          split at fired
          · cases fired
          · rename_i solved solvedSmaller computed
            cases fired
            refine Shape.then (exchange_shape rigid older next.val problem) ?_
            exact carry_shape (second next.val older)
              (separation facts roots heads algebra declared choices reducer fuel (second next.val older)
                (ContextualDependentPrune.exchange S.levels older next.val problem).remaining).property
              (separate_codes facts roots heads algebra declared choices reducer fuel (second next.val older)
                (ContextualDependentPrune.exchange S.levels older next.val problem).remaining)
              (separate_sides facts roots heads algebra rigid declared choices reducer sn fuel (second next.val older)
                (ContextualDependentPrune.exchange S.levels older next.val problem).remaining)
              (shaped _) solved solvedSmaller computed
              (Shape.sides rigid sn (exchange_shape rigid older next.val problem) sides)
          · cases fired
        · cases fired

include rigid in
theorem reorderAt_shape (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat) :
    ∀ (depth : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)),
      SolvedShape (ContextualDependentFlexReorder.reorderAt facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique fuel depth problem)
  | 0, _, problem => firstRule_shape facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique sn fuel problem
  | depth + 1, Θ, problem => by
      simp only [ContextualDependentFlexReorder.reorderAt]
      split
      · exact SolvedShape.none
      · split
        · exact SolvedShape.none
        · exact SolvedShape.throughTwo _ _ problem _ fun older newer stored =>
            exchangeThen_shape facts roots heads algebra rigid declared choices reducer sn fuel _
              (fun stored => reorderAt_shape sn fuel depth stored) older newer stored

include rigid in
theorem reorderSearch_shape (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    ∀ depths : List Nat, SolvedShape (ContextualDependentFlexReorder.reorderSearch facts roots heads algebra rigid
      complete declared choices reducer root normalizes certifyNormal headTypingUnique fuel problem depths)
  | [] => SolvedShape.none
  | depth :: rest => by
      intro update smaller fired
      simp only [ContextualDependentFlexReorder.reorderSearch] at fired
      split at fired
      · rename_i found computed
        cases fired
        exact reorderAt_shape facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique sn fuel depth problem update smaller computed
      · exact reorderSearch_shape sn fuel problem rest update smaller fired

include rigid in
/-- **Flex–flex across a declaration keeps the permuted class** on a strongly normalizing package. -/
theorem reorderRule_keeps (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat) :
    RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      ContextualDependentFlexReorder.reorderRule facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal headTypingUnique fuel problem :=
  fun _ problem permuted => foundKeeps_of_stable permuted (SolvedShape.stable rigid sn
    (reorderSearch_shape facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique sn fuel problem _))

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
