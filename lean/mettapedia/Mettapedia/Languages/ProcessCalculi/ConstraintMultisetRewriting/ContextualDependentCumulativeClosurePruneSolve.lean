import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosureStable

/-!
# Closure of the cumulative round: R110's prune-and-solve rule

The prune-and-solve rule (`ContextualDependentPruneSolve.pruneSolveRule`) prunes `G` under a rigid binder context
(R76's pruning, `prune_stable`), exchanges `F` and the pruned metavariable (`exchange_stable`), and runs R75's pattern
search for `F` (`searchStore_stable`), at the two newest declarations as they are or after exchanging them. Each step is
stable, so the rule keeps the permuted class (`pruneSolveRule_keeps`).
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
open ContextualDependentPiSpine ContextualDependentScope ContextualDependentPruneSolve

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

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
/-- A decided branch of stable outcomes is stable. -/
theorem SolvedStable.dite {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {c : Prop} {decided : Decidable c}
    {yes : c → Option (Found problem)} {no : ¬ c → Option (Found problem)} (keepsYes : ∀ h, SolvedStable (yes h))
    (keepsNo : ∀ h, SolvedStable (no h)) : SolvedStable (@dite _ c decided yes no) := by
  cases decided with
  | isTrue h => exact keepsYes h
  | isFalse h => exact keepsNo h

include rigid in
/-- **R75's pattern search is stable.** -/
theorem searchStore_stable (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ : Context S.R} (type : TypeOver Γ) (problem : EquationStore (TotalTerm (extend Γ type)))
    {update : Update S.levels problem} {smaller : update.target.arity < (extend Γ type).arity}
    (computed : searchStore rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal fuel type problem = some (.solved update smaller)) :
    StableKeeps update := by
  intro before permuted
  exact stableKeeps_of_reducingDrop rigid sn
    (searchStore_drops facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
      sn fuel type problem (fun _ member => permuted.sides_of_mem (List.mem_append_right _ member)) update smaller
      computed) before permuted

include rigid in
theorem tryContext_stable (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    {scopeType : TypeOver (extend (extend Γ₀ older) newer)} (scope : Spine scopeType)
    (active : Active scope.target) (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend (extend Γ₀ older) newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) {u : Head}
    (hu : S.R.isUniverse u) (annotation : active.type.code = .head u) :
    SolvedStable (tryContext facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel older newer scope active equation view rest hu annotation) := by
  have none' : ∀ {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)},
      SolvedStable (Option.none : Option (Found problem)) := fun _ _ fired => by cases fired
  unfold tryContext
  try dsimp only
  -- the pattern candidate in the binder context, read as an application, and `G`'s spine
  split <;> try exact none'
  split <;> try exact none'
  split <;> try exact none'
  try dsimp only
  -- `G`'s arguments, distinct and compatible, the same side, a universe
  split <;> try exact none'
  split <;> try exact none'
  refine SolvedStable.dite (fun _ => ?_) (fun _ => none')
  refine SolvedStable.dite (fun _ => ?_) (fun _ => none')
  try dsimp only
  refine SolvedStable.dite (fun _ => ?_) (fun _ => none')
  split <;> try exact none'
  refine SolvedStable.dite (fun _ => ?_) (fun _ => none')
  -- the other side's application and `F`'s spine
  split <;> try exact none'
  split <;> try exact none'
  split <;> try exact none'
  split <;> try exact none'
  refine SolvedStable.dite (fun _ => ?_) (fun _ => none')
  refine SolvedStable.dite (fun _ => ?_) (fun _ => none')
  try dsimp only
  refine SolvedStable.dite (fun _ => ?_) (fun _ => none')
  refine SolvedStable.dite (fun _ => ?_) (fun _ => none')
  try dsimp only
  -- the deleted binders, the pruned type and its spine
  split <;> try exact none'
  split <;> try exact none'
  split <;> try exact none'
  split <;> try exact none'
  -- distinct kept positions, compatible binders, the same result, covering
  refine SolvedStable.dite (fun _ => ?_) (fun _ => none')
  refine SolvedStable.dite (fun _ => ?_) (fun _ => none')
  refine SolvedStable.dite (fun _ => ?_) (fun _ => none')
  try dsimp only
  refine SolvedStable.dite (fun _ => ?_) (fun _ => none')
  try dsimp only
  -- the pattern search after exchanging
  split
  · exact none'
  · rename_i solved solvedSmaller computed
    intro update smaller fired
    cases fired
    exact StableKeeps.then (StableKeeps.then (prune_stable rigid sn _ _ _) (exchange_stable rigid sn _ _ _))
      (searchStore_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal sn fuel _ _ computed)
  · exact fun _ _ fired => by cases fired

include rigid in
theorem tryCodomain_stable (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    {scopeType : TypeOver (extend (extend Γ₀ older) newer)} (scope : Spine scopeType)
    (active : Active scope.target) (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend (extend Γ₀ older) newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) :
    SolvedStable (tryCodomain facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel older newer scope active equation view rest) := by
  intro update smaller fired
  unfold tryCodomain at fired
  split at fired
  · split at fired
    · exact tryContext_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique sn fuel older newer scope active equation view rest _ _ update smaller fired
    · cases fired
  · cases fired

include rigid in
theorem codomainEquation_stable (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) :
    SolvedStable (codomainEquation facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel older newer equation rest) := by
  intro update smaller fired
  unfold codomainEquation at fired
  split at fired
  · cases fired
  rename_i scope active view _
  dsimp only at fired
  split at fired
  · rename_i inner computed
    cases fired
    exact tryCodomain_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique sn fuel older newer scope active equation view rest update smaller computed
  · exact tryCodomain_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique sn fuel older newer scope ⟨active.type, active.right, active.left⟩ equation
      (fun solution => (view solution).trans (toScoped_swap scope active solution).symm) rest update smaller fired

include rigid in
theorem codomainSearch_stable (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older)) :
    ∀ problem : EquationStore (TotalTerm (extend (extend Γ₀ older) newer)),
      SolvedStable (codomainSearch facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique fuel older newer problem)
  | [] => fun _ _ fired => by cases fired
  | equation :: rest => by
      intro update smaller fired
      simp only [codomainSearch] at fired
      split at fired
      · rename_i found computed
        cases fired
        exact codomainEquation_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique sn fuel older newer equation rest update smaller computed
      · exact solvedStable_keepLeft equation (codomainSearch_stable sn fuel older newer rest) update smaller fired

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
/-- **Stability survives the transport to the two newest declarations.** -/
theorem throughTwo_stable {Θ : Context S.R} (outer : Newest Θ) (inner : Newest outer.base)
    (problem : EquationStore (TotalTerm Θ))
    (solve : {Γ₀ : Context S.R} → (older : TypeOver Γ₀) → (newer : TypeOver (extend Γ₀ older)) →
      (stored : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) → Option (Found stored))
    (stable : ∀ {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
      (stored : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))), SolvedStable (solve older newer stored)) :
    SolvedStable (throughTwo outer inner problem solve) := by
  cases outer with
  | mk base newer same =>
      cases inner with
      | mk base₀ older same₀ =>
          change base = extend base₀ older at same₀
          subst same₀
          subst same
          exact stable older newer problem

include rigid in
theorem codomainRule_stable (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    SolvedStable (codomainRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel problem) := by
  unfold codomainRule
  split
  · exact fun _ _ fired => by cases fired
  split
  · exact fun _ _ fired => by cases fired
  exact throughTwo_stable _ _ problem _ fun older newer stored =>
    codomainSearch_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique sn fuel older newer stored

include rigid in
theorem exchangedRule_stable (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    SolvedStable (exchangedRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel problem) := by
  unfold exchangedRule
  split
  · exact fun _ _ fired => by cases fired
  split
  · exact fun _ _ fired => by cases fired
  refine throughTwo_stable _ _ problem _ fun older newer stored => ?_
  intro update smaller fired
  unfold exchangeSolve at fired
  dsimp only at fired
  split at fired
  · cases fired
  split at fired
  · cases fired
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
      exact StableKeeps.then (exchange_stable rigid sn _ _ _)
        (codomainRule_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique sn fuel _ solved solvedSmaller computed)
    · cases fired
  · cases fired

include rigid in
/-- **R110's prune-and-solve rule keeps the permuted class** on a strongly normalizing package. -/
theorem pruneSolveRule_keeps (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat) :
    RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      pruneSolveRule facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique fuel problem := by
  intro Θ problem permuted
  refine foundKeeps_of_stable permuted ?_
  dsimp only
  unfold pruneSolveRule
  split
  · rename_i found computed
    intro update smaller fired
    cases fired
    exact codomainRule_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique sn fuel problem update smaller computed
  · exact exchangedRule_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique sn fuel problem

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
