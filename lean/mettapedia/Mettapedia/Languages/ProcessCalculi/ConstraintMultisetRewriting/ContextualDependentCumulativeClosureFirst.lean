import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosurePruneSolve

/-!
# Closure of the cumulative round: R76's first rule

R76's first rule (`ContextualDependentDecisiveFragment.firstRule`) is the pattern rule, then the prune rule (prune the
newest metavariable to the arguments of a flex–flex equation, exchange, and run the pattern search), then the exchange
rule (exchange the two newest declarations and run the pattern search). Every solved outcome of each is stable
(`patternRule_stable`, `pruneRule_stable`, `exchangeRule_stable`), so the first rule's are (`firstRule_stable`) and the
first rule keeps the permuted class (`firstRule_keeps`). It is the depth-`0` rule of R86's in-place rule and of the
reorder rule, and the first step of R75's full round.
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
open ContextualDependentPiSpine ContextualDependentScope ContextualDependentGeneralPattern

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

include rigid in
/-- **R75's pattern rule is stable.** -/
theorem patternRule_stable (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    SolvedStable (patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal fuel problem) := by
  intro update smaller fired before permuted
  exact stableKeeps_of_reducingDrop rigid sn
    (patternRule_drops facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
      sn fuel problem (fun _ member => permuted.sides_of_mem (List.mem_append_right _ member)) update smaller fired)
    before permuted

include rigid in
theorem tryPrune_stable (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    {scopeType : TypeOver (extend (extend Γ₀ older) newer)} (scope : Spine scopeType)
    (active : Active scope.target) (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend (extend Γ₀ older) newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer)))
    (spine : Spine newer) (recognized : Recognized spine scope active) :
    SolvedStable (tryPrune rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel older newer scope active equation view rest spine recognized) := by
  have none' : ∀ {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)},
      SolvedStable (Option.none : Option (Found problem)) := fun _ _ fired => by cases fired
  unfold tryPrune
  try dsimp only
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
  split <;> try exact none'
  split <;> try exact none'
  split <;> try exact none'
  split <;> try exact none'
  refine SolvedStable.dite (fun _ => ?_) (fun _ => none')
  refine SolvedStable.dite (fun _ => ?_) (fun _ => none')
  refine SolvedStable.dite (fun _ => ?_) (fun _ => none')
  try dsimp only
  refine SolvedStable.dite (fun _ => ?_) (fun _ => none')
  try dsimp only
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
theorem pruneActive_stable (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    {scopeType : TypeOver (extend (extend Γ₀ older) newer)} (scope : Spine scopeType)
    (active : Active scope.target) (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend (extend Γ₀ older) newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) :
    SolvedStable (pruneActive rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel older newer scope active equation view rest) := by
  have none' : ∀ {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)},
      SolvedStable (Option.none : Option (Found problem)) := fun _ _ fired => by cases fired
  unfold pruneActive
  split <;> try exact none'
  split <;> try exact none'
  split <;> try exact none'
  exact tryPrune_stable facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
    headTypingUnique sn fuel older newer scope active equation view rest _ _

include rigid in
theorem pruneEquation_stable (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) :
    SolvedStable (pruneEquation rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel older newer equation rest) := by
  intro update smaller fired
  unfold pruneEquation at fired
  split at fired
  · cases fired
  rename_i scope active view _
  dsimp only at fired
  split at fired
  · rename_i inner computed
    cases fired
    exact pruneActive_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique sn fuel older newer scope active equation view rest update smaller computed
  · exact pruneActive_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique sn fuel older newer scope ⟨active.type, active.right, active.left⟩ equation
      (fun solution => (view solution).trans (toScoped_swap scope active solution).symm) rest update smaller fired

include rigid in
theorem pruneSearch_stable (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older)) :
    ∀ problem : EquationStore (TotalTerm (extend (extend Γ₀ older) newer)),
      SolvedStable (pruneSearch rigid facts complete roots heads algebra declared choices reducer root normalizes
        certifyNormal headTypingUnique fuel older newer problem)
  | [] => fun _ _ fired => by cases fired
  | equation :: rest => by
      intro update smaller fired
      simp only [pruneSearch] at fired
      split at fired
      · rename_i found computed
        cases fired
        exact pruneEquation_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique sn fuel older newer equation rest update smaller computed
      · exact solvedStable_keepLeft equation (pruneSearch_stable sn fuel older newer rest) update smaller fired

include rigid in
/-- **R76's prune rule is stable.** -/
theorem pruneRule_stable (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    SolvedStable (pruneRule rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel problem) := by
  unfold pruneRule
  split
  · exact fun _ _ fired => by cases fired
  split
  · exact fun _ _ fired => by cases fired
  exact throughTwo_stable _ _ problem _ fun older newer stored =>
    pruneSearch_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique sn fuel older newer stored

include rigid in
theorem exchangeAt_stable (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    (problem : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) :
    SolvedStable (exchangeAt rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal fuel older newer problem) := by
  cases problem with
  | nil => exact fun _ _ fired => by cases fired
  | cons equation rest =>
      intro update smaller fired
      unfold exchangeAt at fired
      cases inverted : ContextualDependentInversion.invert (withoutNewest Γ₀.arity) newer.code with
      | none =>
          rw [inverted] at fired
          cases fired
      | some code =>
          rw [inverted] at fired
          dsimp only at fired
          split at fired
          · cases fired
          · split at fired
            · rename_i same
              obtain ⟨sameCode, sameLevel⟩ := same
              have independent := TypeOver.ext sameCode sameLevel
              subst independent
              dsimp only at fired
              split at fired
              · cases fired
              · rename_i solved solvedSmaller computed
                cases fired
                exact StableKeeps.then (exchange_stable rigid sn _ _ _)
                  (searchStore_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
                    certifyNormal sn fuel _ _ computed)
              · cases fired
            · cases fired

include rigid in
/-- **R76's exchange rule is stable.** -/
theorem exchangeRule_stable (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    SolvedStable (exchangeRule rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal fuel problem) := by
  unfold exchangeRule
  split
  · exact fun _ _ fired => by cases fired
  split
  · exact fun _ _ fired => by cases fired
  exact throughTwo_stable _ _ problem _ fun older newer stored =>
    exchangeAt_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal sn fuel older newer stored

include rigid in
/-- **R76's first rule is stable.** -/
theorem firstRule_stable (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    SolvedStable (ContextualDependentDecisiveFragment.firstRule rigid facts complete roots heads algebra declared
      choices reducer root normalizes certifyNormal headTypingUnique fuel problem) := by
  unfold ContextualDependentDecisiveFragment.firstRule
  split
  · rename_i found computed
    intro update smaller fired
    cases fired
    exact patternRule_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal sn fuel problem update smaller computed
  · split
    · rename_i found computed
      intro update smaller fired
      cases fired
      exact pruneRule_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique sn fuel problem update smaller computed
    · exact exchangeRule_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal sn fuel problem

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
