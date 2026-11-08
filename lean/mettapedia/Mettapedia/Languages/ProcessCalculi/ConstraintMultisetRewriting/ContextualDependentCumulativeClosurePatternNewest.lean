import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosurePatternRule

/-!
# Closure of the cumulative round: R75's pattern rule

R75's pattern rule (`ContextualDependentPatternSolver.patternRule`) is R107's conversion pattern rule with exact
recognition of the annotation instead of recognition up to conversion. Its solved outcomes drop an equation under an
answer that reduces to a pattern answer, by the same argument (`patternRule_drops`), so it keeps the permuted class
(`patternRule_keeps`).
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
open ContextualDependentDynamicFragment ContextualDependentHereditary ExecutableReduction
open ContextualDependentExecutableJoin ContextualDependentPiSpine ContextualDependentGeneralPattern
open ContextualDependentScope

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))

omit [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
/-- Exact recognition keeps the right side's code. -/
theorem recognize_right {Γ : Context S.R} {type : TypeOver Γ} (spine : Spine type)
    {scopeType : TypeOver (extend Γ type)} (scope : Spine scopeType) (active : Active scope.target)
    {recognized : Recognized spine scope active} (read : recognize spine scope active = some recognized) :
    recognized.right.code = active.right.code := by
  unfold recognize at read
  repeat' (first | (split at read) | (cases read) | (dsimp only at read))
  all_goals rfl

include rigid in
/-- **R75's pattern step on one reading drops the equation** when the reading's right side has Miller normal forms. -/
theorem tryActive_drops (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ : Context S.R} (type : TypeOver Γ) {scopeType : TypeOver (extend Γ type)} (scope : Spine scopeType)
    (active : Active scope.target) (equation : Equation (TotalTerm (extend Γ type)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ type),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend Γ type)))
    (sides : ∀ N, Star (R := S.R) active.right.code N → Normal S.R N →
      miller (ContextualDependentShortClosure.spineMark scope) N = true) :
    SolvedDrops (tryActive rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal
      fuel type scope active equation view rest) := by
  intro update smaller fired
  unfold tryActive at fired
  split at fired
  · cases fired
  split at fired
  · cases fired
  rename_i spine _
  split at fired
  · cases fired
  rename_i recognized read
  generalize computed : Pattern.step facts roots heads algebra declared
    (ContextualDependentScopeConsequence.root_reflection rigid) complete rigid normalizes certifyNormal choices
    reducer fuel recognized.pattern recognized.right = outcome at fired
  cases outcome with
  | solved result finished =>
      dsimp only at fired
      split at fired
      · cases fired
        obtain ⟨body, recovers, rfl⟩ := step_solved facts roots heads algebra declared
          (ContextualDependentScopeConsequence.root_reflection rigid) complete rigid normalizes certifyNormal choices
          reducer fuel recognized.pattern recognized.right computed
        refine combine_drops _ rest _ rfl ?_
        change ReducingAnswer S.R (Elimination.instantiate Γ (spine.abstractBody body)).substitution
        have rightSides : ∀ N, Star (R := S.R) (Presentation.rename recognized.pattern.bodyRen body.code) N →
            Normal S.R N → miller (ContextualDependentShortClosure.spineMark scope) N = true := by
          rw [← recovers, recognize_right spine scope active read]
          exact sides
        obtain ⟨v, toV, normalV, millerV⟩ := abstractBody_reducing rigid sn recognized.pattern body rightSides
        exact newestReducing _ toV normalV millerV
      · cases fired
  | refuted absent => cases fired
  | pending =>
      dsimp only at fired
      split at fired <;> cases fired

include rigid in
/-- **R75's pattern rule on one store equation drops it**, in both orientations. -/
theorem tryEquation_drops (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ : Context S.R} (type : TypeOver Γ) (equation : Equation (TotalTerm (extend Γ type)))
    (rest : EquationStore (TotalTerm (extend Γ type))) (sides : FragmentSidesMiller equation) :
    SolvedDrops (tryEquation rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal fuel type equation rest) := by
  intro update smaller fired
  unfold tryEquation at fired
  split at fired
  · cases fired
  rename_i scope active view read
  have readSides := viewEquation_sides facts roots heads algebra declared choices reducer root rigid fuel equation
    sides read
  dsimp only at fired readSides
  split at fired
  · rename_i inner computed
    cases fired
    exact tryActive_drops facts roots heads algebra declared choices reducer rigid complete normalizes certifyNormal
      sn fuel type scope active equation view rest readSides.2 update smaller computed
  · exact tryActive_drops facts roots heads algebra declared choices reducer rigid complete normalizes certifyNormal
      sn fuel type scope ⟨active.type, active.right, active.left⟩ equation
      (fun solution => (view solution).trans (toScoped_swap scope active solution).symm) rest readSides.1 update
      smaller fired

include rigid in
theorem searchStore_drops (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ : Context S.R} (type : TypeOver Γ) :
    ∀ (problem : EquationStore (TotalTerm (extend Γ type))), (∀ equation ∈ problem, FragmentSidesMiller equation) →
      SolvedDrops (searchStore rigid facts complete roots heads algebra declared choices reducer root normalizes
        certifyNormal fuel type problem)
  | [], _ => fun _ _ fired => by cases fired
  | equation :: rest, sides => by
      intro update smaller fired
      simp only [searchStore] at fired
      split at fired
      · rename_i found computed
        cases fired
        exact tryEquation_drops facts roots heads algebra declared choices reducer rigid complete root normalizes
          certifyNormal sn fuel type equation rest (sides equation List.mem_cons_self) update smaller computed
      · exact solvedDrops_keepLeft equation (searchStore_drops sn fuel type rest
          fun other member => sides other (List.mem_cons_of_mem _ member)) update smaller fired

include rigid in
/-- **Every solved outcome of R75's pattern rule drops an equation under a reducing answer.** -/
theorem patternRule_drops (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) (sides : ∀ equation ∈ problem, FragmentSidesMiller equation) :
    SolvedDrops (patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal fuel problem) := by
  unfold patternRule
  split
  · exact fun _ _ fired => by cases fired
  · rename_i view _
    rcases view with ⟨base, newer, same⟩
    subst same
    exact searchStore_drops facts roots heads algebra declared choices reducer rigid complete root normalizes
      certifyNormal sn fuel newer problem sides

include rigid in
/-- **R75's pattern rule keeps the permuted class** on a strongly normalizing package. -/
theorem patternRule_keeps (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat) :
    RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal fuel
        problem :=
  fun _ problem permuted => foundKeeps_of_drops rigid sn permuted
    (patternRule_drops facts roots heads algebra declared choices reducer rigid complete root normalizes
      certifyNormal sn fuel problem fun _ member => permuted.sides_of_mem member)

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
