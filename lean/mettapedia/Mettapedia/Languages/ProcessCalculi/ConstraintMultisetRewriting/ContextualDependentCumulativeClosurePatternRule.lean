import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosurePattern

/-!
# Closure of the cumulative round: the conversion pattern rule, assembled

Every solved outcome of R107's conversion pattern rule drops an equation under an answer that reduces to a pattern
answer (`patternRuleConv_drops`), so the rule keeps the permuted class (`patternRuleConv_keeps`). The general pattern
step solves only through inversion (`step_solved`); a solved scoped result with an empty residual combined into the
store is a drop (`combine_drops`).
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

/-- **A solved scoped result with an empty residual, combined into the store, drops the equation.** -/
theorem combine_drops {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (reading : View equation)
    (rest : EquationStore (TotalTerm Θ)) (moved : ContextualDependentScopedDispatch.Result S.levels [reading.constraint])
    (finished : moved.update.remaining = []) (answer : ReducingAnswer S.R moved.update.answer.substitution) :
    ReducingDrop (equation :: rest) (reading.combine rest moved) := by
  refine ⟨equation, rest, List.Perm.refl _, ?_, fun {Δ} τ => ?_, answer⟩
  · change (frames S.levels).applyStore moved.update.answer rest ++ moved.update.remaining = _
    rw [finished, List.append_nil]
    rfl
  · have holds := moved.sound τ (by rw [finished]; exact Frames.models_nil _)
    have one := (reading.holds_iff (τ ≫ moved.update.answer)).mpr (holds _ (List.mem_singleton_self _))
    exact (solves_reindex moved.update.answer τ _ _).mpr (one _ (List.mem_singleton_self _))

section Step

variable [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (reflects : ContextualDependentReductionReflection.RootReflectsInjections S.R.computation)
  (complete : AlgorithmicComplete S.R S.roles)
  (rigid : ∀ name, S.roles name = .rigid)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

/-- **The general pattern step solves only through inversion**: its answer is `F := λ z̄. u` for a body `u` whose image
along the argument map is the right side, with an empty residual. -/
theorem step_solved (fuel : Nat) {Γ : Context S.R} {type : TypeOver Γ} {spine : Spine type}
    {scopeType : TypeOver (extend Γ type)} {scope : Spine scopeType} (pattern : Pattern spine scope)
    (right : Term scope.target ((lifted spine).result.reindex pattern.map.hom))
    {result : ContextualDependentScopedDispatch.Result S.levels [pattern.constraint right]}
    {finished : result.update.remaining = []}
    (solved : Pattern.step facts roots heads algebra declared reflects complete rigid normalizes certifyNormal choices
      reducer fuel pattern right = .solved result finished) :
    ∃ (body : Term spine.target spine.result) (same : right.code = Presentation.rename pattern.bodyRen body.code),
      result = pattern.replace facts roots heads algebra reflects complete body right same := by
  unfold Pattern.step at solved
  split at solved
  · rename_i found _
    cases solved
    exact ⟨found.body, found.recovers.symm, rfl⟩
  · unfold Pattern.tryRefute at solved
    split at solved
    · cases solved
    · split at solved
      · cases solved
      · split at solved <;> cases solved

end Step

section Rule

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

omit [DecidableRel S.R.cumulative] in
/-- Recognition up to conversion keeps the right side's code. -/
theorem recognizeConv_right (fuel : Nat) {Γ : Context S.R} {type : TypeOver Γ} (spine : Spine type)
    {scopeType : TypeOver (extend Γ type)} (scope : Spine scopeType) (active : Active scope.target)
    {recognized : Recognized spine scope active}
    (read : ContextualDependentRecognitionConversion.recognizeConv facts roots heads algebra reducer fuel spine scope
      active = some recognized) :
    recognized.right.code = active.right.code := by
  unfold ContextualDependentRecognitionConversion.recognizeConv at read
  obtain ⟨shape, _, read⟩ := Option.bind_eq_some_iff.mp read
  obtain ⟨same, _, rfl⟩ := Option.map_eq_some_iff.mp read
  rfl

include rigid in
/-- **R107's conversion pattern step on one reading drops the equation** when the reading's right side has Miller
normal forms. -/
theorem tryActiveConv_drops (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ : Context S.R} (type : TypeOver Γ) {scopeType : TypeOver (extend Γ type)} (scope : Spine scopeType)
    (active : Active scope.target) (equation : Equation (TotalTerm (extend Γ type)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ type),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend Γ type)))
    (sides : ∀ N, Star (R := S.R) active.right.code N → Normal S.R N →
      miller (ContextualDependentShortClosure.spineMark scope) N = true) :
    SolvedDrops (ContextualDependentRecognitionConversion.tryActiveConv facts roots heads algebra declared choices
      reducer rigid complete normalizes certifyNormal fuel type scope active equation view rest) := by
  intro update smaller fired
  unfold ContextualDependentRecognitionConversion.tryActiveConv at fired
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
          rw [← recovers, recognizeConv_right facts roots heads algebra reducer fuel spine scope active read]
          exact sides
        obtain ⟨v, toV, normalV, millerV⟩ := abstractBody_reducing rigid sn recognized.pattern body rightSides
        exact newestReducing _ toV normalV millerV
      · cases fired
  | refuted absent => cases fired
  | pending =>
      dsimp only at fired
      split at fired <;> cases fired

include rigid in
/-- **The conversion pattern rule on one store equation drops it**, in both orientations. -/
theorem tryEquationConv_drops (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ : Context S.R} (type : TypeOver Γ) (equation : Equation (TotalTerm (extend Γ type)))
    (rest : EquationStore (TotalTerm (extend Γ type))) (sides : FragmentSidesMiller equation) :
    SolvedDrops (ContextualDependentRecognitionConversion.tryEquationConv facts roots heads algebra declared choices
      reducer rigid complete root normalizes certifyNormal fuel type equation rest) := by
  intro update smaller fired
  unfold ContextualDependentRecognitionConversion.tryEquationConv at fired
  split at fired
  · cases fired
  rename_i scope active view read
  have readSides := viewEquation_sides facts roots heads algebra declared choices reducer root rigid fuel equation
    sides read
  dsimp only at fired readSides
  split at fired
  · rename_i inner computed
    cases fired
    exact tryActiveConv_drops facts roots heads algebra declared choices reducer rigid complete normalizes certifyNormal
      sn fuel type scope active equation view rest readSides.2 update smaller computed
  · exact tryActiveConv_drops facts roots heads algebra declared choices reducer rigid complete normalizes certifyNormal
      sn fuel type scope ⟨active.type, active.right, active.left⟩ equation
      (fun solution => (view solution).trans (toScoped_swap scope active solution).symm) rest readSides.1 update
      smaller fired

include rigid in
theorem searchStoreConv_drops (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ : Context S.R} (type : TypeOver Γ) :
    ∀ (problem : EquationStore (TotalTerm (extend Γ type))), (∀ equation ∈ problem, FragmentSidesMiller equation) →
      SolvedDrops (ContextualDependentRecognitionConversion.searchStoreConv facts roots heads algebra declared choices
        reducer rigid complete root normalizes certifyNormal fuel type problem)
  | [], _ => fun _ _ fired => by cases fired
  | equation :: rest, sides => by
      intro update smaller fired
      simp only [ContextualDependentRecognitionConversion.searchStoreConv] at fired
      split at fired
      · rename_i found computed
        cases fired
        exact tryEquationConv_drops facts roots heads algebra declared choices reducer rigid complete root normalizes
          certifyNormal sn fuel type equation rest (sides equation List.mem_cons_self) update smaller computed
      · exact solvedDrops_keepLeft equation (searchStoreConv_drops sn fuel type rest
          fun other member => sides other (List.mem_cons_of_mem _ member)) update smaller fired

include rigid in
/-- **Every solved outcome of R107's conversion pattern rule drops an equation under a reducing answer.** -/
theorem patternRuleConv_drops (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) (permuted : PermutedMiller S.levels problem) :
    SolvedDrops (ContextualDependentRecognitionConversion.patternRuleConv facts roots heads algebra declared choices
      reducer rigid complete root normalizes certifyNormal fuel problem) := by
  unfold ContextualDependentRecognitionConversion.patternRuleConv
  split
  · exact fun _ _ fired => by cases fired
  · rename_i view _
    rcases view with ⟨base, newer, same⟩
    subst same
    exact searchStoreConv_drops facts roots heads algebra declared choices reducer rigid complete root normalizes
      certifyNormal sn fuel newer problem fun _ member => permuted.sides_of_mem member

include rigid in
/-- **R107's conversion pattern rule keeps the permuted class** on a strongly normalizing package. -/
theorem patternRuleConv_keeps (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat) :
    RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      ContextualDependentRecognitionConversion.patternRuleConv facts roots heads algebra declared choices reducer rigid
        complete root normalizes certifyNormal fuel problem :=
  fun _ problem permuted => foundKeeps_of_drops rigid sn permuted
    (patternRuleConv_drops facts roots heads algebra declared choices reducer rigid complete root normalizes
      certifyNormal sn fuel problem permuted)

end Rule

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
