import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosureScoped

/-!
# Closure of the cumulative round: R99's decomposition of local applications

R99's rule (`ContextualDependentRigidDecomposition.decomposeSearch`) reads `x a ≐ x b` for a rigid local `x` of the
reading (`decomposeActive`), replaces the equation by the closed argument equation `λ z̄. a ≐ λ z̄. b`, and runs R75's
pattern rule. The argument codes are the arguments of the reading's rigid applications (`decomposeActive_codes`); a
normal form of `x a` is `x` applied to a normal form of `a`, so the arguments have Miller normal reducts
(`argument_reduct`); the replacement is stable (`replaced_stable`), the pattern rule is (`patternRule_stable`), and the
rule keeps the permuted class (`decomposeSearch_keeps`).
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
open ContextualDependentExecutableJoin ContextualDependentPiSpine ContextualDependentScope
open ContextualDependentRigidDecomposition

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **The argument of a rigid local application has a Miller normal reduct** when the application's normal forms are
Miller with the locals rigid. -/
theorem argument_reduct (rigid : ∀ name, S.roles name = .rigid)
    (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) {Γ : Context S.R} {scopeType : TypeOver Γ}
    (scope : Spine scopeType) (position : scope.Local) {type : TypeOver scope.target} (argument : Term scope.target type)
    (sides : ∀ N, Star (R := S.R) (.app (.var (scope.localIndex position)) argument.code) N → Normal S.R N →
      miller (ContextualDependentShortClosure.spineMark scope) N = true) :
    MarkedReduct S.R (ContextualDependentShortClosure.spineMark scope) argument.code := by
  have empty := computation_empty rigid
  obtain ⟨A, toA, normalA⟩ := ContextualDependentOpenedNormal.term_normal sn argument
  have normalApp : Normal S.R (.app (.var (scope.localIndex position)) A) :=
    (normal_app_iff empty).mpr ⟨rfl, normal_var empty _, normalA⟩
  have millerApp := sides _ (star_app .refl toA) normalApp
  have rigidHead : flexHead (ContextualDependentShortClosure.spineMark scope)
      (spineHead (.var (scope.localIndex position) : Tm Head scope.target.arity)) = false :=
    ContextualDependentShortClosure.spineMark_local scope position
  exact ⟨A, toA, normalA, (decompose_app rigidHead millerApp).2⟩

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

/-- **The argument reading's codes are the arguments of the reading's rigid applications.** -/
theorem decomposeActive_codes (fuel : Nat) {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (active : Active scope.target)
    {found : {argument : Active scope.target // ∀ {Δ : Context S.R} (solution : Δ ⟶ Γ),
      (scope.toScoped active).Holds solution ↔ (scope.toScoped argument).Holds solution}}
    (read : decomposeActive facts complete roots heads algebra declared choices reducer fuel scope active =
      some found) :
    ∃ position : scope.Local,
      active.left.code = .app (.var (scope.localIndex position)) found.val.left.code ∧
        active.right.code = .app (.var (scope.localIndex position)) found.val.right.code := by
  unfold decomposeActive at read
  split at read
  · rename_i head left head' right leftFound rightFound
    split at read
    · rename_i same
      subst same
      split at read
      · split at read
        · split at read
          · cases read
          · cases read
            exact ⟨head, asLocalApplication_spec scope leftFound, asLocalApplication_spec scope rightFound⟩
        · cases read
      · cases read
    · cases read
  · cases read

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
/-- A store equation has the solutions of its singleton store. -/
theorem models_singleton {Θ Δ : Context S.R} (σ : Δ ⟶ Θ) (equation : Equation (TotalTerm Θ)) :
    (frames S.levels).Models σ [equation] ↔ (frames S.levels).Solves σ equation :=
  ⟨fun solved => solved _ (List.mem_singleton_self _), fun solved other member => by
    rw [List.mem_singleton.mp member]
    exact solved⟩

variable (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

include rigid in
/-- **R99's decomposition of one local application is stable.** -/
theorem decomposeEquation_stable (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (rest : EquationStore (TotalTerm Θ))
    (sides : FragmentSidesMiller equation) :
    SolvedStable (decomposeEquation rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal fuel equation rest) := by
  have empty := computation_empty rigid
  intro update smaller fired
  unfold decomposeEquation at fired
  split at fired
  · cases fired
  rename_i scope active view read
  have readSides := viewEquation_sides facts roots heads algebra declared choices reducer root rigid fuel equation
    sides read
  dsimp only at readSides
  split at fired
  · cases fired
  rename_i argument sameSolutions readArgument
  split at fired
  · cases fired
  rename_i closed computed
  dsimp only at fired
  split at fired
  · cases fired
  split at fired
  · rename_i solved solvedSmaller computedPattern
    cases fired
    obtain ⟨position, leftCode, rightCode⟩ := decomposeActive_codes facts roots heads algebra complete declared
      choices reducer fuel scope active readArgument
    have leftReduct := argument_reduct rigid sn scope position argument.left (by rw [← leftCode]; exact readSides.1)
    have rightReduct := argument_reduct rigid sn scope position argument.right (by rw [← rightCode]; exact readSides.2)
    refine StableKeeps.then (replaced_stable [closed.equation] (fun σ => ?_) ?_ ?_ _) ?_
    · exact ((Active.holds_iff_models S.levels closed σ).symm.trans
        ((Scoped.closeWith_holds_iff S.levels choices _ computed σ).trans
          ((sameSolutions σ).symm.trans (view σ).symm))).trans (models_singleton σ equation)
    · intro piece member
      rw [List.mem_singleton.mp member]
      exact closed_sides empty choices scope argument computed leftReduct rightReduct
    · intro piece member
      rw [List.mem_singleton.mp member]
      rfl
    · exact patternRule_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal sn fuel _ solved solvedSmaller computedPattern
  · cases fired
  · cases fired

include rigid in
theorem decomposeSearch_stable (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), (∀ equation ∈ problem, FragmentSidesMiller equation) →
      SolvedStable (decomposeSearch rigid facts complete roots heads algebra declared choices reducer root normalizes
        certifyNormal fuel problem)
  | [], _ => fun _ _ fired => by cases fired
  | equation :: rest, sides => by
      intro update smaller fired
      simp only [decomposeSearch] at fired
      split at fired
      · rename_i found computed
        cases fired
        exact decomposeEquation_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal sn fuel equation rest (sides equation List.mem_cons_self) update smaller computed
      · exact solvedStable_keepLeft equation (decomposeSearch_stable sn fuel rest
          fun other member => sides other (List.mem_cons_of_mem _ member)) update smaller fired

include rigid in
/-- **R99's decomposition of local applications keeps the permuted class** on a strongly normalizing package. -/
theorem decomposeSearch_keeps (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat) :
    RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      decomposeSearch rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
        fuel problem :=
  fun _ problem permuted => foundKeeps_of_stable permuted
    (decomposeSearch_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal sn fuel problem fun _ member => permuted.sides_of_mem member)

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
