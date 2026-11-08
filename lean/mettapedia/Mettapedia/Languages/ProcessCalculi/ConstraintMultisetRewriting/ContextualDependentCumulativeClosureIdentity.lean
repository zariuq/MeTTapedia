import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosureLocal

/-!
# Closure of the cumulative round: R98's decomposition of identity types

R98's identity rule (`ContextualDependentFragment.idDecomposeSearch`) reads `Id A a b ≐ Id A a' b'` at a universe
(`idDecomposeActive`), replaces the equation by the closed endpoint equations `a ≐ a'` and `b ≐ b'` at the carrier,
and runs R75's pattern rule. The endpoint codes are the endpoints of the reading's identity types
(`idDecomposeActive_codes`); a normal form of `Id A a b` is an identity type of normal forms, so the endpoints have
Miller normal reducts (`endpoint_reducts`), and the rule keeps the permuted class (`idDecomposeSearch_keeps`).
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

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **The endpoints of an identity type with Miller normal forms have Miller normal reducts.** -/
theorem endpoint_reducts (rigid : ∀ name, S.roles name = .rigid)
    (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) {Θ : Context S.R} {type : TypeOver Θ}
    (term : Term Θ type) {mark : Fin Θ.arity → Bool} {A a b : Tm Head Θ.arity} (code : term.code = .id A a b)
    (sides : ∀ N, Star (R := S.R) term.code N → Normal S.R N → miller mark N = true) :
    MarkedReduct S.R mark a ∧ MarkedReduct S.R mark b := by
  have empty := computation_empty rigid
  obtain ⟨N, toN, normalN⟩ := ContextualDependentOpenedNormal.term_normal sn term
  have millerN := sides N toN normalN
  rw [code] at toN
  obtain ⟨A', a', b', rfl, _, toA, toB⟩ := star_id_inv empty toN
  obtain ⟨_, normalA, normalB⟩ := (normal_id_iff empty).mp normalN
  simp only [miller, Bool.and_eq_true] at millerN
  exact ⟨⟨a', toA, normalA, millerN.1.2⟩, ⟨b', toB, normalB, millerN.2⟩⟩

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

/-- **The endpoint readings' codes are the endpoints of the reading's identity types.** -/
theorem idDecomposeActive_codes (fuel : Nat) {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (active : Active scope.target)
    {found : {pair : Active scope.target × Active scope.target // ∀ {Δ : Context S.R} (solution : Δ ⟶ Γ),
      (scope.toScoped active).Holds solution ↔
        (scope.toScoped pair.1).Holds solution ∧ (scope.toScoped pair.2).Holds solution}}
    (read : idDecomposeActive facts roots heads algebra declared choices reducer fuel scope active = some found) :
    (∃ A, active.left.code = .id A found.val.1.left.code found.val.2.left.code) ∧
      ∃ A', active.right.code = .id A' found.val.1.right.code found.val.2.right.code := by
  unfold idDecomposeActive at read
  split at read
  · rename_i A a b A' a' b' u leftCode rightCode _
    split at read
    · split at read
      · split at read
        · cases read
        · cases read
          exact ⟨⟨A, leftCode⟩, ⟨A', rightCode⟩⟩
      · cases read
    · cases read
  · cases read

variable (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

include rigid in
/-- **R98's identity decomposition of one equation is stable.** -/
theorem idDecomposeEquation_stable (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (rest : EquationStore (TotalTerm Θ))
    (sides : FragmentSidesMiller equation) :
    SolvedStable (idDecomposeEquation facts roots heads algebra declared choices reducer rigid complete root normalizes
      certifyNormal fuel equation rest) := by
  have empty := computation_empty rigid
  intro update smaller fired
  unfold idDecomposeEquation at fired
  split at fired
  · cases fired
  rename_i scope active view read
  have readSides := viewEquation_sides facts roots heads algebra declared choices reducer root rigid fuel equation
    sides read
  dsimp only at readSides
  split at fired
  · cases fired
  rename_i first second split readPair
  split at fired
  · rename_i firstClosed secondClosed firstComputed secondComputed
    dsimp only at fired
    split at fired
    · cases fired
    split at fired
    · rename_i solved solvedSmaller computedPattern
      cases fired
      obtain ⟨⟨A, leftCode⟩, ⟨A', rightCode⟩⟩ := idDecomposeActive_codes facts roots heads algebra declared choices
        reducer fuel scope active readPair
      obtain ⟨firstLeft, secondLeft⟩ := endpoint_reducts rigid sn active.left leftCode readSides.1
      obtain ⟨firstRight, secondRight⟩ := endpoint_reducts rigid sn active.right rightCode readSides.2
      refine StableKeeps.then
        (replaced_stable [firstClosed.equation, secondClosed.equation] (fun σ => ?_) ?_ ?_ _) ?_
      · have pair := Frames.models_append (X := frames S.levels) σ [firstClosed.equation] [secondClosed.equation]
        refine pair.trans ?_
        rw [← Active.holds_iff_models S.levels firstClosed σ, ← Active.holds_iff_models S.levels secondClosed σ,
          Scoped.closeWith_holds_iff S.levels choices _ firstComputed σ,
          Scoped.closeWith_holds_iff S.levels choices _ secondComputed σ, ← split σ, ← view σ]
        exact models_singleton σ equation
      · intro piece member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact closed_sides empty choices scope first firstComputed firstLeft firstRight
        · exact closed_sides empty choices scope second secondComputed secondLeft secondRight
      · intro piece member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> rfl
      · exact patternRule_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal sn fuel _ solved solvedSmaller computedPattern
    · cases fired
    · cases fired
  · cases fired

include rigid in
theorem idDecomposeSearch_stable (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), (∀ equation ∈ problem, FragmentSidesMiller equation) →
      SolvedStable (idDecomposeSearch facts roots heads algebra declared choices reducer rigid complete root normalizes
        certifyNormal fuel problem)
  | [], _ => fun _ _ fired => by cases fired
  | equation :: rest, sides => by
      intro update smaller fired
      simp only [idDecomposeSearch] at fired
      split at fired
      · rename_i found computed
        cases fired
        exact idDecomposeEquation_stable facts roots heads algebra rigid complete declared choices reducer root
          normalizes certifyNormal sn fuel equation rest (sides equation List.mem_cons_self) update smaller computed
      · exact solvedStable_keepLeft equation (idDecomposeSearch_stable sn fuel rest
          fun other member => sides other (List.mem_cons_of_mem _ member)) update smaller fired

include rigid in
/-- **R98's identity decomposition keeps the permuted class** on a strongly normalizing package. -/
theorem idDecomposeSearch_keeps (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat) :
    RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      idDecomposeSearch facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        fuel problem :=
  fun _ problem permuted => foundKeeps_of_stable permuted
    (idDecomposeSearch_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal sn fuel problem fun _ member => permuted.sides_of_mem member)

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
