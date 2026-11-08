import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosureAfter

/-!
# Closure of the cumulative round: the spine rule and deep decomposition

The spine rule (`twoSearch`) reads `λ z̄. x a₁ a₂ ≐ λ z̄. x b₁ b₂` for a local `x` (`decomposeTwoActive`), closes the
two argument equations and continues on them (`twoContinue`). The arguments of a normal Miller spine of a rigid local
have normal Miller reducts (`MarkedReduct.of_spine`), so the closed pieces have Miller sides, and the replacement keeps
the class (`twoEquation_stable`).

Deep decomposition (`deepSearch`) decomposes an equation between rigid formers and keeps decomposing the store
(`decomposeDeep`); every step replaces one equation by R94's pieces, which keeps the class at its position
(`decomposeOnce_position`, `decomposeDeep_position`).

Both continue through `afterParts`, so both keep the class wherever R86's in-place rule is stable
(`twoSearch_keeps_of_inPlace`, `deepSearch_keeps_of_inPlace`).
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
open ContextualDependentExecutableJoin ContextualDependentClosure ContextualDependentPiSpine ContextualDependentScope
open ContextualDependentRigidFormers (parts_equivalent twice)

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

/-! ## The spine rule -/

/-- **The two argument readings' codes are the arguments of the reading's double applications.** -/
theorem decomposeTwoActive_codes (fuel : Nat) {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (active : Active scope.target)
    {found : {pair : Active scope.target × Active scope.target // ∀ {Δ : Context S.R} (solution : Δ ⟶ Γ),
      (scope.toScoped active).Holds solution ↔
        (scope.toScoped pair.1).Holds solution ∧ (scope.toScoped pair.2).Holds solution}}
    (read : ContextualDependentRigidFormers.decomposeTwoActive facts roots heads algebra complete declared choices
      reducer fuel scope active = some found) :
    ∃ position : scope.Local,
      active.left.code = twice (scope.localIndex position) found.val.1.left.code found.val.2.left.code ∧
        active.right.code = twice (scope.localIndex position) found.val.1.right.code found.val.2.right.code := by
  unfold ContextualDependentRigidFormers.decomposeTwoActive at read
  split at read
  · cases read
  · rename_i shape _
    obtain ⟨first, _, read⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨second, _, rfl⟩ := Option.map_eq_some_iff.mp read
    exact ⟨shape.head, shape.leftCode, shape.rightCode⟩

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
/-- The arguments of a double application of a rigid local with a Miller normal reduct have Miller normal reducts. -/
theorem twice_reducts (empty : S.R.computation = RootComputation.empty) {Γ : Context S.R} {scopeType : TypeOver Γ}
    (scope : Spine scopeType) (position : scope.Local) {a b : Tm Head scope.target.arity}
    (whole : MarkedReduct S.R (ContextualDependentShortClosure.spineMark scope) (twice (scope.localIndex position) a b)) :
    MarkedReduct S.R (ContextualDependentShortClosure.spineMark scope) a ∧
      MarkedReduct S.R (ContextualDependentShortClosure.spineMark scope) b := by
  have spine : MarkedReduct S.R (ContextualDependentShortClosure.spineMark scope)
      (appSpine (.var (scope.localIndex position)) [a, b]) := whole
  have rigidHead := ContextualDependentShortClosure.spineMark_local scope position
  exact ⟨MarkedReduct.of_spine empty _ rigidHead [a, b] spine a (by simp),
    MarkedReduct.of_spine empty _ rigidHead [a, b] spine b (by simp)⟩

variable (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R)

include sn in
/-- **The spine rule on one equation is stable** when R86's in-place rule is. -/
theorem twoEquation_stable (fuel : Nat)
    (inPlace : InPlaceStable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel)
    {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (rest : EquationStore (TotalTerm Θ))
    (sides : FragmentSidesMiller equation) :
    SolvedStable (ContextualDependentRigidFormers.twoEquation facts roots heads algebra declared choices reducer rigid
      complete root normalizes certifyNormal headTypingUnique fuel equation rest) := by
  have empty := computation_empty rigid
  intro update smaller fired
  unfold ContextualDependentRigidFormers.twoEquation at fired
  obtain ⟨reading, read, fired⟩ := Option.bind_eq_some_iff.mp fired
  obtain ⟨found, readPair, fired⟩ := Option.bind_eq_some_iff.mp fired
  have readSides := viewEquation_sides facts roots heads algebra declared choices reducer root rigid fuel equation
    sides read
  obtain ⟨position, leftCode, rightCode⟩ := decomposeTwoActive_codes facts roots heads algebra complete declared
    choices reducer fuel reading.1 reading.2.1 readPair
  have leftWhole : MarkedReduct S.R (ContextualDependentShortClosure.spineMark reading.1) reading.2.1.left.code := by
    obtain ⟨N, toN, normalN⟩ := ContextualDependentOpenedNormal.term_normal sn reading.2.1.left
    exact ⟨N, toN, normalN, readSides.1 N toN normalN⟩
  have rightWhole : MarkedReduct S.R (ContextualDependentShortClosure.spineMark reading.1) reading.2.1.right.code := by
    obtain ⟨N, toN, normalN⟩ := ContextualDependentOpenedNormal.term_normal sn reading.2.1.right
    exact ⟨N, toN, normalN, readSides.2 N toN normalN⟩
  rw [leftCode] at leftWhole
  rw [rightCode] at rightWhole
  obtain ⟨firstLeft, secondLeft⟩ := twice_reducts empty reading.1 position leftWhole
  obtain ⟨firstRight, secondRight⟩ := twice_reducts empty reading.1 position rightWhole
  unfold ContextualDependentRigidFormers.twoContinue at fired
  split at fired
  · rename_i firstClosed secondClosed firstComputed secondComputed
    dsimp only at fired
    split at fired
    · cases fired
    · refine afterParts_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique sn fuel inPlace _
        (replaced_stable [firstClosed.equation, secondClosed.equation] (fun σ => ?_) ?_ ?_ _) update smaller fired
      · have pair := Frames.models_append (X := frames S.levels) σ [firstClosed.equation] [secondClosed.equation]
        refine pair.trans ?_
        rw [← Active.holds_iff_models S.levels firstClosed σ, ← Active.holds_iff_models S.levels secondClosed σ,
          Scoped.closeWith_holds_iff S.levels choices _ firstComputed σ,
          Scoped.closeWith_holds_iff S.levels choices _ secondComputed σ, ← found.property σ, ← reading.2.2 σ]
        exact models_singleton σ equation
      · intro piece member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact closed_sides empty choices reading.1 found.val.1 firstComputed firstLeft firstRight
        · exact closed_sides empty choices reading.1 found.val.2 secondComputed secondLeft secondRight
      · intro piece member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> rfl
  · cases fired

include sn in
theorem twoSearch_stable (fuel : Nat)
    (inPlace : InPlaceStable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel)
    {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), (∀ equation ∈ problem, FragmentSidesMiller equation) →
      SolvedStable (ContextualDependentRigidFormers.twoSearch facts roots heads algebra declared choices reducer rigid
        complete root normalizes certifyNormal headTypingUnique fuel problem)
  | [], _ => fun _ _ fired => by cases fired
  | equation :: rest, sides => by
      intro update smaller fired
      simp only [ContextualDependentRigidFormers.twoSearch] at fired
      split at fired
      · rename_i found computed
        cases fired
        exact twoEquation_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique sn fuel inPlace equation rest (sides equation List.mem_cons_self) update
          smaller computed
      · exact solvedStable_keepLeft equation (twoSearch_stable fuel inPlace rest
          fun other member => sides other (List.mem_cons_of_mem _ member)) update smaller fired

include sn in
/-- **The spine rule keeps the class** wherever R86's in-place rule is stable. -/
theorem twoSearch_keeps_of_inPlace (fuel : Nat)
    (inPlace : InPlaceStable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel) :
    RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      ContextualDependentRigidFormers.twoSearch facts roots heads algebra declared choices reducer rigid complete root
        normalizes certifyNormal headTypingUnique fuel problem :=
  fun _ problem permuted => foundKeeps_of_stable permuted
    (twoSearch_stable facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique sn fuel inPlace problem fun _ member => permuted.sides_of_mem member)

/-! ## Deep decomposition -/

include rigid sn in
/-- **One decomposition step keeps the class at its position.** -/
theorem decomposeOnce_position (fuel : Nat) {Θ : Context S.R} :
    ∀ (problem : EquationStore (TotalTerm Θ)) {next : ContextualDependentRigidFormers.Rewritten problem}
      (before : EquationStore (TotalTerm Θ)),
      ContextualDependentRigidFormers.decomposeOnce facts roots heads algebra declared choices reducer complete fuel
        problem = some next →
      PermutedMiller S.levels (before ++ problem) → PermutedMiller S.levels (before ++ next.val)
  | [], _, _, found, _ => by cases found
  | equation :: rest, next, before, found, permuted => by
      simp only [ContextualDependentRigidFormers.decomposeOnce] at found
      split at found
      · rename_i parts computed
        cases found
        exact PermutedMiller.splice_underReducts rigid sn facts algebra permuted
          (formerParts_codes facts roots heads algebra complete declared choices reducer fuel computed) parts.val rfl
          fun σ => (parts.property σ).symm
      · obtain ⟨inner, innerFound, rfl⟩ := Option.map_eq_some_iff.mp found
        have moved := decomposeOnce_position fuel rest (before ++ [equation]) innerFound (by simpa using permuted)
        change PermutedMiller S.levels (before ++ equation :: inner.val)
        simpa using moved

include rigid sn in
/-- **Deep decomposition keeps the class at its position.** -/
theorem decomposeDeep_position (fuel : Nat) {Θ : Context S.R} :
    ∀ (steps : Nat) (problem before : EquationStore (TotalTerm Θ)), PermutedMiller S.levels (before ++ problem) →
      PermutedMiller S.levels (before ++ (ContextualDependentRigidFormers.decomposeDeep facts roots heads algebra
        declared choices reducer complete fuel steps problem).val)
  | 0, _, _, permuted => permuted
  | steps + 1, problem, before, permuted => by
      simp only [ContextualDependentRigidFormers.decomposeDeep]
      cases once : ContextualDependentRigidFormers.decomposeOnce facts roots heads algebra declared choices reducer
          complete fuel problem with
      | none => exact permuted
      | some next =>
          exact decomposeDeep_position fuel steps next.val before
            (decomposeOnce_position facts roots heads algebra rigid complete declared choices reducer sn fuel problem
              before once permuted)

include sn in
/-- **The deep rule on one equation is stable** when R86's in-place rule is. -/
theorem deepEquation_stable (fuel : Nat)
    (inPlace : InPlaceStable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel)
    {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (rest : EquationStore (TotalTerm Θ)) :
    SolvedStable (ContextualDependentRigidFormers.deepEquation facts roots heads algebra declared choices reducer
      rigid complete root normalizes certifyNormal headTypingUnique fuel equation rest) := by
  intro update smaller fired
  unfold ContextualDependentRigidFormers.deepEquation at fired
  obtain ⟨parts, computed, fired⟩ := Option.bind_eq_some_iff.mp fired
  refine afterParts_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique sn fuel inPlace _ ?_ update smaller fired
  intro before permuted
  change PermutedMiller S.levels ((frames S.levels).applyStore (𝟙 Θ) before ++
    (ContextualDependentRigidFormers.decomposeDeep facts roots heads algebra declared choices reducer complete fuel
      (ContextualDependentRigidFormers.storeNodes (equation :: rest)) (parts.val ++ rest)).val)
  rw [applyStore_identity]
  exact decomposeDeep_position facts roots heads algebra rigid complete declared choices reducer sn fuel _ _ before
    (PermutedMiller.splice_underReducts rigid sn facts algebra permuted
      (formerParts_codes facts roots heads algebra complete declared choices reducer fuel computed) parts.val rfl
      fun σ => (parts.property σ).symm)

include sn in
theorem deepSearch_stable (fuel : Nat)
    (inPlace : InPlaceStable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel)
    {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), SolvedStable (ContextualDependentRigidFormers.deepSearch facts roots
      heads algebra declared choices reducer rigid complete root normalizes certifyNormal headTypingUnique fuel problem)
  | [] => fun _ _ fired => by cases fired
  | equation :: rest => by
      intro update smaller fired
      simp only [ContextualDependentRigidFormers.deepSearch] at fired
      split at fired
      · rename_i found computed
        cases fired
        exact deepEquation_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique sn fuel inPlace equation rest update smaller computed
      · exact solvedStable_keepLeft equation (deepSearch_stable fuel inPlace rest) update smaller fired

include sn in
/-- **Deep decomposition keeps the class** wherever R86's in-place rule is stable. -/
theorem deepSearch_keeps_of_inPlace (fuel : Nat)
    (inPlace : InPlaceStable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel) :
    RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      ContextualDependentRigidFormers.deepSearch facts roots heads algebra declared choices reducer rigid complete root
        normalizes certifyNormal headTypingUnique fuel problem :=
  fun _ problem permuted => foundKeeps_of_stable permuted
    (deepSearch_stable facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique sn fuel inPlace problem)

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
