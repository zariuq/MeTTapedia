import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentFiring

/-!
# Decomposing identity types with one carrier

The fragment round reads no rigid–rigid equation between two type formers. The first repair is
the decomposition of identity types: at a universe, `Id A a b ≐ Id A a' b'` has **exactly** the
solutions of `a ≐ a'` and `b ≐ b'` at `A`, in every future context (`id_decompose_scoped`).

* One direction is the injectivity of identity types (`typeEq_id_iff`).
* The other is congruence at the carrier's own universe, which generation supplies after
  substitution, followed by cumulativity up to the equation's universe.

No inhabitation premise and no universe join are needed.

As for the local-application decomposition, a decomposition alone does not lower the rank, so the
**identity decomposition** of a store equation continues at once on the decomposed store: the
distinct-locals rule may refute it, or the pattern rule may solve the newest metavariable.
Otherwise nothing is committed.

The **identity round** prepares the store, tries the identity decomposition on the prepared store,
and otherwise runs the fragment round. Every refutation is certified, every progress lowers the
rank, and the round is eventually constant on every store.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFragment

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist ContextualDependentScope
open ContextualDependentPiSpine ContextualDependentPatternSolver ContextualDependentGeneralPattern
open ContextualDependentDecisiveFragment ContextualDependentConversionBudget

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## The decomposition of one scoped equation -/

/-- The endpoints of a typed identity type are typed at its carrier. -/
theorem id_endpoints_typed {n : Nat} {Γ : Ctx Head n} {A a b T : Tm Head n} (typed : Typed S.R Γ (.id A a b) T) :
    Typed S.R Γ a A ∧ Typed S.R Γ b A := by
  obtain ⟨_, _, _, first, second, _⟩ := typed.generation
  exact ⟨first, second⟩

variable [DecidableRel S.R.headEq] (facts : FormFacts S.R S.roles)

omit [DecidableRel S.R.headEq] in
include facts in
/-- **Identity types with one carrier decompose**, with exactly the original solutions in every
future context. -/
theorem id_decompose_scoped {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (equation first second : Active scope.target) {u : Head} (universal : S.R.isUniverse u)
    (typeCode : equation.type.code = .head u) {A : Tm Head scope.target.arity}
    (firstType : first.type.code = A) (secondType : second.type.code = A)
    (leftCode : equation.left.code = .id A first.left.code second.left.code)
    (rightCode : equation.right.code = .id A first.right.code second.right.code)
    {Δ : Context S.R} (solution : Δ ⟶ Γ) :
    (scope.toScoped equation).Holds solution ↔
      (scope.toScoped first).Holds solution ∧ (scope.toScoped second).Holds solution := by
  rw [Spine.toScoped_holds_iff, Spine.toScoped_holds_iff, Spine.toScoped_holds_iff]
  have typed := equation.left.typed
  change Equal S.R (scope.reindex solution).target.raw (subst (scope.map solution).substitution equation.left.code)
      (subst (scope.map solution).substitution equation.right.code)
      (subst (scope.map solution).substitution equation.type.code) ↔
    Equal S.R (scope.reindex solution).target.raw (subst (scope.map solution).substitution first.left.code)
        (subst (scope.map solution).substitution first.right.code)
        (subst (scope.map solution).substitution first.type.code) ∧
      Equal S.R (scope.reindex solution).target.raw (subst (scope.map solution).substitution second.left.code)
        (subst (scope.map solution).substitution second.right.code)
        (subst (scope.map solution).substitution second.type.code)
  rw [leftCode, rightCode, typeCode, firstType, secondType]
  change Equal S.R (scope.reindex solution).target.raw
      (.id (subst (scope.map solution).substitution A) (subst (scope.map solution).substitution first.left.code)
        (subst (scope.map solution).substitution second.left.code))
      (.id (subst (scope.map solution).substitution A) (subst (scope.map solution).substitution first.right.code)
        (subst (scope.map solution).substitution second.right.code)) (.head u) ↔ _
  constructor
  · intro held
    exact (ContextualDependentRigid.typeEq_id_iff facts (scope.reindex solution).target.formed).mp ⟨u, universal, held⟩
      |>.2
  · rintro ⟨firsts, seconds⟩
    rw [leftCode, typeCode] at typed
    have moved := typed.substitute (scope.map solution).typed
    change Typed S.R (scope.reindex solution).target.raw
      (.id (subst (scope.map solution).substitution A) (subst (scope.map solution).substitution first.left.code)
        (subst (scope.map solution).substitution second.left.code)) (.head u) at moved
    obtain ⟨level, carrier, carrierUniverse, _, _, below⟩ := moved.generation
    exact Equal.subsume (Derivable.idCong (.refl carrier) carrierUniverse firsts seconds) below

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (declared : DeclaredTypesFormed S.R) (choices : ExecutableChecking.HeadChoices S.R)
  (reducer : ExecutableReduction.Reducer S.R)

/-- **The identity decomposition of one scoped equation**: two endpoint equations with exactly
the same solutions. -/
def idDecomposeActive (fuel : Nat) {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (active : Active scope.target) :
    Option {pair : Active scope.target × Active scope.target // ∀ {Δ : Context S.R} (solution : Δ ⟶ Γ),
      (scope.toScoped active).Holds solution ↔
        (scope.toScoped pair.1).Holds solution ∧ (scope.toScoped pair.2).Holds solution} :=
  match leftCode : active.left.code, rightCode : active.right.code, typeCode : active.type.code with
  | .id A a b, .id A' a' b', .head u =>
      if same : A' = A then
        if universal : S.R.isUniverse u then
          match ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel
              scope.target A with
          | none => none
          | some carrier =>
              have lefts := id_endpoints_typed (S := S) (by rw [← leftCode]; exact active.left.typed)
              have rights := id_endpoints_typed (S := S) (by rw [← rightCode]; exact active.right.typed)
              let first : Active scope.target :=
                ⟨carrier.val, ⟨a, by rw [carrier.property]; exact lefts.1⟩,
                  ⟨a', by rw [carrier.property, ← same]; exact rights.1⟩⟩
              let second : Active scope.target :=
                ⟨carrier.val, ⟨b, by rw [carrier.property]; exact lefts.2⟩,
                  ⟨b', by rw [carrier.property, ← same]; exact rights.2⟩⟩
              some ⟨(first, second), fun solution =>
                id_decompose_scoped facts scope active first second universal typeCode carrier.property
                  carrier.property leftCode (by rw [rightCode, same]) solution⟩
        else none
      else none
  | _, _, _ => none

omit [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative] in
/-- Two endpoint equations with closed forms replace a store equation with the same solutions. -/
theorem id_replace_equivalent {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} {constraint first second : Scoped Θ}
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ Θ),
      (frames S.levels).Models solution [equation] ↔ constraint.Holds solution)
    (split : ∀ {Δ : Context S.R} (solution : Δ ⟶ Θ),
      constraint.Holds solution ↔ first.Holds solution ∧ second.Holds solution)
    {firstClosed secondClosed : Active Θ}
    (firstComputed : first.closeWith S.levels choices = some firstClosed)
    (secondComputed : second.closeWith S.levels choices = some secondClosed)
    (rest : EquationStore (TotalTerm Θ)) :
    (frames S.levels).Equivalent (equation :: rest) (firstClosed.equation :: secondClosed.equation :: rest) := by
  intro Δ solution
  have heads : (frames S.levels).Models solution [equation] ↔
      (frames S.levels).Models solution [firstClosed.equation, secondClosed.equation] := by
    rw [view solution, split solution,
      ← Scoped.closeWith_holds_iff S.levels choices first firstComputed solution,
      ← Scoped.closeWith_holds_iff S.levels choices second secondComputed solution,
      Active.holds_iff_models S.levels firstClosed solution, Active.holds_iff_models S.levels secondClosed solution]
    have pair := Frames.models_append (X := frames S.levels) solution [firstClosed.equation] [secondClosed.equation]
    exact pair.symm
  have whole := Frames.models_append (X := frames S.levels) solution [equation] rest
  have whole' := Frames.models_append (X := frames S.levels) solution [firstClosed.equation, secondClosed.equation] rest
  exact whole.trans ((and_congr_left fun _ => heads).trans whole'.symm)

variable (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

/-- **The identity decomposition of one store equation**, continued on the decomposed store by the
distinct-locals rule and the pattern rule. -/
def idDecomposeEquation (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (rest : EquationStore (TotalTerm Θ)) : Option (Found (equation :: rest)) :=
  match viewEquation facts roots heads algebra declared choices reducer root fuel equation with
  | none => none
  | some ⟨scope, active, view⟩ =>
      match idDecomposeActive facts roots heads algebra declared choices reducer fuel scope active with
      | none => none
      | some ⟨(first, second), split⟩ =>
          match firstComputed : (scope.toScoped first).closeWith S.levels choices,
              secondComputed : (scope.toScoped second).closeWith S.levels choices with
          | some firstClosed, some secondClosed =>
              let moved : Update S.levels (equation :: rest) :=
                (Update.pending S.levels (firstClosed.equation :: secondClosed.equation :: rest)).rephrase
                  (id_replace_equivalent choices view split firstComputed secondComputed rest)
              match ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared
                  choices reducer root fuel (firstClosed.equation :: secondClosed.equation :: rest) with
              | some absent => some (.refuted fun solvable => absent.down (moved.solvable_iff.mp solvable))
              | none =>
                  match patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes
                      certifyNormal fuel (firstClosed.equation :: secondClosed.equation :: rest) with
                  | some (.solved solved smaller) => some (.solved (moved.then solved) smaller)
                  | some (.refuted absent) => some (.refuted fun solvable => absent (moved.solvable_iff.mp solvable))
                  | none => none
          | _, _ => none

/-- Search the store for an equation on which the identity decomposition decides. -/
def idDecomposeSearch (fuel : Nat) {Θ : Context S.R} :
    (problem : EquationStore (TotalTerm Θ)) → Option (Found problem)
  | [] => none
  | equation :: rest =>
      match idDecomposeEquation facts roots heads algebra declared choices reducer rigid complete root normalizes
          certifyNormal fuel equation rest with
      | some found => some found
      | none => (idDecomposeSearch fuel rest).map (Found.keepLeft equation)

variable (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)

/-- **One identity round**: prepare, decompose an identity equation when that decides, and
otherwise run the fragment round. -/
def identityRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels size problem :=
  match idDecomposeSearch facts roots heads algebra declared choices reducer rigid complete root normalizes
      certifyNormal fuel (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining with
  | some (.solved update smaller) =>
      .progress ((ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).then update)
        (Prod.Lex.left _ _ (by
          have same := prepare_arity facts roots heads root rootComplete fuel problem
          change update.target.arity < Θ.arity
          omega))
  | some (.refuted absent) =>
      .refuted fun solvable =>
        absent ((ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).solvable_iff.mp
          solvable)
  | none => fragmentRound rigid facts complete roots heads algebra declared choices reducer root rootComplete normalizes
      certifyNormal headTypingUnique fuel problem

/-- **The identity solver** at one budget. -/
def identitySolver (fuel : Nat) : Solver S.levels where
  rank := size
  round := identityRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
    headTypingUnique rootComplete fuel

/-- **The identity solver as a fuel-indexed family.** -/
def identityFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := size
  round fuel := identityRound facts roots heads algebra declared choices reducer rigid complete root normalizes
    certifyNormal headTypingUnique rootComplete fuel

end ContextualDependentFragment
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
