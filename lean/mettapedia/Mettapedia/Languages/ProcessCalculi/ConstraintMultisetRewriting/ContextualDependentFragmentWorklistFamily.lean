import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentWorklistRounds

/-!
# The fragment round: every rule of the dependent solver in one round

The **fragment round** prepares the store (normalizing the context, the annotations and the sides),
runs the decomposition round on the prepared store (decomposition, then the distinct-locals rule,
then the pattern, prune and exchange rules, then the worklist round), and, when that is stuck,
rotates a deeper metavariable to the newest position. It is a worklist solver: every progress lowers
the rank and every refutation is a refutation by one of the rules, hence certified.

It is **eventually constant on every store** (`fragmentRound_const`), so it settles on any class of
stores on which, from some budget on, it is not stuck and keeps its residual stores in the class
(`fragmentSettled`). Decisiveness at one joint budget on such a class follows from
`Settled.decided`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFragment

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist ContextualDependentScope
open ContextualDependentPiSpine ContextualDependentPatternSolver
open ContextualDependentDecisiveFragment ContextualDependentConversionBudget

universe u v w

/-- Two eventually constant sequences are eventually constant together. -/
theorem EventuallyConst.pair {α : Type u} {β : Type v} {f : Nat → α} {g : Nat → β}
    (first : EventuallyConst f) (second : EventuallyConst g) : EventuallyConst fun fuel => (f fuel, g fuel) := by
  obtain ⟨t₁, same₁⟩ := first
  obtain ⟨t₂, same₂⟩ := second
  refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
  dsimp only
  rw [same₁ fuel (le_of_max_le_left enough), same₁ _ (le_max_left _ _), same₂ fuel (le_of_max_le_right enough),
    same₂ _ (le_max_right _ _)]

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- What a rule commits: an update, a refutation (`some none`), or nothing. -/
def foundView {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} :
    Option (Found problem) → Option (Option (Update S.levels problem))
  | some (.solved update _) => some (some update)
  | some (.refuted _) => some none
  | none => none

variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (rigid : ∀ name, S.roles name = .rigid) (facts : FormFacts S.R S.roles)
  (complete : AlgorithmicComplete S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

omit [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative] in
/-- The prepared context has as many declarations as the original one. -/
theorem prepare_arity (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).target.arity = Θ.arity :=
  congrArg Prod.fst (ContextualDependentNormalizing.prepare_size root rootComplete facts roots heads fuel problem)

/-- **One fragment round**: prepare, decompose and run the rigid round, and rotate when stuck. -/
def fragmentRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels size problem :=
  match ContextualDependentRigidDecomposition.decomposeRound rigid facts complete roots heads algebra declared choices
      reducer root normalizes certifyNormal headTypingUnique fuel
      (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining with
  | .progress update smaller =>
      .progress ((ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).then update)
        (by
          rw [ContextualDependentNormalizing.prepare_size] at smaller
          exact smaller)
  | .refuted absent =>
      .refuted fun solvable =>
        absent ((ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).solvable_iff.mp
          solvable)
  | .stuck =>
      match ContextualDependentPermutation.rotateRule rigid complete facts roots heads algebra declared choices reducer
          root normalizes certifyNormal fuel
          (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining with
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
      | none => .stuck

/-- **The fragment solver** at one budget. -/
def fragmentSolver (fuel : Nat) : Solver S.levels where
  rank := size
  round := fragmentRound rigid facts complete roots heads algebra declared choices reducer root rootComplete normalizes
    certifyNormal headTypingUnique fuel

/-- **The fragment solver as a fuel-indexed family**, for the joint-budget driver. -/
def fragmentFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := size
  round fuel := fragmentRound rigid facts complete roots heads algebra declared choices reducer root rootComplete
    normalizes certifyNormal headTypingUnique fuel

/-- **Every refutation of the fragment round is a refutation of the prepared store** by the
decomposition round or by rotation, both certified. -/
theorem fragmentRound_refuted {fuel : Nat} {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    {absent : ¬ (frames S.levels).Solvable problem}
    (refuted : fragmentRound rigid facts complete roots heads algebra declared choices reducer root rootComplete
      normalizes certifyNormal headTypingUnique fuel problem = .refuted absent) :
    (∃ absent', ContextualDependentRigidDecomposition.decomposeRound rigid facts complete roots heads algebra declared
        choices reducer root normalizes certifyNormal headTypingUnique fuel
        (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining =
          .refuted absent') ∨
      ∃ absent', ContextualDependentPermutation.rotateRule rigid complete facts roots heads algebra declared choices
        reducer root normalizes certifyNormal fuel
        (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining =
          some (.refuted absent') := by
  unfold fragmentRound at refuted
  split at refuted
  · cases refuted
  · rename_i absent' computed
    exact .inl ⟨absent', computed⟩
  · split at refuted
    · cases refuted
    · rename_i absent' computed
      exact .inr ⟨absent', computed⟩
    · cases refuted

/-- The fragment round, read through its view. -/
theorem fragmentRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (fragmentRound rigid facts complete roots heads algebra declared choices reducer root rootComplete
        normalizes certifyNormal headTypingUnique fuel problem) =
      ((roundView (ContextualDependentRigidDecomposition.decomposeRound rigid facts complete roots heads algebra
          declared choices reducer root normalizes certifyNormal headTypingUnique fuel
          (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining)).or
        (foundView (ContextualDependentPermutation.rotateRule rigid complete facts roots heads algebra declared choices
          reducer root normalizes certifyNormal fuel
          (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining))).map
        (Option.map fun update =>
          (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).then update) := by
  unfold fragmentRound
  split
  · rename_i update smaller computed
    simp only [computed, roundView, Option.or, Option.map_some]
  · rename_i absent computed
    simp only [computed, roundView, Option.or, Option.map_some, Option.map_none]
  · rename_i computed
    split
    · rename_i update smaller rotated
      simp only [computed, rotated, roundView, foundView, Option.or, Option.map_some]
    · rename_i absent rotated
      simp only [computed, rotated, roundView, foundView, Option.or, Option.map_some, Option.map_none]
    · rename_i rotated
      simp only [computed, rotated, roundView, foundView, Option.or, Option.map_none]

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))
include stable

/-- **The fragment round is eventually constant on every store.** -/
theorem fragmentRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      fragmentRound rigid facts complete roots heads algebra declared choices reducer root rootComplete normalizes
        certifyNormal headTypingUnique fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => fragmentRound_view rigid facts complete roots heads algebra declared
    choices reducer root rootComplete normalizes certifyNormal headTypingUnique fuel problem) ?_
  exact EventuallyConst.dep (h := fun fuel =>
      ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem)
    (k := fun fuel prepared =>
      ((roundView (ContextualDependentRigidDecomposition.decomposeRound rigid facts complete roots heads algebra
          declared choices reducer root normalizes certifyNormal headTypingUnique fuel prepared.remaining)).or
        (foundView (ContextualDependentPermutation.rotateRule rigid complete facts roots heads algebra declared choices
          reducer root normalizes certifyNormal fuel prepared.remaining))).map
        (Option.map fun update => prepared.then update))
    (prepare_const root rootComplete facts roots heads problem)
    (fun prepared => EventuallyConst.comp (fun pair => ((roundView pair.1).or (foundView pair.2)).map
        (Option.map fun update => prepared.then update))
      (EventuallyConst.pair
        (decomposeRound_const rigid facts complete roots heads algebra declared choices reducer root normalizes
          certifyNormal headTypingUnique stable prepared.remaining)
        (rotateRule_const rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          stable prepared.remaining)))

/-- **The fragment solver settles** on every class of stores on which, at each nonempty store and
from some budget on, the fragment round is not stuck and keeps every residual store in the class. -/
def fragmentSettled (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        fragmentRound rigid facts complete roots heads algebra declared choices reducer root rootComplete normalizes
            certifyNormal headTypingUnique larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem} {smaller : Below (size update.remaining) (size problem)},
          fragmentRound rigid facts complete roots heads algebra declared choices reducer root rootComplete normalizes
              certifyNormal headTypingUnique larger problem = .progress update smaller → holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (fragmentFamily rigid facts complete roots heads algebra declared choices reducer root rootComplete normalizes
        certifyNormal headTypingUnique) :=
  Settled.ofConst _ (fun problem => fragmentRound_const rigid facts complete roots heads algebra declared choices
    reducer root rootComplete normalizes certifyNormal headTypingUnique stable problem) holds eventual

end ContextualDependentFragment
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
