import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidFormersRounds

/-!
# η-expansion of a neutral side against an abstraction

The scoped reading of a store equation opens both sides along the spine discovered from the
**left** side's leading abstractions: each side is applied to the fresh locals and normalized. When
the left side is neutral and the right side is an abstraction, the reading has too short a spine:
`f ≐ λ x. F f x` stays a comparison of a local with an abstraction, which no rule reads.

**η-expansion** reads the equation from its side with more leading abstractions instead. The neutral
side is then applied to the fresh locals: the scoped reading compares `F f x` with `f x`, the
η-expansion `f ≡ λ x. f x` followed by β, whose exactness is the scoped reading's own
(`Spine.opened_models_iff`). Exchanging the sides keeps exactly the solutions (`swap_equivalent`).

As for decompositions, the reoriented store is examined at once by the clash test, the first of the
pattern, prune and exchange rules, and the in-place rule; otherwise nothing is committed.

The module also gives the combinator that extends a round by one rule on the prepared store, used for
the η round and later rounds (`extendRound`), with its view and its eventual constancy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaExpansion

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentInPlace ContextualDependentRigidFormers ContextualDependentConversionBudget

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Exchanging the sides -/

/-- The equation read from its right side. -/
def swap {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Equation (TotalTerm Θ) := (equation.2, equation.1)

theorem solves_swap {Θ Δ : Context S.R} (σ : Δ ⟶ Θ) (equation : Equation (TotalTerm Θ)) :
    (frames S.levels).Solves σ (swap equation) ↔ (frames S.levels).Solves σ equation :=
  ⟨fun held => ((frames S.levels).equivalence Δ).symm held, fun held => ((frames S.levels).equivalence Δ).symm held⟩

/-- **Exchanging the sides keeps exactly the solutions.** -/
theorem swap_equivalent {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (rest : EquationStore (TotalTerm Θ)) :
    (frames S.levels).Equivalent (equation :: rest) (swap equation :: rest) := fun _ σ => by
  rw [models_cons, models_cons, solves_swap]

/-! ## Extending a round by one rule -/

section Extend

variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (root : ExecutableReduction.RootEvaluator S.R)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)
  (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (base : Nat → {Θ : Context S.R} → (problem : EquationStore (TotalTerm Θ)) → Round S.levels size problem)
  (rule : Nat → {Θ : Context S.R} → (problem : EquationStore (TotalTerm Θ)) → Option (Found problem))

omit [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative] in
/-- **A round extended by one rule**: the base round, and when it is stuck, the rule on the prepared
store. Every progress of the rule removes a declaration; its refutations are certified. -/
def extendRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Round S.levels size problem :=
  match base fuel problem with
  | .progress update smaller => .progress update smaller
  | .refuted absent => .refuted absent
  | .stuck =>
      match rule fuel (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining with
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

omit [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative] in
/-- The extended round, read through its view. -/
theorem extendRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (extendRound root rootComplete facts roots heads base rule fuel problem) =
      (roundView (base fuel problem)).or
        ((foundView (rule fuel
          (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining)).map
          (Option.map fun update =>
            (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).then update)) := by
  unfold extendRound
  split
  · rename_i update smaller computed
    simp only [computed, roundView, Option.or]
  · rename_i absent computed
    simp only [computed, roundView, Option.or]
  · rename_i computed
    split
    · rename_i update smaller found
      simp only [computed, found, roundView, foundView, Option.or, Option.map_some]
    · rename_i absent found
      simp only [computed, found, roundView, foundView, Option.or, Option.map_some, Option.map_none]
    · rename_i found
      simp only [computed, found, roundView, foundView, Option.or, Option.map_none]

omit [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative] in
/-- **An extended round is eventually constant** when its base round and its rule are. -/
theorem extendRound_const
    (baseConst : ∀ {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)), EventuallyConst fun fuel => base fuel problem)
    (ruleConst : ∀ {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)), EventuallyConst fun fuel => rule fuel problem)
    {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => extendRound root rootComplete facts roots heads base rule fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => extendRound_view root rootComplete facts roots heads base rule fuel problem) ?_
  exact EventuallyConst.dep (h := fun fuel =>
      (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem,
        roundView (base fuel problem)))
    (k := fun fuel pair => pair.2.or
      ((foundView (rule fuel pair.1.remaining)).map (Option.map fun update => pair.1.then update)))
    (EventuallyConst.pair (prepare_const root rootComplete facts roots heads problem)
      (EventuallyConst.comp roundView (baseConst problem)))
    (fun pair => EventuallyConst.comp (fun found => pair.2.or ((foundView found).map
        (Option.map fun update => pair.1.then update)))
      (ruleConst pair.1.remaining))

omit [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative] in
/-- **Every refutation of an extended round is certified**: the base round's, or the rule's on the
prepared store. -/
theorem extendRound_refuted {fuel : Nat} {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    {absent : ¬ (frames S.levels).Solvable problem}
    (refuted : extendRound root rootComplete facts roots heads base rule fuel problem = .refuted absent) :
    (∃ absent', base fuel problem = .refuted absent') ∨
      ∃ absent', rule fuel (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel
        problem).remaining = some (.refuted absent') := by
  unfold extendRound at refuted
  split at refuted
  · cases refuted
  · rename_i absent' computed
    exact .inl ⟨absent', computed⟩
  · split at refuted
    · cases refuted
    · rename_i absent' computed
      exact .inr ⟨absent', computed⟩
    · cases refuted

end Extend

/-! ## The η rule -/

variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)

/-- **η-expansion of one equation**: when its right side has more leading abstractions, it is read
from the right, so that the left side is η-expanded by the scoped reading; the rules then run on the
reoriented store. -/
def etaEquation (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (rest : EquationStore (TotalTerm Θ)) : Option (Found (equation :: rest)) :=
  if lamDepth equation.1.2.code < lamDepth equation.2.2.code then
    afterParts facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
      headTypingUnique fuel (swap equation :: rest) (swap_equivalent equation rest)
  else none

/-- Search the store for an equation whose η-expansion decides. -/
def etaSearch (fuel : Nat) {Θ : Context S.R} : (problem : EquationStore (TotalTerm Θ)) → Option (Found problem)
  | [] => none
  | equation :: rest =>
      match etaEquation facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
          headTypingUnique fuel equation rest with
      | some found => some found
      | none => (etaSearch fuel rest).map (Found.keepLeft equation)

/-- **One η round**: the rigid-former round, and when it is stuck, η-expansion on the prepared store. -/
def etaRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Round S.levels size problem :=
  extendRound root rootComplete facts roots heads
    (fun fuel => formersRound facts roots heads algebra declared choices reducer rigid complete root normalizes
      certifyNormal headTypingUnique rootComplete fuel)
    (fun fuel => etaSearch facts roots heads algebra declared choices reducer rigid complete root normalizes
      certifyNormal headTypingUnique fuel) fuel problem

/-- **The η family.** -/
def etaFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := size
  round fuel := etaRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
    headTypingUnique rootComplete fuel

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))
include stable

theorem etaEquation_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (rest : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => etaEquation facts roots heads algebra declared choices reducer rigid complete root
      normalizes certifyNormal headTypingUnique fuel equation rest := by
  by_cases deeper : lamDepth equation.1.2.code < lamDepth equation.2.2.code
  · obtain ⟨threshold, same⟩ := (afterParts_const facts roots heads algebra declared choices reducer rigid complete root
      normalizes certifyNormal headTypingUnique stable (swap equation :: rest) (swap_equivalent equation rest)).spec
    refine ⟨threshold, fun fuel enough => ?_⟩
    dsimp only
    unfold etaEquation
    rw [if_pos deeper, if_pos deeper]
    exact same fuel enough
  · refine ⟨0, fun fuel _ => ?_⟩
    dsimp only
    unfold etaEquation
    rw [if_neg deeper, if_neg deeper]

theorem etaSearch_const {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), EventuallyConst fun fuel =>
      etaSearch facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique fuel problem
  | [] => EventuallyConst.const _
  | equation :: rest => by
      obtain ⟨t₁, first⟩ := (etaEquation_const facts roots heads algebra declared choices reducer rigid complete root
        normalizes certifyNormal headTypingUnique stable equation rest).spec
      obtain ⟨t₂, later⟩ := (etaSearch_const rest).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      dsimp only
      simp only [etaSearch]
      erw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), later fuel (le_of_max_le_right enough),
        later _ (le_max_right _ _)]

/-- **The η round is eventually constant on every store.** -/
theorem etaRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => etaRound facts roots heads algebra declared choices reducer rigid complete root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem :=
  extendRound_const root rootComplete facts roots heads _ _
    (fun problem => formersRound_const facts roots heads algebra declared choices reducer rigid complete root
      normalizes certifyNormal headTypingUnique rootComplete stable problem)
    (fun problem => etaSearch_const facts roots heads algebra declared choices reducer rigid complete root normalizes
      certifyNormal headTypingUnique stable problem) problem

/-- **The η family settles** on every class of stores on which, at each nonempty store and from some
budget on, its round is not stuck and keeps every residual store in the class. -/
def etaSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        etaRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
            headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem} {smaller : Below (size update.remaining) (size problem)},
          etaRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
              headTypingUnique rootComplete larger problem = .progress update smaller → holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (etaFamily facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => etaRound_const facts roots heads algebra declared choices reducer rigid complete
    root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end ContextualDependentEtaExpansion
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
