import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidFormersSpine
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentOccursCheck

/-!
# The spine round

The two-argument decomposition of a store equation reads the equation under its telescope, splits it
into the two argument equations, closes them, and examines the decomposed store at once: the
distinct-locals rule may refute it, then a rigid clash, the first of the pattern, prune and exchange
rules, or the in-place rule may decide it. Otherwise nothing is committed.

The **spine round** extends the occurs round by this rule. It is eventually constant on every store.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRigidFormers

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist ContextualDependentScope
open ContextualDependentPiSpine ContextualDependentPatternSolver ContextualDependentDecisiveFragment
open ContextualDependentFragment ContextualDependentInPlace ContextualDependentEtaExpansion
open ContextualDependentOccursCheck ContextualDependentConversionBudget

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
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

/-- The scoped reading of a store equation. -/
abbrev Reading {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :=
  (scope : Spine equation.1.1) × (active : Active scope.target) ×'
    ∀ {Δ : Context S.R} (solution : Δ ⟶ Θ),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution

/-- What the spine rule does after the decomposition: close both argument equations and run the
rules on the decomposed store. -/
def twoContinue (fuel : Nat) {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (rest : EquationStore (TotalTerm Θ))
    (reading : Reading equation)
    (found : {pair : Active reading.1.target × Active reading.1.target // ∀ {Δ : Context S.R} (solution : Δ ⟶ Θ),
      (reading.1.toScoped reading.2.1).Holds solution ↔
        (reading.1.toScoped pair.1).Holds solution ∧ (reading.1.toScoped pair.2).Holds solution}) :
    Option (Found (equation :: rest)) :=
  match firstComputed : (reading.1.toScoped found.val.1).closeWith S.levels choices,
      secondComputed : (reading.1.toScoped found.val.2).closeWith S.levels choices with
  | some firstClosed, some secondClosed =>
      let same := id_replace_equivalent choices reading.2.2 found.property firstComputed secondComputed rest
      match ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared choices
          reducer root fuel (firstClosed.equation :: secondClosed.equation :: rest) with
      | some absent => some (.refuted fun solvable =>
          absent.down (((Update.pending S.levels _).rephrase same).solvable_iff.mp solvable))
      | none => afterParts facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
          headTypingUnique fuel (firstClosed.equation :: secondClosed.equation :: rest) same
  | _, _ => none

/-- **The spine rule on one store equation.** -/
def twoEquation (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (rest : EquationStore (TotalTerm Θ)) :
    Option (Found (equation :: rest)) :=
  (viewEquation facts roots heads algebra declared choices reducer root fuel equation).bind fun reading =>
    (decomposeTwoActive facts roots heads algebra complete declared choices reducer fuel reading.1 reading.2.1).bind
      fun found => twoContinue facts roots heads algebra declared choices reducer rigid complete root normalizes
        certifyNormal headTypingUnique fuel rest reading found

/-- Search the store for an equation whose two-argument decomposition decides. -/
def twoSearch (fuel : Nat) {Θ : Context S.R} : (problem : EquationStore (TotalTerm Θ)) → Option (Found problem)
  | [] => none
  | equation :: rest =>
      match twoEquation facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
          headTypingUnique fuel equation rest with
      | some found => some found
      | none => (twoSearch fuel rest).map (Found.keepLeft equation)

/-- **One spine round**: the occurs round, and when it is stuck, the spine rule on the prepared store. -/
def spineRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Round S.levels size problem :=
  extendRound root rootComplete facts roots heads
    (fun fuel => occursRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel)
    (fun fuel => twoSearch facts roots heads algebra declared choices reducer rigid complete root normalizes
      certifyNormal headTypingUnique fuel) fuel problem

/-- **The spine family.** -/
def spineFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := size
  round fuel := spineRound facts roots heads algebra declared choices reducer rigid complete root normalizes
    certifyNormal headTypingUnique rootComplete fuel

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))
include stable

theorem decomposeTwoActive_const {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (active : Active scope.target) :
    EventuallyConst fun fuel =>
      decomposeTwoActive facts roots heads algebra complete declared choices reducer fuel scope active := by
  cases shaped : twoShape scope active with
  | none =>
      refine ⟨0, fun fuel _ => ?_⟩
      simp only [decomposeTwoActive, shaped]
  | some shape =>
      obtain ⟨t₁, s₁⟩ := (formType_const facts roots heads algebra declared choices reducer stable
        (Γ := scope.target) shape.domain₁).spec
      obtain ⟨t₂, s₂⟩ := (formType_const facts roots heads algebra declared choices reducer stable
        (Γ := scope.target) shape.domain₂).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      simp only [decomposeTwoActive, shaped]
      erw [s₁ fuel (le_of_max_le_left enough), s₁ _ (le_max_left _ _), s₂ fuel (le_of_max_le_right enough),
        s₂ _ (le_max_right _ _)]

theorem twoContinue_const {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (rest : EquationStore (TotalTerm Θ))
    (reading : Reading equation)
    (found : {pair : Active reading.1.target × Active reading.1.target // ∀ {Δ : Context S.R} (solution : Δ ⟶ Θ),
      (reading.1.toScoped reading.2.1).Holds solution ↔
        (reading.1.toScoped pair.1).Holds solution ∧ (reading.1.toScoped pair.2).Holds solution}) :
    EventuallyConst fun fuel => twoContinue facts roots heads algebra declared choices reducer rigid complete root
      normalizes certifyNormal headTypingUnique fuel rest reading found := by
  unfold twoContinue
  split
  · rename_i firstClosed secondClosed firstComputed secondComputed
    obtain ⟨t₁, locals⟩ := (localsRule_const facts roots heads algebra declared choices reducer root stable rigid
      complete (firstClosed.equation :: secondClosed.equation :: rest)).spec
    obtain ⟨t₂, after⟩ := (afterParts_const facts roots heads algebra declared choices reducer rigid complete root
      normalizes certifyNormal headTypingUnique stable (firstClosed.equation :: secondClosed.equation :: rest)
      (id_replace_equivalent choices reading.2.2 found.property firstComputed secondComputed rest)).spec
    refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
    dsimp only
    erw [locals fuel (le_of_max_le_left enough), locals _ (le_max_left _ _), after fuel (le_of_max_le_right enough),
      after _ (le_max_right _ _)]
  · exact EventuallyConst.const _

theorem twoEquation_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (rest : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => twoEquation facts roots heads algebra declared choices reducer rigid complete root
      normalizes certifyNormal headTypingUnique fuel equation rest :=
  EventuallyConst.dep (h := fun fuel => viewEquation facts roots heads algebra declared choices reducer root fuel equation)
    (k := fun fuel reading => reading.bind fun reading =>
      (decomposeTwoActive facts roots heads algebra complete declared choices reducer fuel reading.1 reading.2.1).bind
        fun found => twoContinue facts roots heads algebra declared choices reducer rigid complete root normalizes
          certifyNormal headTypingUnique fuel rest reading found)
    (viewEquation_const facts roots heads algebra declared choices reducer root stable equation)
    (fun reading => by
      cases reading with
      | none => exact EventuallyConst.const _
      | some reading =>
          exact EventuallyConst.dep
            (h := fun fuel => decomposeTwoActive facts roots heads algebra complete declared choices reducer fuel
              reading.1 reading.2.1)
            (k := fun fuel found => found.bind fun found => twoContinue facts roots heads algebra declared choices
              reducer rigid complete root normalizes certifyNormal headTypingUnique fuel rest reading found)
            (decomposeTwoActive_const facts roots heads algebra declared choices reducer complete stable reading.1
              reading.2.1)
            (fun found => by
              cases found with
              | none => exact EventuallyConst.const _
              | some found =>
                  exact twoContinue_const facts roots heads algebra declared choices reducer rigid complete root
                    normalizes certifyNormal headTypingUnique stable rest reading found))

theorem twoSearch_const {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), EventuallyConst fun fuel =>
      twoSearch facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique fuel problem
  | [] => EventuallyConst.const _
  | equation :: rest => by
      obtain ⟨t₁, first⟩ := (twoEquation_const facts roots heads algebra declared choices reducer rigid complete root
        normalizes certifyNormal headTypingUnique stable equation rest).spec
      obtain ⟨t₂, later⟩ := (twoSearch_const rest).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      dsimp only
      simp only [twoSearch]
      erw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), later fuel (le_of_max_le_right enough),
        later _ (le_max_right _ _)]

/-- **The spine round is eventually constant on every store.** -/
theorem spineRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => spineRound facts roots heads algebra declared choices reducer rigid complete root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem :=
  extendRound_const root rootComplete facts roots heads _ _
    (fun problem => occursRound_const facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete stable problem)
    (fun problem => twoSearch_const facts roots heads algebra declared choices reducer rigid complete root normalizes
      certifyNormal headTypingUnique stable problem) problem

/-- **The spine family settles** on every class of stores on which, at each nonempty store and from
some budget on, its round is not stuck and keeps every residual store in the class. -/
def spineSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        spineRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
            headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem} {smaller : Below (size update.remaining) (size problem)},
          spineRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
              headTypingUnique rootComplete larger problem = .progress update smaller → holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (spineFamily facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => spineRound_const facts roots heads algebra declared choices reducer rigid complete
    root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end ContextualDependentRigidFormers
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
