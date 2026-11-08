import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentDecidedIdentity

/-!
# The identity round is eventually constant

The identity decomposition reads the budget through the scoped reading, the formation of the
carrier, the distinct-locals rule and the pattern rule on the decomposed store. Each is eventually
constant, so the identity decomposition of every store equation, its search through the store and
the **identity round** are eventually constant on every store. The identity family therefore
settles on every class where, from some budget on, its round is not stuck and keeps its residual
stores in the class (`identitySettledOfConst`).
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
variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))
include stable

/-- **The identity decomposition of one scoped equation is eventually constant.** -/
theorem idDecomposeActive_const {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (active : Active scope.target) :
    EventuallyConst fun fuel =>
      idDecomposeActive facts roots heads algebra declared choices reducer fuel scope active := by
  cases leftCode : active.left.code with
  | id A a b =>
      obtain ⟨threshold, same⟩ := (formType_const facts roots heads algebra declared choices reducer stable
        (Γ := scope.target) A).spec
      refine ⟨threshold, fun fuel enough => idDecomposeActive_congr facts roots heads algebra declared choices reducer
        scope active fun A' a' b' code => ?_⟩
      rw [leftCode] at code
      cases code
      exact same fuel enough
  | _ =>
      refine ⟨0, fun fuel _ => idDecomposeActive_congr facts roots heads algebra declared choices reducer scope active
        fun A a b code => ?_⟩
      rw [leftCode] at code
      cases code

/-- **The identity decomposition of one store equation is eventually constant.** -/
theorem idDecomposeEquation_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (rest : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      idDecomposeEquation facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        fuel equation rest := by
  obtain ⟨t₁, viewed⟩ := (viewEquation_const facts roots heads algebra declared choices reducer root stable
    equation).spec
  cases viewRun : viewEquation facts roots heads algebra declared choices reducer root t₁ equation with
  | none =>
      refine ⟨t₁, fun fuel enough => ?_⟩
      dsimp only
      unfold idDecomposeEquation
      erw [viewed fuel enough, viewRun]
  | some reading =>
      obtain ⟨scope, active, view⟩ := reading
      obtain ⟨t₂, decomposed⟩ := (idDecomposeActive_const facts roots heads algebra declared choices reducer stable
        scope active).spec
      cases decomposeRun : idDecomposeActive facts roots heads algebra declared choices reducer t₂ scope active with
      | none =>
          refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
          dsimp only
          unfold idDecomposeEquation
          erw [viewed fuel (le_of_max_le_left enough), viewRun, viewed _ (le_max_left _ _), viewRun]
          dsimp only
          erw [decomposed fuel (le_of_max_le_right enough), decomposeRun, decomposed _ (le_max_right _ _),
            decomposeRun]
      | some found =>
          obtain ⟨⟨first, second⟩, split⟩ := found
          cases firstClosing : (scope.toScoped first).closeWith S.levels choices with
          | none =>
              refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
              dsimp only
              unfold idDecomposeEquation
              erw [viewed fuel (le_of_max_le_left enough), viewRun, viewed _ (le_max_left _ _), viewRun]
              dsimp only
              erw [decomposed fuel (le_of_max_le_right enough), decomposeRun, decomposed _ (le_max_right _ _),
                decomposeRun]
              dsimp only
              split
              · rename_i firstClosed secondClosed firstComputed _
                rw [firstComputed] at firstClosing
                cases firstClosing
              · rfl
          | some firstClosed₀ =>
              cases secondClosing : (scope.toScoped second).closeWith S.levels choices with
              | none =>
                  refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
                  dsimp only
                  unfold idDecomposeEquation
                  erw [viewed fuel (le_of_max_le_left enough), viewRun, viewed _ (le_max_left _ _), viewRun]
                  dsimp only
                  erw [decomposed fuel (le_of_max_le_right enough), decomposeRun, decomposed _ (le_max_right _ _),
                    decomposeRun]
                  dsimp only
                  split
                  · rename_i firstClosed secondClosed _ secondComputed
                    rw [secondComputed] at secondClosing
                    cases secondClosing
                  · rfl
              | some secondClosed₀ =>
                  obtain ⟨t₃, localsSame⟩ := (localsRule_const facts roots heads algebra declared choices reducer root
                    stable rigid complete (firstClosed₀.equation :: secondClosed₀.equation :: rest)).spec
                  obtain ⟨t₄, patternSame⟩ := (patternRule_const rigid facts complete roots heads algebra declared
                    choices reducer root normalizes certifyNormal stable
                    (firstClosed₀.equation :: secondClosed₀.equation :: rest)).spec
                  refine ⟨max (max t₁ t₂) (max t₃ t₄), fun fuel enough => ?_⟩
                  have e₁ : t₁ ≤ fuel := by omega
                  have e₂ : t₂ ≤ fuel := by omega
                  have e₃ : t₃ ≤ fuel := by omega
                  have e₄ : t₄ ≤ fuel := by omega
                  have f₁ : t₁ ≤ max (max t₁ t₂) (max t₃ t₄) := by omega
                  have f₂ : t₂ ≤ max (max t₁ t₂) (max t₃ t₄) := by omega
                  have f₃ : t₃ ≤ max (max t₁ t₂) (max t₃ t₄) := by omega
                  have f₄ : t₄ ≤ max (max t₁ t₂) (max t₃ t₄) := by omega
                  dsimp only
                  unfold idDecomposeEquation
                  erw [viewed fuel e₁, viewRun, viewed _ f₁, viewRun]
                  dsimp only
                  erw [decomposed fuel e₂, decomposeRun, decomposed _ f₂, decomposeRun]
                  dsimp only
                  split
                  · rename_i firstClosed secondClosed firstComputed secondComputed
                    rw [firstComputed] at firstClosing
                    rw [secondComputed] at secondClosing
                    cases firstClosing
                    cases secondClosing
                    erw [localsSame fuel e₃, localsSame _ f₃, patternSame fuel e₄, patternSame _ f₄]
                  · rfl

/-- **The identity search through the store is eventually constant.** -/
theorem idDecomposeSearch_const {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), EventuallyConst fun fuel =>
      idDecomposeSearch facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        fuel problem
  | [] => EventuallyConst.const _
  | equation :: rest => by
      obtain ⟨t₁, first⟩ := (idDecomposeEquation_const facts roots heads algebra declared choices reducer rigid complete
        root normalizes certifyNormal stable equation rest).spec
      obtain ⟨t₂, later⟩ := (idDecomposeSearch_const rest).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      dsimp only
      simp only [idDecomposeSearch]
      erw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), later fuel (le_of_max_le_right enough),
        later _ (le_max_right _ _)]

/-- **The identity round is eventually constant on every store.** -/
theorem identityRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      identityRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => identityRound_view facts roots heads algebra declared choices reducer rigid
    complete root normalizes certifyNormal headTypingUnique rootComplete fuel problem) ?_
  exact EventuallyConst.dep (h := fun fuel =>
      (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem,
        roundView (fragmentRound rigid facts complete roots heads algebra declared choices reducer root rootComplete
          normalizes certifyNormal headTypingUnique fuel problem)))
    (k := fun fuel pair => identityView pair.1 (idDecomposeSearch facts roots heads algebra declared choices reducer
      rigid complete root normalizes certifyNormal fuel pair.1.remaining) pair.2)
    (EventuallyConst.pair (prepare_const root rootComplete facts roots heads problem)
      (EventuallyConst.comp roundView (fragmentRound_const rigid facts complete roots heads algebra declared choices
        reducer root rootComplete normalizes certifyNormal headTypingUnique stable problem)))
    (fun pair => EventuallyConst.comp (fun found => identityView pair.1 found pair.2)
      (idDecomposeSearch_const facts roots heads algebra declared choices reducer rigid complete root normalizes
        certifyNormal stable pair.1.remaining))

/-- **The identity family settles** on every class of stores on which, at each nonempty store and
from some budget on, the identity round is not stuck and keeps every residual store in the class. -/
def identitySettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        identityRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
            headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem} {smaller : Below (size update.remaining) (size problem)},
          identityRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
              headTypingUnique rootComplete larger problem = .progress update smaller → holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (identityFamily facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => identityRound_const facts roots heads algebra declared choices reducer rigid
    complete root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end ContextualDependentFragment
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
