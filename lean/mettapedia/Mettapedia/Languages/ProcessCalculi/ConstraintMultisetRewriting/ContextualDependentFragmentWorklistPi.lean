import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentFiringPi
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentWorklistIdentity

/-!
# The Π round is eventually constant

The binder decomposition reads the budget only through type formation, whose successes are kept,
and falls through to nothing on every failure; so its successes are kept, and it is eventually
constant. With the scoped reading, the distinct-locals rule and the pattern rule eventually
constant, the binder decomposition of every store equation, its search and the **Π round** are
eventually constant on every store, and the Π family settles on every class where, from some budget
on, its round is not stuck and keeps its residual stores in the class (`piSettledOfConst`).
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

/-- **A Π decomposition found at one budget is kept.** -/
theorem piDecomposeActive_mono {fuel larger : Nat} {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (active : Active scope.target) {found}
    (computed : piDecomposeActive facts roots heads algebra declared choices reducer complete fuel scope active =
      some found) (enough : fuel ≤ larger) :
    piDecomposeActive facts roots heads algebra declared choices reducer complete larger scope active = some found := by
  have kept : ∀ {Γ' : Context S.R} {code : Tm Head Γ'.arity} {result},
      ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ' code = some result →
        ContextualDependentPruning.formType facts roots heads algebra declared choices reducer larger Γ' code =
          some result :=
    fun run => ContextualDependentRecoveryBudget.formType_mono facts roots heads algebra declared choices reducer stable
      run enough
  unfold piDecomposeActive at computed ⊢
  split at computed
  · rename_i A B A' B' u leftCode rightCode typeCode
    by_cases same : A' = A
    · rw [dif_pos same] at computed ⊢
      by_cases universal : S.R.isUniverse u
      · rw [dif_pos universal] at computed ⊢
        cases domainRun : ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel
            scope.target A with
        | none => rw [domainRun] at computed; cases computed
        | some domain =>
            rw [domainRun] at computed
            rw [kept domainRun]
            dsimp only at computed ⊢
            cases firstRun : ContextualDependentPruning.formType facts roots heads algebra declared choices reducer
                fuel (extend scope.target domain.val) B with
            | none => rw [firstRun] at computed; cases computed
            | some first =>
                cases secondRun : ContextualDependentPruning.formType facts roots heads algebra declared choices
                    reducer fuel (extend scope.target domain.val) B' with
                | none => rw [firstRun, secondRun] at computed; cases computed
                | some second =>
                    rw [firstRun, secondRun] at computed
                    rw [kept firstRun, kept secondRun]
                    dsimp only at computed ⊢
                    cases levelRun : codomainUniverse choices first.val.level second.val.level with
                    | none => rw [levelRun] at computed; cases computed
                    | some level =>
                        rw [levelRun] at computed
                        dsimp only at computed ⊢
                        cases annotationRun : ContextualDependentPruning.formType facts roots heads algebra declared
                            choices reducer fuel (extend scope.target domain.val) (.head level.val) with
                        | none => rw [annotationRun] at computed; cases computed
                        | some annotation =>
                            rw [annotationRun] at computed
                            rw [kept annotationRun]
                            exact computed
      · rw [dif_neg universal] at computed
        cases computed
    · rw [dif_neg same] at computed
      cases computed
  · cases computed

/-- **A Σ decomposition found at one budget is kept.** -/
theorem sigmaDecomposeActive_mono {fuel larger : Nat} {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (active : Active scope.target) {found}
    (computed : sigmaDecomposeActive facts roots heads algebra declared choices reducer complete fuel scope active =
      some found) (enough : fuel ≤ larger) :
    sigmaDecomposeActive facts roots heads algebra declared choices reducer complete larger scope active = some found := by
  have kept : ∀ {Γ' : Context S.R} {code : Tm Head Γ'.arity} {result},
      ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ' code = some result →
        ContextualDependentPruning.formType facts roots heads algebra declared choices reducer larger Γ' code =
          some result :=
    fun run => ContextualDependentRecoveryBudget.formType_mono facts roots heads algebra declared choices reducer stable
      run enough
  unfold sigmaDecomposeActive at computed ⊢
  split at computed
  · rename_i A B A' B' u leftCode rightCode typeCode
    by_cases same : A' = A
    · rw [dif_pos same] at computed ⊢
      by_cases universal : S.R.isUniverse u
      · rw [dif_pos universal] at computed ⊢
        cases domainRun : ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel
            scope.target A with
        | none => rw [domainRun] at computed; cases computed
        | some domain =>
            rw [domainRun] at computed
            rw [kept domainRun]
            dsimp only at computed ⊢
            cases firstRun : ContextualDependentPruning.formType facts roots heads algebra declared choices reducer
                fuel (extend scope.target domain.val) B with
            | none => rw [firstRun] at computed; cases computed
            | some first =>
                cases secondRun : ContextualDependentPruning.formType facts roots heads algebra declared choices
                    reducer fuel (extend scope.target domain.val) B' with
                | none => rw [firstRun, secondRun] at computed; cases computed
                | some second =>
                    rw [firstRun, secondRun] at computed
                    rw [kept firstRun, kept secondRun]
                    dsimp only at computed ⊢
                    cases levelRun : codomainUniverse choices first.val.level second.val.level with
                    | none => rw [levelRun] at computed; cases computed
                    | some level =>
                        rw [levelRun] at computed
                        dsimp only at computed ⊢
                        cases annotationRun : ContextualDependentPruning.formType facts roots heads algebra declared
                            choices reducer fuel (extend scope.target domain.val) (.head level.val) with
                        | none => rw [annotationRun] at computed; cases computed
                        | some annotation =>
                            rw [annotationRun] at computed
                            rw [kept annotationRun]
                            exact computed
      · rw [dif_neg universal] at computed
        cases computed
    · rw [dif_neg same] at computed
      cases computed
  · cases computed

omit stable in
/-- Only a Π left side is read by the Π decomposition. -/
theorem piDecomposeActive_of_not_pi (fuel : Nat) {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (active : Active scope.target) (notPi : ∀ A B, active.left.code ≠ .pi A B) :
    piDecomposeActive facts roots heads algebra declared choices reducer complete fuel scope active = none := by
  unfold piDecomposeActive
  split
  · rename_i A B A' B' u leftCode rightCode typeCode
    exact absurd leftCode (notPi _ _)
  · rfl

omit stable in
/-- A Σ decomposition reads a Σ left side. -/
theorem sigma_left_of_some {fuel : Nat} {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (active : Active scope.target) {found}
    (computed : sigmaDecomposeActive facts roots heads algebra declared choices reducer complete fuel scope active =
      some found) : ∀ A B, active.left.code ≠ .pi A B := by
  intro A B isPi
  unfold sigmaDecomposeActive at computed
  split at computed
  · rename_i A' B' A'' B'' u leftCode rightCode typeCode
    rw [isPi] at leftCode
    cases leftCode
  · cases computed

/-- **A binder decomposition found at one budget is kept.** -/
theorem binderDecomposeActive_mono {fuel larger : Nat} {Γ : Context S.R} {scopeType : TypeOver Γ}
    (scope : Spine scopeType) (active : Active scope.target) {found}
    (computed : binderDecomposeActive facts roots heads algebra declared choices reducer complete fuel scope active =
      some found) (enough : fuel ≤ larger) :
    binderDecomposeActive facts roots heads algebra declared choices reducer complete larger scope active =
      some found := by
  unfold binderDecomposeActive at computed ⊢
  cases piRun : piDecomposeActive facts roots heads algebra declared choices reducer complete fuel scope active with
  | some piFound =>
      rw [piRun] at computed
      rw [piDecomposeActive_mono facts roots heads algebra declared choices reducer complete stable scope active piRun
        enough]
      exact computed
  | none =>
      rw [piRun] at computed
      have sigmaRun : sigmaDecomposeActive facts roots heads algebra declared choices reducer complete fuel scope active =
          some found := computed
      rw [piDecomposeActive_of_not_pi facts roots heads algebra declared choices reducer complete larger scope active
        (sigma_left_of_some facts roots heads algebra declared choices reducer complete scope active sigmaRun)]
      exact sigmaDecomposeActive_mono facts roots heads algebra declared choices reducer complete stable scope active
        sigmaRun enough

theorem binderDecomposeActive_const {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (active : Active scope.target) :
    EventuallyConst fun fuel =>
      binderDecomposeActive facts roots heads algebra declared choices reducer complete fuel scope active :=
  EventuallyConst.of_mono fun computed enough =>
    binderDecomposeActive_mono facts roots heads algebra declared choices reducer complete stable scope active computed
      enough

/-- **The binder decomposition of one store equation is eventually constant.** -/
theorem piDecomposeEquation_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (rest : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      piDecomposeEquation facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        fuel equation rest := by
  obtain ⟨t₁, viewed⟩ := (viewEquation_const facts roots heads algebra declared choices reducer root stable
    equation).spec
  cases viewRun : viewEquation facts roots heads algebra declared choices reducer root t₁ equation with
  | none =>
      refine ⟨t₁, fun fuel enough => ?_⟩
      dsimp only
      unfold piDecomposeEquation
      erw [viewed fuel enough, viewRun]
  | some reading =>
      obtain ⟨scope, active, view⟩ := reading
      obtain ⟨t₂, decomposed⟩ := (binderDecomposeActive_const facts roots heads algebra declared choices reducer complete
        stable scope active).spec
      cases decomposeRun : binderDecomposeActive facts roots heads algebra declared choices reducer complete t₂ scope
          active with
      | none =>
          refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
          dsimp only
          unfold piDecomposeEquation
          erw [viewed fuel (le_of_max_le_left enough), viewRun, viewed _ (le_max_left _ _), viewRun]
          dsimp only
          erw [decomposed fuel (le_of_max_le_right enough), decomposeRun, decomposed _ (le_max_right _ _),
            decomposeRun]
      | some found =>
          obtain ⟨body, split⟩ := found
          cases closing : (scopeWith scope body).closeWith S.levels choices with
          | none =>
              refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
              dsimp only
              unfold piDecomposeEquation
              erw [viewed fuel (le_of_max_le_left enough), viewRun, viewed _ (le_max_left _ _), viewRun]
              dsimp only
              erw [decomposed fuel (le_of_max_le_right enough), decomposeRun, decomposed _ (le_max_right _ _),
                decomposeRun]
              dsimp only
              split
              · rfl
              · rename_i closed computed
                rw [computed] at closing
                cases closing
          | some closed₀ =>
              obtain ⟨t₃, localsSame⟩ := (localsRule_const facts roots heads algebra declared choices reducer root
                stable rigid complete (closed₀.equation :: rest)).spec
              obtain ⟨t₄, patternSame⟩ := (patternRule_const rigid facts complete roots heads algebra declared choices
                reducer root normalizes certifyNormal stable (closed₀.equation :: rest)).spec
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
              unfold piDecomposeEquation
              erw [viewed fuel e₁, viewRun, viewed _ f₁, viewRun]
              dsimp only
              erw [decomposed fuel e₂, decomposeRun, decomposed _ f₂, decomposeRun]
              dsimp only
              split
              · rfl
              · rename_i closed computed
                rw [computed] at closing
                cases closing
                erw [localsSame fuel e₃, localsSame _ f₃, patternSame fuel e₄, patternSame _ f₄]

/-- **The binder search through the store is eventually constant.** -/
theorem piDecomposeSearch_const {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), EventuallyConst fun fuel =>
      piDecomposeSearch facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        fuel problem
  | [] => EventuallyConst.const _
  | equation :: rest => by
      obtain ⟨t₁, first⟩ := (piDecomposeEquation_const facts roots heads algebra declared choices reducer rigid complete
        root normalizes certifyNormal stable equation rest).spec
      obtain ⟨t₂, later⟩ := (piDecomposeSearch_const rest).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      dsimp only
      simp only [piDecomposeSearch]
      erw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), later fuel (le_of_max_le_right enough),
        later _ (le_max_right _ _)]

omit stable in
/-- The Π round, read through its view. -/
theorem piRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (piRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem) =
      identityView (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem)
        (piDecomposeSearch facts roots heads algebra declared choices reducer rigid complete root normalizes
          certifyNormal fuel (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel
            problem).remaining)
        (roundView (identityRound facts roots heads algebra declared choices reducer rigid complete root normalizes
          certifyNormal headTypingUnique rootComplete fuel problem)) := by
  unfold piRound identityView
  split
  · rename_i update smaller computed
    simp only [computed, roundView, foundView, Option.map_some]
  · rename_i absent computed
    simp only [computed, roundView, foundView, Option.map_none]
  · rename_i computed
    first | rfl | simp only [computed, foundView]

/-- **The Π round is eventually constant on every store.** -/
theorem piRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      piRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => piRound_view facts roots heads algebra declared choices reducer rigid
    complete root normalizes certifyNormal headTypingUnique rootComplete fuel problem) ?_
  exact EventuallyConst.dep (h := fun fuel =>
      (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem,
        roundView (identityRound facts roots heads algebra declared choices reducer rigid complete root normalizes
          certifyNormal headTypingUnique rootComplete fuel problem)))
    (k := fun fuel pair => identityView pair.1 (piDecomposeSearch facts roots heads algebra declared choices reducer
      rigid complete root normalizes certifyNormal fuel pair.1.remaining) pair.2)
    (EventuallyConst.pair (prepare_const root rootComplete facts roots heads problem)
      (EventuallyConst.comp roundView (identityRound_const facts roots heads algebra declared choices reducer rigid
        complete root normalizes certifyNormal headTypingUnique rootComplete stable problem)))
    (fun pair => EventuallyConst.comp (fun found => identityView pair.1 found pair.2)
      (piDecomposeSearch_const facts roots heads algebra declared choices reducer rigid complete root normalizes
        certifyNormal stable pair.1.remaining))

/-- **The Π family settles** on every class of stores on which, at each nonempty store and from
some budget on, the Π round is not stuck and keeps every residual store in the class. -/
def piSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        piRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
            headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem} {smaller : Below (size update.remaining) (size problem)},
          piRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
              headTypingUnique rootComplete larger problem = .progress update smaller → holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (piFamily facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => piRound_const facts roots heads algebra declared choices reducer rigid complete
    root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end ContextualDependentFragment
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
