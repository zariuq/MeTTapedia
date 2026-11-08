import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentInPlace
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentWorklistPi

/-!
# The in-place round is eventually constant

Strengthening keeps its results: type formation and checked recovery keep theirs, and the
inversion of codes reads no budget. So strengthening, separation, the in-place rule at every depth,
its search through the depths and the **in-place round** give the same result at every large
enough budget, on every store, with no normality, typing or fragment condition. The in-place
family therefore settles on every class where, from some budget on, its round is not stuck and
keeps its residual stores in the class (`inPlaceSettledOfConst`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentInPlace

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentConversionBudget

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

/-- **A strengthening found at one budget is kept.** -/
theorem strengthen_mono {fuel larger : Nat} {Γ : Context S.R} {type : TypeOver Γ} {term : TotalTerm (extend Γ type)}
    {result : {strong : TotalTerm Γ // rename wk strong.1.code = term.1.code ∧ rename wk strong.2.code = term.2.code}}
    (computed : strengthen facts roots heads algebra declared choices reducer fuel type term = some result)
    (enough : fuel ≤ larger) :
    strengthen facts roots heads algebra declared choices reducer larger type term = some result := by
  unfold strengthen at computed ⊢
  obtain ⟨code, coded, rest⟩ := Option.bind_eq_some_iff.mp computed
  obtain ⟨formed, formedRun, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨recovered, recoveredRun, returned⟩ := Option.map_eq_some_iff.mp rest
  exact Option.bind_eq_some_iff.mpr ⟨code, coded, Option.bind_eq_some_iff.mpr ⟨formed,
    ContextualDependentRecoveryBudget.formType_mono facts roots heads algebra declared choices reducer stable formedRun
      enough,
    Option.map_eq_some_iff.mpr ⟨recovered,
      ContextualDependentRecoveryBudget.recover_mono facts roots heads algebra declared choices reducer stable
        recoveredRun enough, returned⟩⟩⟩

/-- **Strengthening is eventually constant.** -/
theorem strengthen_const {Γ : Context S.R} (type : TypeOver Γ) (term : TotalTerm (extend Γ type)) :
    EventuallyConst fun fuel => strengthen facts roots heads algebra declared choices reducer fuel type term :=
  EventuallyConst.of_mono fun computed enough =>
    strengthen_mono facts roots heads algebra declared choices reducer stable computed enough

/-- **Separation is eventually constant on every store.** -/
theorem separate_const {Γ : Context S.R} (type : TypeOver Γ) :
    ∀ problem : EquationStore (TotalTerm (extend Γ type)),
      EventuallyConst fun fuel => separate facts roots heads algebra declared choices reducer fuel type problem
  | [] => EventuallyConst.const _
  | equation :: rest => by
      obtain ⟨t₁, s₁⟩ := (strengthen_const facts roots heads algebra declared choices reducer stable type equation.1).spec
      obtain ⟨t₂, s₂⟩ := (strengthen_const facts roots heads algebra declared choices reducer stable type equation.2).spec
      obtain ⟨t₃, s₃⟩ := (separate_const type rest).spec
      refine ⟨max t₁ (max t₂ t₃), fun fuel enough => ?_⟩
      have e₁ : t₁ ≤ fuel := by omega
      have e₂ : t₂ ≤ fuel := by omega
      have e₃ : t₃ ≤ fuel := by omega
      have f₁ : t₁ ≤ max t₁ (max t₂ t₃) := by omega
      have f₂ : t₂ ≤ max t₁ (max t₂ t₃) := by omega
      have f₃ : t₃ ≤ max t₁ (max t₂ t₃) := by omega
      dsimp only
      simp only [separate]
      erw [s₁ fuel e₁, s₁ _ f₁, s₂ fuel e₂, s₂ _ f₂, s₃ fuel e₃, s₃ _ f₃]

/-- Separation with its equivalence is eventually constant. -/
theorem separation_const {Γ : Context S.R} (type : TypeOver Γ) (problem : EquationStore (TotalTerm (extend Γ type))) :
    EventuallyConst fun fuel => separation facts roots heads algebra declared choices reducer fuel type problem :=
  EventuallyConst.of_injective (g := Subtype.val) Subtype.val_injective
    (separate_const facts roots heads algebra declared choices reducer stable type problem)

/-- **The in-place rule at every depth is eventually constant on every store.** -/
theorem inPlaceAt_const : ∀ (depth : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)),
    EventuallyConst fun fuel =>
      inPlaceAt facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique fuel depth problem
  | 0, _, problem => firstRule_const rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal headTypingUnique stable problem
  | depth + 1, Θ, problem => by
      obtain ⟨t₁, viewed⟩ := (newestOf_const facts roots heads algebra declared choices reducer stable Θ).spec
      cases viewRun : newestOf facts roots heads algebra declared choices reducer t₁ Θ with
      | none =>
          refine ⟨t₁, fun fuel enough => ?_⟩
          dsimp only
          simp only [inPlaceAt]
          erw [viewed fuel enough, viewRun]
      | some view =>
          obtain ⟨t₂, solved⟩ := (ContextualDependentDecisiveFragment.throughNewest_const view problem
            (fun fuel stored =>
              (inPlaceAt facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
                headTypingUnique fuel depth
                (separation facts roots heads algebra declared choices reducer fuel view.type stored).val.1).map
                (carry view.type (separation facts roots heads algebra declared choices reducer fuel view.type
                  stored).property))
            (fun stored => EventuallyConst.dep
              (h := fun fuel => separation facts roots heads algebra declared choices reducer fuel view.type stored)
              (k := fun fuel separated =>
                (inPlaceAt facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
                  headTypingUnique fuel depth separated.val.1).map (carry view.type separated.property))
              (separation_const facts roots heads algebra declared choices reducer stable view.type stored)
              (fun separated => EventuallyConst.comp (Option.map (carry view.type separated.property))
                (inPlaceAt_const depth separated.val.1)))).spec
          refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
          dsimp only
          simp only [inPlaceAt]
          erw [viewed fuel (le_of_max_le_left enough), viewRun, viewed _ (le_max_left _ _), viewRun]
          exact (solved fuel (le_of_max_le_right enough)).trans (solved _ (le_max_right _ _)).symm

/-- The search through the depths is eventually constant. -/
theorem inPlaceSearch_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    ∀ depths : List Nat, EventuallyConst fun fuel =>
      inPlaceSearch facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique fuel problem depths
  | [] => EventuallyConst.const _
  | depth :: rest => by
      obtain ⟨t₁, first⟩ := (inPlaceAt_const facts roots heads algebra declared choices reducer rigid complete root
        normalizes certifyNormal headTypingUnique stable depth problem).spec
      obtain ⟨t₂, later⟩ := (inPlaceSearch_const problem rest).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      dsimp only
      simp only [inPlaceSearch]
      erw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), later fuel (le_of_max_le_right enough),
        later _ (le_max_right _ _)]

/-- **The in-place rule is eventually constant on every store.** -/
theorem inPlaceRule_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      inPlaceRule facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique fuel problem :=
  inPlaceSearch_const facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
    headTypingUnique stable problem _

omit stable in
/-- The in-place round, read through its view. -/
theorem inPlaceRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (inPlaceRound facts roots heads algebra declared choices reducer rigid complete root normalizes
        certifyNormal headTypingUnique rootComplete fuel problem) =
      (roundView (piRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
          headTypingUnique rootComplete fuel problem)).or
        ((foundView (inPlaceRule facts roots heads algebra declared choices reducer rigid complete root normalizes
          certifyNormal headTypingUnique fuel
          (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining)).map
          (Option.map fun update =>
            (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).then update)) := by
  unfold inPlaceRound
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

/-- **The in-place round is eventually constant on every store.** -/
theorem inPlaceRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      inPlaceRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => inPlaceRound_view facts roots heads algebra declared choices reducer rigid
    complete root normalizes certifyNormal headTypingUnique rootComplete fuel problem) ?_
  exact EventuallyConst.dep (h := fun fuel =>
      (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem,
        roundView (piRound facts roots heads algebra declared choices reducer rigid complete root normalizes
          certifyNormal headTypingUnique rootComplete fuel problem)))
    (k := fun fuel pair => pair.2.or
      ((foundView (inPlaceRule facts roots heads algebra declared choices reducer rigid complete root normalizes
        certifyNormal headTypingUnique fuel pair.1.remaining)).map (Option.map fun update => pair.1.then update)))
    (EventuallyConst.pair (prepare_const root rootComplete facts roots heads problem)
      (EventuallyConst.comp roundView (piRound_const facts roots heads algebra declared choices reducer rigid complete
        root normalizes certifyNormal headTypingUnique rootComplete stable problem)))
    (fun pair => EventuallyConst.comp (fun found => pair.2.or ((foundView found).map
        (Option.map fun update => pair.1.then update)))
      (inPlaceRule_const facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique stable pair.1.remaining))

/-- **The in-place family settles** on every class of stores on which, at each nonempty store and
from some budget on, the in-place round is not stuck and keeps every residual store in the class. -/
def inPlaceSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        inPlaceRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
            headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem} {smaller : Below (size update.remaining) (size problem)},
          inPlaceRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
              headTypingUnique rootComplete larger problem = .progress update smaller → holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (inPlaceFamily facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => inPlaceRound_const facts roots heads algebra declared choices reducer rigid complete
    root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end ContextualDependentInPlace
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
