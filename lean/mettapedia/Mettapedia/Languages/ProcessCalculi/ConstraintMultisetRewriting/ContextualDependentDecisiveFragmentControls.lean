import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDecisiveFragmentKept
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDynamicFragmentControls

/-!
# A pattern store in the fragment, decided at one joint budget

Over `T : U0, F : (a b : T) → U0`, the crossed pattern `λ x y. F y x ≐ λ x y. Id T x y`:

* belongs to the dynamic pattern fragment, from its normal forms read by the actual normalizer;
* at budget 16 every executable on the pattern rule's path succeeds, so the pattern rule returns the
  same principal answer at every larger budget, and the distinct-locals rule never fires;
* the class `{crossed store, empty stores}` therefore satisfies the settling criterion, and the rigid
  solver decides the store at one joint budget, with the same outcome at every larger joint budget,
  and the outcome is a principal answer.

Every fact at budget 16 is evaluated by the kernel; every larger budget is covered by the kept-result
lemmas.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentDecisiveFragment.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentPatternSolver ContextualDependentDecisiveDriver
open ContextualDependentGeneralPattern ContextualDependentGeneralPattern.Controls ContextualDependentPatternSolver.Controls
open ContextualDependentNormalizing.Controls ContextualDependentDynamicFragment ContextualDependentDynamicFragment.Controls

theorem stable : ∀ {n : Nat} (fuel : Nat) (term : Tower.Tm n),
    ContextualDependentConversionBudget.Keeps (ContextualDependentInversion.Controls.reducer fuel term)
      (ContextualDependentInversion.Controls.reducer (fuel + 1) term) :=
  fun fuel term => ContextualDependentConversionBudget.normalizer_stable _ (fun _ => none) fuel term

/-- The rigid round of the tower controls, as a fuel-indexed family. -/
abbrev family :=
  rigidFamily (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique

/-- The pattern rule of the controls at one budget. -/
abbrev rule (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :=
  patternRule (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    DispatchControls.tower_normalizes DispatchControls.certifyNormal fuel problem

/-- The distinct-locals rule of the controls at one budget. -/
abbrev locals (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :=
  ContextualDependentRigidDecomposition.localsRule (S := setting) ContextualDependentPiSpine.Controls.rigid
    TowerModel.complete TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) fuel problem

/-- The scoped reading of the controls at one budget. -/
abbrev reading (fuel : Nat) {Θ : Context setting.R} (equation : Equation (TotalTerm Θ)) :=
  viewEquation (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) fuel equation

/-! ## The scoped reading of an equation, kept from budget 16 -/

/-- A reading found at budget 16 with every step finished is kept. -/
theorem reading_kept {Θ : Context setting.R} (equation : Equation (TotalTerm Θ))
    (compared : (ContextualDependentEta.Conversion.compareTypes (S := setting) TowerModel.facts TowerModel.roots
      TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.reducer 16 equation.2.1
      equation.1.1).isSome)
    (discovered : (ContextualDependentPiSpineDiscovery.discover (S := setting) TowerModel.facts TowerModel.roots
      TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
      ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16
      (lamDepth equation.1.2.code) equation.1.1).isSome)
    (leftFinished : (ContextualDependentNormalization.reduceTerm (S := setting) (fun _ => none) TowerModel.facts
      TowerModel.roots TowerModel.heads 16
      ⟨(Option.get _ discovered).result, (Option.get _ discovered).openFunction equation.1.2⟩).isSome)
    (rightFinished : (ContextualDependentNormalization.reduceTerm (S := setting) (fun _ => none) TowerModel.facts
      TowerModel.roots TowerModel.heads 16
      ⟨(Option.get _ discovered).result, (Option.get _ discovered).openFunction
        (equation.2.2.convertType equation.1.1 (Option.get _ compared).down)⟩).isSome) :
    ∀ larger, 16 ≤ larger → reading larger equation = reading 16 equation :=
  viewEquation_kept TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) stable equation (Option.get _ compared)
    (Option.some_get compared).symm (Option.some_get discovered).symm leftFinished rightFinished

/-! ## The distinct-locals rule never fires on the crossed store -/

theorem crossed_store_eq : crossedStore = [crossedEquation] :=
  singleton_of_length crossedStore crossed_store_length

theorem crossed_reading_kept : ∀ larger, 16 ≤ larger → reading larger crossedEquation = reading 16 crossedEquation :=
  reading_kept crossedEquation (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem crossed_locals_none : locals 16 crossedStore = none := by decide +kernel

theorem crossed_locals_kept : ∀ larger, 16 ≤ larger → locals larger crossedStore = none := by
  intro larger enough
  have kept := localsRule_singleton_kept ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none) crossedEquation
    crossed_reading_kept larger enough
  have atBudget := crossed_locals_none
  rw [crossed_store_eq] at atBudget ⊢
  exact kept.trans atBudget

/-! ## The pattern rule fires on it, kept from budget 16 -/

theorem newest_read : (ContextualDependentWorklist.newestOf (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 outer).isSome := by decide +kernel

/-- The newest declaration `F`, read at budget 16. -/
def newestView : Newest (S := setting) outer := Option.get _ newest_read

/-- The crossed store, over the newest view of its context. -/
def transported : EquationStore (TotalTerm (extend newestView.base newestView.type)) :=
  newestView.same ▸ crossedStore

theorem transported_length : transported.length = 1 := by decide +kernel

def transportedEquation : Equation (TotalTerm (extend newestView.base newestView.type)) :=
  transported.head (List.ne_nil_of_length_pos (by rw [transported_length]; decide))

theorem transported_eq : transported = [transportedEquation] :=
  singleton_of_length transported transported_length

theorem transported_reading_kept :
    ∀ larger, 16 ≤ larger → reading larger transportedEquation = reading 16 transportedEquation :=
  reading_kept transportedEquation (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem transported_viewed : (reading 16 transportedEquation).isSome := by decide +kernel

/-- The scoped reading of the transported equation at budget 16. -/
def transportedReading := Option.get _ transported_viewed

theorem applied_read : (readApplication transportedReading.2.1.left.code).isSome := by decide +kernel

/-- The head and arguments of the opened left side. -/
def applied := Option.get _ applied_read

theorem spine_found : (ContextualDependentPiSpineDiscovery.discover (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 applied.2.length
    newestView.type).isSome := by decide +kernel

/-- The spine of `F`'s type. -/
def patternSpine := Option.get _ spine_found

theorem recognized_found : (recognize patternSpine transportedReading.1 transportedReading.2.1).isSome := by
  decide +kernel

/-- The recognized pattern `F y x`. -/
def recognizedPattern := Option.get _ recognized_found

theorem recovered_found : (ContextualDependentTypedInversion.recover (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16
    recognizedPattern.pattern.bodyInclusion patternSpine.result recognizedPattern.right.code).isSome := by
  decide +kernel

/-- The orientation that fires, at budget 16. -/
abbrev active (fuel : Nat) :=
  tryActive (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer
    DispatchControls.tower_normalizes DispatchControls.certifyNormal fuel newestView.type
    transportedReading.1 transportedReading.2.1 transportedEquation transportedReading.2.2 []

theorem active_fires : (active 16).isSome := by decide +kernel

theorem active_kept : ∀ larger, 16 ≤ larger → active larger = active 16 :=
  tryActive_kept ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer
    DispatchControls.tower_normalizes DispatchControls.certifyNormal stable newestView.type transportedReading.1
    transportedReading.2.1 transportedEquation transportedReading.2.2 [] (Option.some_get applied_read).symm
    (Option.some_get spine_found).symm (Option.some_get recognized_found).symm (Option.some_get recovered_found).symm

theorem transported_search_kept :
    ∃ found, ∀ larger, 16 ≤ larger →
      searchStore (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
        TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
        ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
        DispatchControls.tower_normalizes DispatchControls.certifyNormal larger newestView.type transported =
          some found := by
  have equationKept := tryEquation_kept ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    DispatchControls.tower_normalizes DispatchControls.certifyNormal newestView.type transportedEquation []
    (Option.some_get transported_viewed).symm transported_reading_kept (Option.some_get active_fires).symm active_kept
  have searchKept := searchStore_singleton_kept ContextualDependentPiSpine.Controls.rigid TowerModel.facts
    TowerModel.complete TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
    DispatchControls.certifyNormal newestView.type transportedEquation equationKept
  have key : ∀ store, store = [transportedEquation] → ∃ found, ∀ larger, 16 ≤ larger →
      searchStore (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
        TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
        ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
        DispatchControls.tower_normalizes DispatchControls.certifyNormal larger newestView.type store = some found := by
    intro store same
    subst same
    exact ⟨_, searchKept⟩
  exact key transported transported_eq

/-- **The pattern rule on the crossed store is kept from budget 16.** -/
theorem crossed_rule_kept : ∀ larger, 16 ≤ larger → rule larger crossedStore = rule 16 crossedStore := by
  obtain ⟨found, searched⟩ := transported_search_kept
  exact patternRule_kept ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    DispatchControls.tower_normalizes DispatchControls.certifyNormal stable crossedStore
    (Option.some_get newest_read).symm (found := found) searched

theorem crossed_rule_fires : (rule 16 crossedStore).isSome := by decide +kernel

/-- At budget 16 the pattern rule solves the store and leaves nothing. -/
theorem crossed_rule_finishes :
    (match rule 16 crossedStore with
      | some (.solved update _) => update.remaining.isEmpty
      | _ => false) = true := by decide +kernel

/-! ## The class, the criterion, and decisiveness -/

/-- The crossed store, and every empty store. -/
def crossedClass {Γ : Context setting.R} (problem : EquationStore (TotalTerm Γ)) : Prop :=
  problem = [] ∨ (⟨Γ, problem⟩ : (Γ : Context setting.R) × EquationStore (TotalTerm Γ)) = ⟨outer, crossedStore⟩

/-- **The crossed class satisfies the settling criterion.** -/
def crossedSettled : Settled family :=
  settledWhereFiring (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    DispatchControls.tower_normalizes DispatchControls.certifyNormal stable
    ContextualDependentNormalCheckingTower.head_typing_unique (fun problem => crossedClass problem)
    (by
      intro Γ problem inside nonempty
      rcases inside with empty | same
      · exact absurd empty nonempty
      · cases same
        refine ⟨16, fun larger enough => .inr ⟨crossed_locals_kept larger enough, ?_, ?_⟩⟩
        · change (rule larger crossedStore).isSome
          rw [crossed_rule_kept larger enough]
          exact crossed_rule_fires
        · intro update smaller fired
          change rule larger crossedStore = _ at fired
          rw [crossed_rule_kept larger enough] at fired
          have finishes := crossed_rule_finishes
          rw [fired] at finishes
          exact .inl (List.isEmpty_iff.mp finishes))

/-- **The crossed store is in the dynamic pattern fragment.** -/
theorem crossed_in_fragment : InFragment crossedEquation := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have same : crossedEquation.2.1.code = crossedEquation.1.1.code := by decide +kernel
    rw [same]
    exact IsType.refl crossedEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact side_by_normalizer 64 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact side_by_normalizer 64 (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **Decisiveness at one joint budget** on the crossed store, a store of the dynamic pattern
fragment: from one budget on, used both for the executables and for the rounds, the rigid solver
reaches the same outcome, a principal answer or a certified refutation. -/
theorem crossed_decided :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (family.solver larger) crossedStore larger = run (family.solver budget) crossedStore budget ∧
      ((∃ state finished, run (family.solver larger) crossedStore larger = .solved state finished ∧
          (frames setting.levels).Principal crossedStore state.answer) ∨
        (∃ absent, run (family.solver larger) crossedStore larger = .refuted absent)) :=
  crossedSettled.decided (Or.inr rfl)

/-- The crossed store is solvable, so the decided outcome is the principal answer. -/
theorem crossed_solvable : (frames setting.levels).Solvable crossedStore := by
  obtain ⟨state, finished, solved⟩ := ContextualDependentWorklist.Controls.solved_of_commit crossed_solved
  have principal := drive_solved_principal full solved
  exact ⟨_, state.answer, principal.sound⟩

theorem crossed_decided_principal :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (family.solver larger) crossedStore larger = run (family.solver budget) crossedStore budget ∧
      ∃ state finished, run (family.solver larger) crossedStore larger = .solved state finished ∧
        (frames setting.levels).Principal crossedStore state.answer := by
  obtain ⟨budget, decided⟩ := crossed_decided
  refine ⟨budget, fun larger enough => ⟨(decided larger enough).1, ?_⟩⟩
  rcases (decided larger enough).2 with principal | ⟨absent, _⟩
  · exact principal
  · exact absurd crossed_solvable absent

end ContextualDependentDecisiveFragment.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
