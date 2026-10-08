import Mettapedia.Logic.HMLBudgetedEquivalence
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Types.Basic

/-!
# Actual modal observation classes and dependent resource restriction

The quotient identifies states precisely when all declared affordable tests
have equal actual answers and spending. Its complete readout is injective;
an arbitrary consumer factors through it exactly when it respects this
earned execution equivalence.

Increasing resources refines the equivalence and yields a presheaf of
classes. Dependent families on observable classes pull back coherently.
No arbitrary hidden-state family is asserted to descend, and no selected
representative or new runtime state is manufactured.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ModalMuCalculus.StackInspection.BudgetObservation

open Inspection Funded _root_.CategoryTheory _root_.Opposite

universe u v w

variable {State : Type u} {Action : Type v} {n : Nat}

def observationSetoid (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (budget : Nat) : Setoid State where
  r := Agree presentation environment budget
  iseqv := ⟨agreement_refl presentation environment budget,
    agreement_symm presentation environment budget,
    agreement_trans presentation environment budget⟩

abbrev ObservationClass (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (budget : Nat) :=
  Quotient (observationSetoid presentation environment budget)

def classifyState (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (budget : Nat) (state : State) :
    ObservationClass presentation environment budget := Quotient.mk _ state

theorem class_equality_iff (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (budget : Nat) (first second : State) :
    classifyState presentation environment budget first =
      classifyState presentation environment budget second ↔
        Agree presentation environment budget first second := Quotient.eq

def classProfile (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (budget : Nat) :
    ObservationClass presentation environment budget → Question Action n → Option Bool × Nat :=
  Quotient.lift (fun state question => observation presentation environment budget question state)
    (fun _ _ same => funext same)

theorem class_profile_injective (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (budget : Nat) :
    Function.Injective (classProfile presentation environment budget) := by
  intro first second
  induction first using Quotient.inductionOn
  induction second using Quotient.inductionOn
  intro same
  exact Quotient.sound (fun question => congrFun same question)

def descend {Value : Type w} (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (budget : Nat) (readout : State → Value)
    (invariant : ∀ first second, Agree presentation environment budget first second →
      readout first = readout second) : ObservationClass presentation environment budget → Value :=
  Quotient.lift readout invariant

theorem consumer_universal {Value : Type w} (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (budget : Nat) (readout : State → Value) :
    (∃! consumer : ObservationClass presentation environment budget → Value,
      ∀ state, consumer (classifyState presentation environment budget state) = readout state) ↔
        ∀ first second, Agree presentation environment budget first second →
          readout first = readout second := by
  constructor
  · rintro ⟨consumer, correct, _⟩ first second same
    exact (correct first).symm.trans
      ((congrArg consumer (Quotient.sound same)).trans (correct second))
  · intro invariant
    refine ⟨descend presentation environment budget readout invariant, fun _ => rfl, ?_⟩
    intro other correct
    funext code
    induction code using Quotient.inductionOn
    exact correct _

def restrictClass (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) {small large : Nat} (included : small ≤ large) :
    ObservationClass presentation environment large → ObservationClass presentation environment small :=
  Quotient.lift (classifyState presentation environment small)
    (fun _ _ same => Quotient.sound (agreement_restriction presentation environment included same))

theorem restrictClass_identity (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (budget : Nat)
    (code : ObservationClass presentation environment budget) :
    restrictClass presentation environment (le_refl budget) code = code := by
  induction code using Quotient.inductionOn
  rfl

theorem restrictClass_composition (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) {small middle large : Nat}
    (first : small ≤ middle) (second : middle ≤ large)
    (code : ObservationClass presentation environment large) :
    restrictClass presentation environment first (restrictClass presentation environment second code) =
      restrictClass presentation environment (first.trans second) code := by
  induction code using Quotient.inductionOn
  rfl

def observationClasses (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) : Natᵒᵖ ⥤ Type u where
  obj budget := ObservationClass presentation environment budget.unop
  map change := TypeCat.ofHom (restrictClass presentation environment (leOfHom change.unop))
  map_id budget := by
    apply ConcreteCategory.hom_ext
    intro code
    exact restrictClass_identity presentation environment budget.unop code
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro code
    exact (restrictClass_composition presentation environment
      (leOfHom second.unop) (leOfHom first.unop) code).symm

def stateClassifications (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) :
    (Functor.const Natᵒᵖ).obj State ⟶ observationClasses presentation environment where
  app budget := TypeCat.ofHom (classifyState presentation environment budget.unop)
  naturality first second change := by
    apply ConcreteCategory.hom_ext
    intro state
    rfl

def pullClassFamily (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) {small large : Nat} (included : small ≤ large)
    (family : ObservationClass presentation environment small → Type w) :
    ObservationClass presentation environment large → Type w :=
  fun code => family (restrictClass presentation environment included code)

theorem pullClassFamily_identity (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) (budget : Nat)
    (family : ObservationClass presentation environment budget → Type w) :
    pullClassFamily presentation environment (le_refl budget) family = family := by
  funext code
  exact congrArg family (restrictClass_identity presentation environment budget code)

theorem pullClassFamily_composition (presentation : SuccessorPresentation State Action)
    (environment : BooleanEnv State n) {small middle large : Nat}
    (first : small ≤ middle) (second : middle ≤ large)
    (family : ObservationClass presentation environment small → Type w) :
    pullClassFamily presentation environment second
      (pullClassFamily presentation environment first family) =
        pullClassFamily presentation environment (first.trans second) family := by
  funext code
  exact congrArg family (restrictClass_composition presentation environment first second code)

end Mettapedia.Logic.ModalMuCalculus.StackInspection.BudgetObservation
