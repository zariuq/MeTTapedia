import Mettapedia.Languages.ProcessCalculi.PiCalculus.EquationAdequacy

/-!
# Equation-respecting observations of the authored pi fragment

The generated modalities are characterized by the independent occurrence
reduction and the actual static equation relation. Diamond looks forward;
the OSLF right-adjoint box looks universally over predecessors. An atomic
grammar test on the supplied syntax is not equation invariant, because a
singleton bag may wrap a channel or a message. Testing the canonical normal
form instead gives a native predicate of the declared monoid quotient.

These results concern `piCalc` with its declared bag laws. They do not add
the larger restriction and unfolding equations or assert that arbitrary
equation representatives remain in the syntactic atomic grammar.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.BagNormalForm
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-- Reflection through static saturation retains the supplied final endpoint. -/
theorem pi_semantic_step_iff_raw (source target : Pattern) :
    StepModuloEquations (engineBasePremises RelationEnv.empty) piCalc source target ↔
      ∃ redex contractum,
        EquationEquiv (engineBasePremises RelationEnv.empty) piCalc source redex ∧
        PiRawStep redex contractum ∧
        EquationEquiv (engineBasePremises RelationEnv.empty) piCalc contractum target := by
  constructor
  · rintro ⟨redex, contractum, before, firing, after⟩
    exact ⟨redex, contractum, before, piRawStep_of_step firing, after⟩
  · rintro ⟨redex, contractum, before, firing, after⟩
    exact ⟨redex, contractum, before, step_of_piRawStep firing, after⟩

/-- A semantic observation can be tested on the actual rule contractum. -/
theorem pi_native_diamond_iff_raw
    (property : EquationPredicate (langGSLT piCalc)) (source : Pattern) :
    piCalcDiamond property source ↔
      ∃ redex contractum,
        EquationEquiv (engineBasePremises RelationEnv.empty) piCalc source redex ∧
        PiRawStep redex contractum ∧ property contractum := by
  change gsltDiamond (langGSLT piCalc) property.1 source ↔ _
  erw [gsltDiamond_spec]
  constructor
  · rintro ⟨target, ⟨redex, contractum, before, firing, after⟩, holds⟩
    exact ⟨redex, contractum, before, piRawStep_of_step firing, (property.2 after).mpr holds⟩
  · rintro ⟨redex, contractum, before, firing, holds⟩
    exact ⟨contractum, ⟨redex, contractum, before, step_of_piRawStep firing, .refl _⟩, holds⟩

/-- The native right adjoint quantifies over incoming firings, not future states. -/
theorem pi_native_box_iff_raw
    (property : EquationPredicate (langGSLT piCalc)) (target : Pattern) :
    piCalcBox property target ↔
      ∀ redex contractum, PiRawStep redex contractum →
        EquationEquiv (engineBasePremises RelationEnv.empty) piCalc contractum target →
        property redex := by
  change gsltBox (langGSLT piCalc) property.1 target ↔ _
  erw [gsltBox_spec]
  constructor
  · intro holds redex contractum firing after
    exact holds redex ⟨redex, contractum, .refl _, step_of_piRawStep firing, after⟩
  · intro holds source ⟨redex, contractum, before, firing, after⟩
    exact (property.2 before).mpr (holds redex contractum (piRawStep_of_step firing) after)

/-- Canonical atomic membership is an observation of the actual static quotient. -/
def atomicNativeType (depth : Nat) : EquationPredicate (langGSLT piCalc) :=
  ⟨fun process => AtomicPi depth (normalForm (some "PiNil") process), by
    intro left right equivalent
    have same := normalForm_eq_of_equationEquiv piBagTheory equivalent
    simp only [same]⟩

theorem named_has_atomic_native_type (process : Process) :
    atomicNativeType 0 (piToPattern process) := (piToPattern_atomic process).normalForm

theorem atomic_step_admissible {depth : Nat} {source target : Pattern}
    (atomic : AtomicPi depth source)
    (firing : Step (engineBasePremises RelationEnv.empty) piCalc source target) :
    Admissible piCalc piNameContext (List.replicate depth (.base "Proc")) (.base "Proc") target := by
  have result := atomic_step_preservation atomic firing
  exact ⟨result.hasType, result.canonical, result.object⟩

theorem atomic_enabled_native_diamond {depth : Nat} {source target : Pattern}
    (atomic : AtomicPi depth source)
    (firing : Step (engineBasePremises RelationEnv.empty) piCalc source target) :
    piCalcDiamond (atomicNativeType depth) source := by
  apply (pi_native_diamond_iff_raw _ _).mpr
  exact ⟨source, target, .refl _, piRawStep_of_step firing,
    (atomic_step_preservation atomic firing).normalForm⟩

private theorem collection_not_atomic_name (depth : Nat) (elements : List Pattern) :
    ¬ AtomicName depth (.collection .hashBag elements none) := by
  intro atomic
  cases atomic

/-- A sorted monoid equation may leave the atomic syntax grammar inside a message. -/
theorem atomic_grammar_not_equation_invariant :
    ¬ EquationInvariant (langGSLT piCalc) (AtomicPi 0) := by
  intro invariant
  let before : Pattern := .apply "PiOut" [.fvar "a", .fvar "b"]
  let after : Pattern := .apply "PiOut" [.fvar "a", .collection .hashBag [.fvar "b"] none]
  have same : EquationEquiv (engineBasePremises RelationEnv.empty) piCalc before after := by
    have singleton : EquationEquiv (engineBasePremises RelationEnv.empty) piCalc
        (.collection .hashBag [.fvar "b"] none) (.fvar "b") := derivedInstance_equivalent
      (DerivedInstance.singleton piBagTheory.bagAlgebraRule rfl
        ⟨piNameContext, [], bag_hasType piBagTheory (.cons (.fvar rfl) (.nil _ _))⟩)
    exact equationEquiv_fill (.apply "PiOut" [.fvar "a"] .hole []) (.symm _ _ singleton)
  have first : AtomicPi 0 before := .output (.free 0 "a") (.free 0 "b")
  have escaped : AtomicPi 0 after := (invariant same).mp first
  generalize shape : after = process at escaped
  cases escaped <;> simp [after] at shape
  case output subject payload =>
    rcases shape with ⟨rfl, rfl⟩
    exact collection_not_atomic_name 0 _ payload

end Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
