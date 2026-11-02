import Mettapedia.Languages.ProcessCalculi.PiCalculus.EquationAdequacy

/-!
# Equation-respecting observations of the authored pi fragment

The generated modalities are characterized by the independent occurrence
reduction and the actual static equation relation. Diamond looks forward;
the OSLF right-adjoint box looks universally over predecessors. An atomic
grammar test on the supplied syntax is not equation invariant, because a
singleton bag may wrap a channel or a message. Having an atomic representative
is a native predicate of `piCalc`'s static quotient, restriction laws included
(`atomicNativeType`). In the parallel fragment, testing the bag normal form
decides it (`parallelAtomicType`).
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

/-- **Having an atomic representative** is an observation of `piCalc`'s static quotient. -/
def atomicNativeType (depth : Nat) : EquationPredicate (langGSLT piCalc) :=
  ⟨fun process => ∃ representative,
      EquationEquiv (engineBasePremises RelationEnv.empty) piCalc process representative ∧
        AtomicPi depth representative, by
    intro left right equivalent
    constructor
    · rintro ⟨representative, related, atomic⟩
      exact ⟨representative, .trans _ _ _ (.symm _ _ equivalent) related, atomic⟩
    · rintro ⟨representative, related, atomic⟩
      exact ⟨representative, .trans _ _ _ equivalent related, atomic⟩⟩

theorem named_has_atomic_native_type (process : Process) :
    atomicNativeType 0 (piToPattern process) := ⟨_, .refl _, piToPattern_atomic process⟩

/-- **In the parallel fragment, the bag normal form decides atomicity**: an observation of the fragment's
quotient. -/
def parallelAtomicType (depth : Nat) : EquationPredicate (langGSLT piParallelFragment) :=
  ⟨fun process => AtomicPi depth (normalForm (some "PiNil") process), by
    intro left right equivalent
    have same := normalForm_eq_of_equationEquiv piParallelBagTheory equivalent
    simp only [same]⟩

/-- A fragment step is a step of `piCalc`: the fragment keeps every rule. -/
theorem step_of_parallel_step {source target : Pattern}
    (step : Step (engineBasePremises RelationEnv.empty) piParallelFragment source target) :
    Step (engineBasePremises RelationEnv.empty) piCalc source target :=
  Step.mono_rules (lang₁ := piParallelFragment) (lang₂ := piCalc) (fun _ member => member) step

theorem parallel_step_of_step {source target : Pattern}
    (step : Step (engineBasePremises RelationEnv.empty) piCalc source target) :
    Step (engineBasePremises RelationEnv.empty) piParallelFragment source target :=
  Step.mono_rules (lang₁ := piCalc) (lang₂ := piParallelFragment) (fun _ member => member) step

/-- The fragment's native right adjoint quantifies over incoming firings. -/
theorem parallel_native_box_iff_raw
    (property : EquationPredicate (langGSLT piParallelFragment)) (target : Pattern) :
    langBox piParallelFragment property target ↔
      ∀ redex contractum, PiRawStep redex contractum →
        EquationEquiv (engineBasePremises RelationEnv.empty) piParallelFragment contractum target →
        property redex := by
  change gsltBox (langGSLT piParallelFragment) property.1 target ↔ _
  erw [gsltBox_spec]
  constructor
  · intro holds redex contractum firing after
    exact holds redex ⟨redex, contractum, .refl _, parallel_step_of_step (step_of_piRawStep firing), after⟩
  · intro holds source ⟨redex, contractum, before, firing, after⟩
    exact (property.2 before).mpr
      (holds redex contractum (piRawStep_of_step (step_of_parallel_step firing)) after)

theorem atomic_step_admissible {depth : Nat} {source target : Pattern}
    (atomic : AtomicPi depth source)
    (firing : Step (engineBasePremises RelationEnv.empty) piCalc source target) :
    Admissible piCalc piNameContext (List.replicate depth (.base "Name")) (.base "Proc") target := by
  have result := atomic_step_preservation atomic firing
  exact ⟨result.hasType, result.canonical, result.object⟩

theorem atomic_enabled_native_diamond {depth : Nat} {source target : Pattern}
    (atomic : AtomicPi depth source)
    (firing : Step (engineBasePremises RelationEnv.empty) piCalc source target) :
    piCalcDiamond (atomicNativeType depth) source := by
  apply (pi_native_diamond_iff_raw _ _).mpr
  exact ⟨source, target, .refl _, piRawStep_of_step firing,
    ⟨target, .refl _, atomic_step_preservation atomic firing⟩⟩

private theorem collection_not_atomic_name (depth : Nat) (elements : List Pattern) :
    ¬ AtomicName depth (.collection .hashBag elements none) := by
  intro atomic
  cases atomic

/-- The untyped static theory may leave the atomic syntax grammar inside a message: a one-member bag around a name
is a process in a context where the name is one. In π's sorted reading a name is no process, and the bag is no
name. -/
theorem atomic_grammar_not_equation_invariant :
    ¬ EquationInvariant (langGSLT piCalc) (AtomicPi 0) := by
  intro invariant
  let before : Pattern := .apply "PiOut" [.fvar "a", .fvar "b"]
  let after : Pattern := .apply "PiOut" [.fvar "a", .collection .hashBag [.fvar "b"] none]
  have same : EquationEquiv (engineBasePremises RelationEnv.empty) piCalc before after := by
    have singleton : EquationEquiv (engineBasePremises RelationEnv.empty) piCalc
        (.collection .hashBag [.fvar "b"] none) (.fvar "b") := derivedInstance_equivalent
      (DerivedInstance.singleton piBagPresentation.bagAlgebraRule rfl
        ⟨fun _ => some (.base "Proc"), [], bag_hasType (piBagPresentation.asBare rfl) (.cons (.fvar rfl) (.nil _ _))⟩)
    exact equationEquiv_fill (.apply "PiOut" [.fvar "a"] .hole []) (.symm _ _ singleton)
  have first : AtomicPi 0 before := .output (.free 0 "a") (.free 0 "b")
  have escaped : AtomicPi 0 after := (invariant same).mp first
  generalize shape : after = process at escaped
  cases escaped <;> simp [after] at shape
  case output subject payload =>
    rcases shape with ⟨rfl, rfl⟩
    exact collection_not_atomic_name 0 _ payload

end Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
