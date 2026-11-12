import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.SettlingStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentSchemaArguments

/-!
# The comprehension read through the schema opening

A firing's helper telescope extends the state's frame `Γ` to `helpers.frame`. The dependent schema
package proves that a substitution into the extended frame is exactly an old-context substitution
together with a tuple of typed arguments for the helpers
(`Interface.DependentFull.Helpers.openingEquiv`, from `extensionEquiv`). Read through it:

* **The comprehension** of a firing's information is the set of old-context substitutions and
  typed arguments whose instantiation solves it (`mem_solutions_iff_arguments`).
* **Typed after the match** is typed along every such instantiation
  (`typedAfterMatch_iff_arguments`). A pattern's arguments are what the match supplies, and the
  rule is checked against all of them, nonprincipal families included.
* **A principal answer is a refined context with an argument tuple** (`answer_arguments`): its
  opening is the base substitution `σ ≫ weaken` and the argument values; settling along it is
  settling along their instantiation (`settled_along_arguments`).

So the schema opening supplies the context the match refines, and settling is the step it does not
take: typing the made rows in that refined context.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep

open _root_.CategoryTheory Opposite Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull (Make Helpers)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L)

/-- **The comprehension, read through the opening**: a substitution into the helper frame solves the
information exactly when the instantiation of its base substitution and arguments does. -/
theorem mem_solutions_iff_arguments {Γ Θ : Context rules} (helpers : Helpers Γ)
    (I : EquationStore (TotalTerm helpers.frame)) (τ : Θ ⟶ helpers.frame) :
    τ ∈ (solutions levels I).obj (op Θ) ↔
      (frames levels).Models (helpers.instantiate (helpers.openingEquiv Θ τ).1
        (helpers.openingEquiv Θ τ).2) I := by
  rw [helpers.instantiate_opening]
  exact Iff.rfl

/-- **Typed after the match, read through the opening**: typed along the instantiation of every
base substitution and typed argument tuple that solves the information. -/
theorem typedAfterMatch_iff_arguments {Γ : Context rules} (helpers : Helpers Γ)
    (I : EquationStore (TotalTerm helpers.frame)) (m : Make helpers.frame) :
    TypedAfterMatch levels I m ↔
      ∀ (Δ : Context rules) (baseMap : Δ ⟶ Γ) (args : helpers.Arguments baseMap),
        (frames levels).Models (helpers.instantiate baseMap args) I →
          (m.reindex (helpers.instantiate baseMap args)).WellTyped := by
  rw [typedAfterMatch_iff]
  exact Helpers.entails_iff_arguments levels helpers I (fun _ τ => (m.reindex τ).WellTyped)

/-- **A principal answer is a refined context with an argument tuple**: its opening is the base
substitution through the weakening, and the answer is the instantiation of its opening. -/
theorem answer_arguments {Γ M : Context rules} (helpers : Helpers Γ) (σ : M ⟶ helpers.frame) :
    (helpers.openingEquiv M σ).1 = σ ≫ helpers.weaken ∧
      helpers.instantiate (helpers.openingEquiv M σ).1 (helpers.openingEquiv M σ).2 = σ :=
  ⟨helpers.opening_base σ, helpers.instantiate_opening σ⟩

omit [UniverseLevel.LevelOrder L] in
/-- **Settling along an answer is settling along its arguments.** -/
theorem settled_along_arguments {Γ M : Context rules} (helpers : Helpers Γ) (σ : M ⟶ helpers.frame)
    (m : Make helpers.frame) :
    m.reindex (helpers.instantiate (helpers.openingEquiv M σ).1 (helpers.openingEquiv M σ).2) =
      m.reindex σ := by
  rw [helpers.instantiate_opening]

end NativeTypesOnTheStep

#print axioms NativeTypesOnTheStep.mem_solutions_iff_arguments
#print axioms NativeTypesOnTheStep.typedAfterMatch_iff_arguments
#print axioms NativeTypesOnTheStep.answer_arguments
#print axioms NativeTypesOnTheStep.settled_along_arguments

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
