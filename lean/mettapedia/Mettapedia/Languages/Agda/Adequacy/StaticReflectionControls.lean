import Mettapedia.Languages.Agda.Adequacy.StaticReflection
import Mettapedia.Languages.Agda.Structural.StaticRegularityControls
import Mettapedia.Languages.Agda.StaticSpecification.Examples

/-!
# Controls for reflection of actual native derivations

The positive inputs below are structural derivations constructed without using
the source-to-presentation translator. They include dependent substitution,
context conversion and the derived comparison of binding and nonbinding
lambdas. Source refusals transfer in the opposite direction through reflection.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.Reflection.Controls

open Structural.Statics
open Structural.Statics.RegularityControls

noncomputable def betaInSource : StaticSpecification.TermEq .nil
    (StaticSpecification.Examples.closedIdentity.app (.sort 0)) (.sort 0)
    (StaticSpecification.Ty.universe 1) :=
  (interpret betaEquality .nil rfl).at rfl rfl rfl

noncomputable def dependentResultsInSource : StaticSpecification.TypeEq .nil
    (.el 1 (StaticSpecification.Examples.closedIdentity.app (.sort 0))) (.el 1 (.sort 0)) :=
  (interpret equalDependentResults .nil rfl).at rfl rfl

noncomputable def mixedAbstractionsInSource : StaticSpecification.TermEq .nil
    (.lam (.bind (.sort 0))) (.lam (.noBind (.sort 0)))
    (StaticSpecification.Ty.pi (StaticSpecification.Ty.universe 1)
      (.noBind (StaticSpecification.Ty.universe 1))) :=
  (interpret bindingAndNonbindingEqual .nil rfl).at rfl rfl rfl

noncomputable def convertedVariableInSource : StaticSpecification.Typing
    (.snoc .nil (.el 1 (.sort 0))) (.var 0)
    (.el 1 ((StaticSpecification.Examples.closedIdentity.app (.sort 0)).weaken)) :=
  (interpret variableAfterContextConversion _ rfl).at rfl rfl

noncomputable def twoDeclarationTyping :
    ReflectedTyping (rightContext.snoc dependentMember) (.var (.succ .zero))
      (Structural.ContextGeometry.lookup (leftContext.snoc dependentMember) (.succ .zero)) :=
  reflectTyping olderVariableAfterConversion

theorem wrong_universe_rejected {n : Nat} (Γ : StaticSpecification.RawContext n) :
    ¬ Nonempty (Derivation (typed (embedContext Γ) (embedTerm (.sort 0))
      (embedTy (StaticSpecification.Ty.universe 0)))) := by
  rintro ⟨tree⟩
  exact StaticSpecification.Examples.wrong_universe_rejected ⟨typingBack tree⟩

theorem malformed_telescope_rejected :
    ¬ Nonempty (Derivation (context (embedContext StaticSpecification.Examples.malformedTelescope))) := by
  rintro ⟨tree⟩
  exact StaticSpecification.Examples.malformed_telescope_rejected ⟨contextBack tree⟩

theorem unsupported_term_rejected {n : Nat} (Γ : RawContext n) (t : RawTm n) (A : RawTy n)
    (unsupported : Observation.term t = none) : ¬ Nonempty (Derivation (typed Γ t A)) := by
  rintro ⟨tree⟩
  have observed := (reflectTyping tree).typing.observed
  rw [unsupported] at observed
  cases observed

theorem unsupported_beneath_binder_rejected {n : Nat} (Γ : RawContext n) (A : RawTy n) :
    ¬ Nonempty (Derivation (typed Γ (Structural.lam (Structural.natLiteral 7)) A)) :=
  unsupported_term_rejected Γ _ A rfl

theorem different_annotations_rejected {n : Nat} (Γ : StaticSpecification.RawContext n) :
    ¬ Nonempty (Derivation (typeEqual (embedContext Γ)
      (embedTy (StaticSpecification.Ty.universe 0)) (embedTy (StaticSpecification.Ty.universe 1)))) := by
  rintro ⟨tree⟩
  exact StaticSpecification.Examples.distinct_universes_not_convertible ⟨typeEqualityBack tree⟩

end Mettapedia.Languages.Agda.StaticAdequacy.Reflection.Controls
