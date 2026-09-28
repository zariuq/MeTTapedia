import Mettapedia.Languages.Agda.Structural.AdministrativeDependentFunctionObjects
import Mettapedia.Languages.Agda.Structural.AdministrativeDependentFunctionControls
import Mettapedia.Languages.Agda.Structural.AdministrativeLocalFunctionControls

/-!
# Native dependent sections retain their actual argument and local annotations

The dependent function is a variable in a formed context, not a claimed closed
inhabitant of `(X : Set 1) → X`. Its two applications inhabit the two actual
argument-indexed fibres. A second control uses an ambient free type variable.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Presheaf.DependentObjectControls

open CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

noncomputable def dependentFrame : FunctionBase :=
  ⟨DependentControls.functionWorld, Statics.universeType 1 1, .bind ⟨1,.var .zero⟩⟩

noncomputable def dependentFunction : localFunctions.obj dependentFrame :=
  ⟨.var .zero, ⟨DependentControls.functionVariableTyping⟩⟩

noncomputable def firstArgument : localArguments.obj dependentFrame :=
  ⟨DependentControls.firstArgument, ⟨DependentControls.firstArgumentTyping⟩⟩

noncomputable def secondArgument : localArguments.obj dependentFrame :=
  ⟨DependentControls.secondArgument, ⟨DependentControls.secondArgumentTyping⟩⟩

noncomputable def firstValue :=
  (nativeApplicationSections.app dependentFrame dependentFunction).app dependentFrame
    (𝟙 dependentFrame) firstArgument

noncomputable def secondValue :=
  (nativeApplicationSections.app dependentFrame dependentFunction).app dependentFrame
    (𝟙 dependentFrame) secondArgument

theorem first_value_at_its_own_fibre :
    Nonempty (CoreDerivation (Statics.typed DependentControls.functionContext firstValue.val
      (el (set (levelClosed 1)) DependentControls.firstArgument))) := firstValue.property

theorem second_value_at_its_own_fibre :
    Nonempty (CoreDerivation (Statics.typed DependentControls.functionContext secondValue.val
      (el (set (levelClosed 1)) DependentControls.secondArgument))) := secondValue.property

theorem results_retain_raw_arguments : firstValue.val ≠ secondValue.val := by
  intro same
  cases same

theorem result_fibre_annotations_differ :
    (dependentFrame.2.2.instantiate firstArgument.val).code ≠
      (dependentFrame.2.2.instantiate secondArgument.val).code :=
  DependentControls.dependent_result_annotations_differ

noncomputable def localIdentity : localFunctions.obj LocalControls.inhabitedFrame :=
  ⟨lam (.var .zero), ⟨LocalControls.identityTyped LocalControls.openParameter.weaken
    (CoreDerivation.typingFormation LocalControls.localVariableTyping)⟩⟩

noncomputable def localArgument : localArguments.obj LocalControls.inhabitedFrame :=
  ⟨.var .zero, ⟨LocalControls.localVariableTyping⟩⟩

noncomputable def localValue :=
  (nativeApplicationSections.app LocalControls.inhabitedFrame localIdentity).app
    LocalControls.inhabitedFrame (𝟙 LocalControls.inhabitedFrame) localArgument

theorem open_result_has_local_type :
    Nonempty (CoreDerivation (Statics.typed LocalControls.inhabitedContext localValue.val
      LocalControls.openParameter.weaken.code)) := localValue.property

theorem open_result_keeps_application :
    localValue.val = Statics.app (n := 2) (lam (.var .zero)) (.var .zero) := rfl

theorem local_annotations_do_not_become_global :
    ¬ ∃ value : TypeSection,
      value.app Controls.openWorld PUnit.unit = LocalControls.openParameter.code :=
  LocalControls.openParameter_cannot_be_global

#print axioms second_value_at_its_own_fibre
#print axioms open_result_has_local_type

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Presheaf.DependentObjectControls
