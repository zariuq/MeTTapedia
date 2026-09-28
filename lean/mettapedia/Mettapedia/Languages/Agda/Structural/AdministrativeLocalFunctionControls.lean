import Mettapedia.Languages.Agda.Structural.AdministrativeLocalFunctionPredicates
import Mettapedia.Languages.Agda.Structural.AdministrativePresheafControls
import Mettapedia.Languages.Agda.Structural.AdministrativeFunctionControls

/-!
# Local dependent families with free type variables

A type referring to an ambient variable has different images along two
actual typed substitutions, so it cannot be supplied by a global section.
The category-of-elements construction accepts it. Extending its context by
an inhabitant gives an actual typed identity application at that local type.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Presheaf.LocalControls

open CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open scoped Mettapedia.GSLT.Topos.ConstructivePresheaf

def openParameter : Statics.TypeParameter 1 := ⟨1, eliminate (.var .zero) nil⟩

noncomputable def openFrame : FunctionBase :=
  ⟨Controls.openWorld, openParameter, .noBind openParameter⟩

theorem openParameter_cannot_be_global :
    ¬ ∃ value : TypeSection,
      value.app Controls.openWorld PUnit.unit = openParameter.code := by
  rintro ⟨value, chosen⟩
  have first := congrArg (fun h : one.obj Controls.openWorld ⟶ (terms .type).obj Controls.closedWorld =>
    h PUnit.unit) (value.naturality Controls.replaceWithRedex)
  have second := congrArg (fun h : one.obj Controls.openWorld ⟶ (terms .type).obj Controls.closedWorld =>
    h PUnit.unit) (value.naturality Controls.replaceWithContractum)
  have same := first.symm.trans second
  change (terms .type).map Controls.replaceWithRedex (value.app Controls.openWorld PUnit.unit) =
    (terms .type).map Controls.replaceWithContractum (value.app Controls.openWorld PUnit.unit) at same
  rw [chosen] at same
  exact Controls.equal_arguments_change_raw_annotations same

/-- The same native identity construction works for any actually formed local domain. -/
noncomputable def identityTyped {n : Nat} {Γ : Statics.RawContext n} (A : Statics.TypeParameter n)
    (domain : CoreDerivation (Statics.formed Γ A.code)) :
    CoreDerivation (Statics.typed Γ (lam (.var .zero)) (Statics.piType A (.noBind A)).code) := by
  let extended := administrativeOperations.extend (Derivation.contextRegularity domain) domain
  let codomain := administrativeOperations.weakenFormation domain domain
  let body := Derivation.core (.variable (Γ.snoc A.code) .zero)
    (consEvidence CoreDerivation extended (noEvidence CoreDerivation))
  have openCode : (Statics.TypeBody.noBind A).open.code = weaken A.code :=
    Telescope.bind_projection A.code
  refine Derivation.core (.lambda Γ A (.noBind A) (.bind (.var .zero)))
    (consEvidence CoreDerivation domain (consEvidence CoreDerivation ?_
      (consEvidence CoreDerivation ?_ (noEvidence CoreDerivation))))
  · rw [openCode]
    exact codomain
  · change CoreDerivation (Statics.typed (Γ.snoc A.code) (.var .zero)
      (Statics.TypeBody.noBind A).open.code)
    rw [openCode]
    exact body

theorem genuinely_local_identity_internal :
    localApplicationFunction.app openFrame (lam (.var .zero)) ∈
      (dependentFunctionPredicate localArguments localResults).obj openFrame :=
  local_typed_function_internal openFrame
    ⟨identityTyped openParameter AdministrativeStatics.Controls.administrativeFormation⟩

noncomputable def restrictFrame {X : FunctionBase} {Y : Base} (substitution : X.1 ⟶ Y) :
    X ⟶ (⟨Y, functionParameters.map substitution X.2⟩ : FunctionBase) :=
  CategoryOfElements.homMk _ _ substitution rfl

theorem free_parameter_changes_with_substitution :
    functionParameters.map Controls.replaceWithRedex openFrame.2 ≠
      functionParameters.map Controls.replaceWithContractum openFrame.2 := by
  intro same
  have codes := congrArg
    (fun pair : functionParameters.obj Controls.closedWorld => pair.1.code) same
  exact Controls.equal_arguments_change_raw_annotations codes

theorem substituted_local_identity_internal :
    localApplicationFunction.app
        (⟨Controls.closedWorld, functionParameters.map Controls.replaceWithRedex openFrame.2⟩ : FunctionBase)
        (lam (.var .zero)) ∈
      (dependentFunctionPredicate localArguments localResults).obj
        ⟨Controls.closedWorld, functionParameters.map Controls.replaceWithRedex openFrame.2⟩ :=
  (dependentFunctionPredicate localArguments localResults).map
    (restrictFrame (X := openFrame) Controls.replaceWithRedex) genuinely_local_identity_internal

def inhabitedContext : Statics.RawContext 2 :=
  AdministrativeStatics.Controls.extended.snoc openParameter.code

noncomputable def inhabitedContextFormation : CoreDerivation (Statics.context inhabitedContext) :=
  administrativeOperations.extend
    (Derivation.contextRegularity AdministrativeStatics.Controls.administrativeFormation)
    AdministrativeStatics.Controls.administrativeFormation

noncomputable def inhabitedWorld : Base :=
  Opposite.op ⟨⟨⟨2, inhabitedContext⟩, ⟨inhabitedContextFormation⟩⟩⟩

noncomputable def inhabitedFrame : FunctionBase :=
  ⟨inhabitedWorld, openParameter.weaken, .noBind openParameter.weaken⟩

noncomputable def localVariableTyping : CoreDerivation
    (Statics.typed inhabitedContext (.var .zero) openParameter.weaken.code) :=
  Derivation.core (.variable inhabitedContext .zero)
    (consEvidence CoreDerivation inhabitedContextFormation (noEvidence CoreDerivation))

/-- The type family contains an actual value at the open annotation. -/
noncomputable def localInhabitant :
    inhabitantsByType.obj ⟨inhabitedWorld, openParameter.weaken.code⟩ :=
  ⟨.var .zero, ⟨localVariableTyping⟩⟩

theorem actual_local_identity_application :
    Nonempty (CoreDerivation (Statics.typed inhabitedContext
      (Statics.app (n := 2) (lam (.var .zero)) (.var .zero)) openParameter.weaken.code)) := by
  have formation := CoreDerivation.typingFormation localVariableTyping
  exact local_typed_function_application (𝟙 inhabitedFrame)
    (lam (.var .zero)) (.var .zero)
    ⟨identityTyped openParameter.weaken formation⟩ ⟨localVariableTyping⟩

/-- A malformed annotation cannot acquire an inhabitant through the family construction. -/
theorem unsupported_local_family_empty (X : Base) :
    IsEmpty (inhabitantsByType.obj
      ⟨X, (FunctionControls.unsupportedAnnotation.app X PUnit.unit)⟩) := by
  refine ⟨?_⟩
  intro value
  exact FunctionControls.unsupported_members_empty X value.val value.property

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Presheaf.LocalControls
