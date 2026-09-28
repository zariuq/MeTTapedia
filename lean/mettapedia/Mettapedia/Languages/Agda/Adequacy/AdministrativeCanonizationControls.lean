import Mettapedia.Languages.Agda.Adequacy.AdministrativeComponentTransportControls
import Mettapedia.Languages.Agda.Adequacy.AdministrativeCanonization
import Mettapedia.Languages.Agda.Adequacy.AdministrativeComponentTransport

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.Canonization.Controls

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Structural
open Structural.Statics (RawTm RawTy RawContext TypeParameter TypeBody)
open Structural.AdministrativeStatics
open BinderPreservationControls

noncomputable def convertedBinder : CoreDerivation
    (Statics.termEqual empty (lam (eliminate (.var .zero) nil)) (lam (.var .zero)) expandedFunction) :=
  (typing convertedBindingSource).at (term := .lam (.bind (.var 0))) rfl

noncomputable def nonbindingBinder : CoreDerivation
    (Statics.termEqual one (lamNoAbs (eliminate (.var .zero) nil)) (lamNoAbs (.var .zero))
      (Statics.piType secondDomain secondCodomain).code) :=
  (typing nonbindingSource).at (term := .lam (.noBind (.var 0))) rfl

theorem nonbinding_readback_keeps_older_variable :
    (Statics.TermBody.noBind (embedTerm (.var 0 : StaticSpecification.Term 1))).open =
      (.var (.succ .zero) : RawTm 2) := rfl

theorem nonbinding_readback_does_not_capture :
    (Statics.TermBody.noBind (embedTerm (.var 0 : StaticSpecification.Term 1))).open ≠
      (.var .zero : RawTm 2) := nonbinding_open_does_not_capture

noncomputable def dependentPi : CoreDerivation
    (Statics.termEqual empty (dependentFamily.pi adminDomain) (dependentFamily.pi domain)
      (Statics.universeType 0 2).code) :=
  (typing dependentPiSource).at (term := .pi (.universe 1) (.bind (.el 1 (.var 0)) )) rfl

noncomputable def dependentAnnotation : CoreDerivation
    (Statics.typeEqual ComponentTransport.Controls.nativeContext ComponentTransport.Controls.nativeDependent
      ComponentTransport.Controls.canonicalDependent) :=
  (formation ComponentTransport.Controls.dependentCanonization.typeEndpoints.left).at
    ComponentTransport.Controls.dependent_observation

noncomputable def returnedContext : ComponentTransport.IdentityReturn ComponentTransport.Controls.sourceContext
    ComponentTransport.Controls.nativeContext :=
  (context adminContextFormed).returnAt ComponentTransport.Controls.context_observation

theorem returned_context_changes_raw_annotations :
    ComponentTransport.Controls.nativeContext ≠ embedContext ComponentTransport.Controls.sourceContext :=
  ComponentTransport.Controls.contexts_are_raw_distinct

theorem dependent_readback_changes_raw_annotation :
    ComponentTransport.Controls.nativeDependent ≠ embedTy ComponentTransport.Controls.sourceDependent :=
  ComponentTransport.Controls.readback_keeps_no_administrative_wrapper

abbrev twoArgumentReadback : RawTm 1 :=
  Statics.app (Statics.app (.var .zero) (Statics.universeTerm 0)) (Statics.universeTerm 0)

noncomputable def convertedAppend : CoreDerivation
    (Statics.termEqual SpineStatics.Controls.functionContext
      (eliminate (.var .zero) (append SpineStatics.Controls.firstSpine SpineStatics.Controls.secondSpine))
      twoArgumentReadback PreservationControls.expandedUniverse) :=
  (action PreservationControls.convertedAppendSource).at
    (spine := [.apply (.sort 0), .apply (.sort 0)]) rfl
    (termReflexivity (includePrior SpineStatics.Controls.functionTyped))

noncomputable def convertedNested : CoreDerivation
    (Statics.termEqual SpineStatics.Controls.functionContext
      (eliminate (eliminate (.var .zero) SpineStatics.Controls.firstSpine) SpineStatics.Controls.secondSpine)
      twoArgumentReadback PreservationControls.expandedUniverse) :=
  (typing PreservationControls.convertedNestedSource).at
    (term := (StaticSpecification.Term.var 0).app (.sort 0) |>.app (.sort 0)) rfl

theorem append_canonization_changes_raw_syntax :
    eliminate (.var .zero) (append SpineStatics.Controls.firstSpine SpineStatics.Controls.secondSpine) ≠
      twoArgumentReadback := by
  intro same
  cases same

abbrev dependentContext : RawContext 1 :=
  empty.snoc (Statics.piType domain RegularityControls.family).code

noncomputable def dependentContextFormed : CoreDerivation (Statics.context dependentContext) :=
  administrativeOperations.extend (includeCanonical Statics.Derivation.empty) RegularityControls.inputFormed

abbrev localFamily : TypeBody 1 := .bind ⟨1, .var .zero⟩
abbrev localDomain : TypeParameter 1 := Statics.universeType 1 1
abbrev localArgument : RawTm 1 := eliminate (Statics.universeTerm 0) nil

noncomputable def dependentHead : CoreDerivation
    (Statics.typed dependentContext (.var .zero) (Statics.piType localDomain localFamily).code) :=
  Derivation.core (.variable dependentContext .zero)
    (consEvidence CoreDerivation dependentContextFormed (noEvidence CoreDerivation))

noncomputable def dependentArgument : CoreDerivation (Statics.typed dependentContext localArgument localDomain.code) :=
  Derivation.elimination
    (Derivation.core (.sort dependentContext 0)
      (consEvidence CoreDerivation dependentContextFormed (noEvidence CoreDerivation)))
    (Derivation.nil dependentContext _)

noncomputable def dependentAction : Action dependentContext (Statics.piType localDomain localFamily).code
    (cons (apply localArgument) nil) (localFamily.instantiate localArgument).code :=
  Derivation.cons dependentArgument (Derivation.nil dependentContext _)

noncomputable def dependentApplication : CoreDerivation
    (Statics.termEqual dependentContext (Statics.app (.var .zero) localArgument)
      (Statics.app (.var .zero) (Statics.universeTerm 0)) (localFamily.instantiate localArgument).code) :=
  (typing (Derivation.elimination dependentHead dependentAction)).at
    (term := (StaticSpecification.Term.var 0).app (.sort 0)) rfl

theorem dependent_output_keeps_original_raw_argument :
    (localFamily.instantiate localArgument).code ≠ (localFamily.instantiate (Statics.universeTerm 0)).code := by
  intro same
  cases same

noncomputable def malformedAction : ActionResult Structural.AdministrativeStatics.Controls.empty
    Structural.AdministrativeStatics.Controls.unsupportedType nil
    Structural.AdministrativeStatics.Controls.unsupportedType :=
  action (Derivation.nil _ _)

theorem malformed_action_is_observed : Observation.spine (nil : Spine (scope 0)) = some [] :=
  malformedAction.observed

theorem malformed_action_does_not_supply_formation :
    ¬ Nonempty (CoreDerivation (Statics.formed Structural.AdministrativeStatics.Controls.empty
      Structural.AdministrativeStatics.Controls.unsupportedType)) :=
  Structural.AdministrativeStatics.Controls.unsupported_type_unformed

theorem malformed_action_cannot_supply_head_typing (t : RawTm 0)
    (tree : CoreDerivation (Statics.typed Structural.AdministrativeStatics.Controls.empty t
      Structural.AdministrativeStatics.Controls.unsupportedType)) : False :=
  malformed_action_does_not_supply_formation ⟨tree.typingFormation⟩

noncomputable def directHistory := includePrior SpineStatics.Controls.directElimination
noncomputable def convertedHistory := includePrior SpineStatics.Controls.convertedElimination

theorem input_histories_remain_distinct : directHistory ≠ convertedHistory := by
  intro same
  exact SpineStatics.Controls.elimination_history_retained (includePrior_injective same)

theorem distinct_histories_have_same_observation :
    (typing directHistory).value = (typing convertedHistory).value :=
  Option.some.inj ((typing directHistory).observed.symm.trans (typing convertedHistory).observed)

end Mettapedia.Languages.Agda.StaticAdequacy.Canonization.Controls
