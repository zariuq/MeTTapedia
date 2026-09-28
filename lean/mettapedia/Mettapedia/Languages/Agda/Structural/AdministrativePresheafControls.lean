import Mettapedia.Languages.Agda.Structural.AdministrativePresheaf
import Mettapedia.Languages.Agda.Structural.AdministrativeRegularityControls
import Mettapedia.Languages.Agda.Structural.PresentationCorrespondence

/-!
# Formed-world predicate and retained-event controls

The examples restrict a native typing predicate along a nontrivial typed
substitution, change a dependent annotation, and retain distinct computation
histories with identical endpoints. Raw contexts remain distinct after
admission even when a supported identity-image substitution relates them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Presheaf.Controls

open CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open scoped Mettapedia.GSLT.Topos.ConstructivePresheaf
open Mettapedia.GSLT.Topos.PresheafEventModalities

noncomputable def closedWorld : Base :=
  Opposite.op ⟨⟨⟨0, AdministrativeStatics.Controls.empty⟩,
    ⟨includeCanonical Statics.Derivation.empty⟩⟩⟩

noncomputable def openWorld : Base :=
  Opposite.op ⟨⟨⟨1, AdministrativeStatics.Controls.extended⟩,
    ⟨AdministrativeStatics.Controls.argumentImages.left.source⟩⟩⟩

noncomputable def replaceWithRedex : openWorld ⟶ closedWorld :=
  (show closedWorld.unop ⟶ openWorld.unop from
    ⟨Statics.single AdministrativeStatics.Controls.expanded,
      ⟨AdministrativeStatics.Controls.argumentImages.left⟩⟩).op

noncomputable def replaceWithContractum : openWorld ⟶ closedWorld :=
  (show closedWorld.unop ⟶ openWorld.unop from
    ⟨Statics.single AdministrativeStatics.Controls.contracted,
      ⟨AdministrativeStatics.Controls.argumentImages.right⟩⟩).op

theorem actual_variable_restriction :
    (terms .term).map replaceWithRedex (.var .zero) =
      AdministrativeStatics.Controls.expanded := rfl

theorem actual_typing_restriction :
    (AdministrativeStatics.Controls.domain.code, AdministrativeStatics.Controls.expanded) ∈
      typed.obj closedWorld :=
  typing_restrict replaceWithRedex
    ((Statics.universeType 1 1).code, .var .zero)
    ⟨AdministrativeStatics.Controls.newestTyped⟩

noncomputable def variableAnnotation : (terms .type).obj openWorld :=
  el (set (levelClosed 1)) (eliminate (.var .zero) nil)

theorem dependent_annotation_restricts :
    (terms .type).map replaceWithRedex variableAnnotation ∈ formed.obj closedWorld :=
  formation_restrict replaceWithRedex variableAnnotation
    ⟨AdministrativeStatics.Controls.administrativeFormation⟩

theorem equal_arguments_change_raw_annotations :
    (terms .type).map replaceWithRedex variableAnnotation ≠
      (terms .type).map replaceWithContractum variableAnnotation := by
  intro same
  cases same

/-- Two genuine compatible/root occurrences, with their full authored histories. -/
noncomputable def outerEvent : (events .term).obj closedWorld :=
  ⟨Structural.Controls.overlapSource, Structural.Controls.overlapTarget,
    stepToTree Structural.Controls.outerOccurrence⟩

noncomputable def innerEvent : (events .term).obj closedWorld :=
  ⟨Structural.Controls.overlapSource, Structural.Controls.overlapTarget,
    stepToTree Structural.Controls.innerOccurrence⟩

theorem event_histories_distinct : outerEvent ≠ innerEvent := by
  intro same
  have histories := congrArg
    (fun event => CompatibleDerivations.height (treeToStep event.history)) same
  change CompatibleDerivations.height
      (treeToStep (stepToTree Structural.Controls.outerOccurrence)) =
    CompatibleDerivations.height
      (treeToStep (stepToTree Structural.Controls.innerOccurrence)) at histories
  rw [treeToStep_stepToTree, treeToStep_stepToTree] at histories
  cases histories

theorem event_endpoints_equal :
    (computation .term).source.app closedWorld outerEvent =
        (computation .term).source.app closedWorld innerEvent ∧
      (computation .term).target.app closedWorld outerEvent =
        (computation .term).target.app closedWorld innerEvent := ⟨rfl, rfl⟩

theorem may_observation_retains_a_real_event :
    Structural.Controls.overlapSource ∈
      (diamond (computation .term) (⊤ : Subfunctor (terms .term))).obj closedWorld :=
  ⟨outerEvent, trivial, rfl⟩

noncomputable def convertedLeftWorld : Base := Opposite.op ⟨RegularityControls.admittedLeft⟩
noncomputable def convertedRightWorld : Base := Opposite.op ⟨RegularityControls.admittedRight⟩

theorem converted_worlds_remain_distinct : convertedLeftWorld ≠ convertedRightWorld := by
  intro same
  have contexts := congrArg (fun world : Base => world.unop.val) same
  exact RegularityControls.admitted_contexts_remain_distinct contexts

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Presheaf.Controls
