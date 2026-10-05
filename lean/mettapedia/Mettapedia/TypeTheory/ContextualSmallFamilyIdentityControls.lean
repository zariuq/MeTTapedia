import Mettapedia.TypeTheory.ContextualSmallFamilyIdentity
import Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormerControls

/-!
# Discrete J retaining complete future functions

The motive returns a whole contextual dependent function, whose future
results vary at infinitely many newly available arguments. Reflexivity J
retains that function and its future values over arbitrary bare-hyperset
parameters. An independently raised natural motive tests the larger-motive
universe of J without raising the material identity witness bound.

Two functions agree on every present argument and differ in their complete
future values. Their discrete material identity carrier is empty. A
noninjective parameter change retains both endpoints, their witness and
the parameter coordinate forgotten by the change.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyIdentityControls

open CategoryTheory ContextualWitnessCover
open ContextualSmallFamilyTypeFormers ContextualSmallFamilyIdentity
open ContextualSmallFamilyTypeFormerControls ContextualSmallFamilyUniverseControls
open MaterialSets.Hypersets

abbrev functionDomain := pi cyclicSmall positionResults

def functionReceipt : (identityContext functionDomain).obj 0 :=
  (diagonal functionDomain).app 0 ⟨HSet.quineAtom, greatestSection.val (parameter 0 HSet.quineAtom)⟩

def functionPoint : (identityContext functionDomain).Elements := ⟨0, functionReceipt⟩

theorem J_preserves_whole_function :
    (J functionDomain (endpointMotive functionDomain) (endpointMethod functionDomain)).val functionPoint =
      greatestSection.val (parameter 0 HSet.quineAtom) := J_endpoint_value functionDomain functionPoint

theorem J_preserves_infinitely_growing_future_results (stage : Nat) :
    (((J functionDomain (endpointMotive functionDomain) (endpointMethod functionDomain)).val functionPoint).val
      (laterArgument stage)).val = stage + 1 := by
  rw [J_preserves_whole_function]
  exact greatest_future_value stage

def raisedMotive : (identityContext functionDomain).Elements ⥤ Type 1 where
  obj point := ULift.{1} ((endpointMotive functionDomain).obj point)
  map step := TypeCat.ofHom fun term => ⟨(endpointMotive functionDomain).map step term.down⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro term
    exact congrArg ULift.up ((endpointMotive functionDomain).map_id_apply point term.down)
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro term
    exact congrArg ULift.up ((endpointMotive functionDomain).map_comp_apply earlier later term.down)

def raisedMethod : (reindex raisedMotive (diagonal functionDomain)).sections :=
  ⟨fun point => ⟨point.2.2⟩, by
    intro first second step
    exact congrArg ULift.up ((lastVariable functionDomain).property step)⟩

theorem larger_motive_computation :
    reindexSection (diagonal functionDomain) raisedMotive (J functionDomain raisedMotive raisedMethod) =
      raisedMethod := J_beta functionDomain raisedMotive raisedMethod

theorem larger_motive_preserves_future_result (stage : Nat) :
    (((J functionDomain raisedMotive raisedMethod).val functionPoint).down.val (laterArgument stage)).val = stage + 1 := by
  have value : (J functionDomain raisedMotive raisedMethod).val functionPoint =
      ⟨greatestSection.val (parameter 0 HSet.quineAtom)⟩ :=
    eq_of_heq (J_value_heq functionDomain raisedMotive raisedMethod functionPoint)
  rw [value]
  exact greatest_future_value stage

theorem same_present_applications_empty_discrete_identity :
    (∀ argument : cyclicSmall.obj (parameter 0 HSet.quineAtom),
      evaluateValue cyclicSmall positionResults (parameter 0 HSet.quineAtom)
        (greatestSection.val (parameter 0 HSet.quineAtom)) argument =
      evaluateValue cyclicSmall positionResults (parameter 0 HSet.quineAtom)
        (zeroSection.val (parameter 0 HSet.quineAtom)) argument) ∧
      ¬ Nonempty ((identityFamily functionDomain greatestSection zeroSection).obj (parameter 0 HSet.quineAtom)) :=
  ⟨same_present_all_arguments HSet.quineAtom,
    PresheafIdentityWitness.witness_empty_of_distinct different_whole_future_functions⟩

theorem full_function_identity_graph_empty :
    HSet.mk (PresheafIdentityWitness.graph
      (greatestSection.val (parameter 0 HSet.quineAtom))
      (zeroSection.val (parameter 0 HSet.quineAtom))) = ∅ :=
  PresheafIdentityWitness.graph_empty_of_distinct different_whole_future_functions

theorem reflexive_function_identity_material_singleton :
    HSet.mk (PresheafIdentityWitness.graph (greatestSection.val (parameter 0 HSet.quineAtom))
      (greatestSection.val (parameter 0 HSet.quineAtom))) = {∅} :=
  PresheafIdentityWitness.graph_reflexive _

def changedReceipt (saved : HSet.{0}) : (identityContext (reindex functionDomain selectFirst)).obj 0 :=
  (diagonal (reindex functionDomain selectFirst)).app 0
    ⟨(HSet.quineAtom, saved), greatestSection.val (parameter 0 HSet.quineAtom)⟩

def changedPoint (saved : HSet.{0}) : (identityContext (reindex functionDomain selectFirst)).Elements :=
  ⟨0, changedReceipt saved⟩

theorem changed_receipts_retain_saved_parameter : changedReceipt ∅ ≠ changedReceipt HSet.quineAtom := by
  intro same
  exact HSet.empty_ne_quineAtom
    (congrArg (fun receipt : (identityContext (reindex functionDomain selectFirst)).obj 0 => receipt.1.1.1.2) same)

theorem actual_parameter_map_forgets_saved_coordinate :
    (identityReindex selectFirst functionDomain).app 0 (changedReceipt ∅) =
      (identityReindex selectFirst functionDomain).app 0 (changedReceipt HSet.quineAtom) := rfl

theorem substituted_J_preserves_selected_whole_function (saved : HSet.{0}) :
    (J (reindex functionDomain selectFirst)
      (reindex (endpointMotive functionDomain) (identityReindex selectFirst functionDomain))
      (reindexMethod selectFirst functionDomain (endpointMotive functionDomain) (endpointMethod functionDomain))).val
        (changedPoint saved) = greatestSection.val (parameter 0 HSet.quineAtom) := by
  have square := congrArg (fun term :
    (reindex (endpointMotive functionDomain) (identityReindex selectFirst functionDomain)).sections =>
      term.val (changedPoint saved))
    (J_substitution selectFirst functionDomain (endpointMotive functionDomain) (endpointMethod functionDomain))
  exact square.symm.trans J_preserves_whole_function

theorem independently_formed_identity_code_decodes :
    ContextualSmallFamilyUniverse.decodedFamily
      (ContextualSmallFamilyUniverse.classifier (identityFamily functionDomain greatestSection greatestSection)) =
        identityFamily functionDomain greatestSection greatestSection :=
  identity_decoder functionDomain greatestSection greatestSection

end Mettapedia.TypeTheory.ContextualSmallFamilyIdentityControls
