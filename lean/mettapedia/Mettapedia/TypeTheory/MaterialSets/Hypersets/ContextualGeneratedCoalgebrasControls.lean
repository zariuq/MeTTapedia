import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedCoalgebras
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualPowerFamiliesControls
import Mettapedia.TypeTheory.MaterialSets.Hypersets.UniverseSizeObstructions

/-!
# Infinite material controls for small contextual generation

The argument functor is the actual member family of the infinite observed
material model. Its fibres inhabit the successor universe. The original
constructed fibre decoders enumerate the complete future-child predicate
at the smaller graph bound. Generated paths retain parallel context
histories and distinct context-versus-child receipts with equal endpoints.

A separate constant ambient hyperset coalgebra has a small generated
carrier at each root but cannot supply a small carrier for the whole
ambient universe.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedCoalgebrasControls

open _root_.CategoryTheory
open ContextualGeneratedUniverse
open PowerClassPresheafBaseChange
open ContextualPowerFamiliesControls
open Mettapedia.TypeTheory.ContextualWitnessCover
open Mettapedia.GSLT.ObservedGeneratedModel
open Mettapedia.GSLT.ObservedGeneratedModelControls.Paths

abbrev wide := domain.members

def positiveMember (point : actualContext.base.Elements) : wide.obj point :=
  (domain.model point).decode.symm (positiveSection.val point)

theorem positiveMember_value (point : actualContext.base.Elements) :
    (positiveMember point).val = (domain.model point).value (positiveSection.val point) := rfl

theorem positiveMember_restriction {first second : actualContext.base.Elements} (step : first ⟶ second) :
    wide.map step (positiveMember first) = positiveMember second :=
  (domain.memberRestriction_encode step (positiveSection.val first)).trans
    (congrArg (domain.model second).decode.symm (positiveSection.property step))

/-- Every actual future member is admitted. The truth subtype is large,
while the independently constructed decoder supplies a small cover. -/
def allChildren (point : actualContext.base.Elements) : CoveredFuturePowerFamilies.Predicate wide point where
  holds _ := True
  closed _ _ := trivial

def allEnumeration (point : actualContext.base.Elements) : CoveredFuturePowerFamilies.Enumeration (allChildren point) where
  Carrier future := domain.family.obj future.1 × Bool
  value future code := (domain.model future.1).decode.symm code.1
  covered future argument := ⟨fun _ => ⟨((domain.model future.1).decode argument, false),
    (domain.model future.1).decode.symm_apply_apply argument⟩, fun _ => trivial⟩

def allCoalgebra : NaturalHom wide (CoveredFuturePowerFamilies.family wide) where
  app point _ := ⟨allChildren point, ⟨allEnumeration point⟩⟩
  naturality _ _ := by
    apply Subtype.ext
    apply CoveredFuturePowerFamilies.Predicate.ext
    intro _
    exact Iff.rfl

def branchEnumerations (point : actualContext.base.Elements) (argument : wide.obj point) :
    CoveredFuturePowerFamilies.Enumeration (allCoalgebra.app point argument).val := allEnumeration point

def seed : ContextualGeneratedCoalgebras.State wide := ⟨initialPoint, positiveMember initialPoint⟩

abbrev generated := ContextualGeneratedCoalgebras.family wide allCoalgebra branchEnumerations seed
abbrev readout := ContextualGeneratedCoalgebras.endpoint wide allCoalgebra branchEnumerations seed
abbrev system := ContextualGeneratedCoalgebras.pathSystem wide allCoalgebra branchEnumerations

def rootPath : ContextualGeneratedCoalgebras.PathNode wide allCoalgebra branchEnumerations seed :=
  LocallyPresentedCoalgebras.rootNode system seed

def rootReceipt : generated.obj initialPoint :=
  ContextualGeneratedCoalgebras.rootMember wide allCoalgebra branchEnumerations seed

theorem root_material_value : (readout.app initialPoint rootReceipt).val = ∅ :=
  (congrArg Subtype.val (ContextualGeneratedCoalgebras.endpoint_root
    wide allCoalgebra branchEnumerations seed)).trans old_section_value

def newCyclicReceipt : generated.obj (observedPoint model worldCoding futureRaw) :=
  ContextualGeneratedCoalgebras.childReceipt wide allCoalgebra branchEnumerations seed rootPath
    ⟨observedPoint model worldCoding futureRaw, futureArrow⟩ (futureArgument, false)

theorem new_cyclic_material_value :
    (readout.app (observedPoint model worldCoding futureRaw) newCyclicReceipt).val = HSet.quineAtom :=
  (congrArg Subtype.val (ContextualGeneratedCoalgebras.endpoint_childReceipt
    wide allCoalgebra branchEnumerations seed rootPath
      ⟨observedPoint model worldCoding futureRaw, futureArrow⟩ (futureArgument, false))).trans futureArgument_value

theorem actual_generated_family_varies :
    (readout.app initialPoint rootReceipt).val ≠
      (readout.app (observedPoint model worldCoding futureRaw) newCyclicReceipt).val := by
  rw [root_material_value, new_cyclic_material_value]
  exact HSet.empty_ne_quineAtom

theorem generated_cyclic_future :
    ((ContextualGeneratedCoalgebras.generatedCoalgebra wide allCoalgebra branchEnumerations seed).app
      initialPoint rootReceipt).val.holds
        ⟨⟨observedPoint model worldCoding futureRaw, futureArrow⟩, newCyclicReceipt⟩ := trivial

theorem actual_coalgebra_square :
    (ContextualGeneratedCoalgebras.generatedCoalgebra wide allCoalgebra branchEnumerations seed).comp
      (CoveredFuturePowerFunctor.imageHom readout) = readout.comp allCoalgebra :=
  ContextualGeneratedCoalgebras.coalgebra_square wide allCoalgebra branchEnumerations seed

def contextHistory (label : Nat) : ContextualGeneratedCoalgebras.PathNode wide allCoalgebra branchEnumerations seed :=
  ContextualGeneratedCoalgebras.contextNode wide allCoalgebra branchEnumerations seed rootPath
    (nextPoint label) (extensionArrow label)

theorem contextHistory_injective : Function.Injective contextHistory := by
  intro first second same
  have receipts := Sum.inl.inj
    (ContextualGeneratedCoalgebras.append_injective wide allCoalgebra branchEnumerations seed rootPath same)
  have history := congrArg
    (fun move : Σ target : actualContext.base.Elements, initialPoint ⟶ target => move.2.val.unop.unop.val) receipts
  exact List.singleton_injective history

def childHistory (label : Nat) : ContextualGeneratedCoalgebras.PathNode wide allCoalgebra branchEnumerations seed :=
  ContextualGeneratedCoalgebras.childNode wide allCoalgebra branchEnumerations seed rootPath
    ⟨nextPoint label, extensionArrow label⟩ (positiveSection.val (nextPoint label), false)

theorem contextHistory_ne_childHistory (label : Nat) : contextHistory label ≠ childHistory label :=
  ContextualGeneratedCoalgebras.contextNode_ne_childNode wide allCoalgebra branchEnumerations seed rootPath
    ⟨nextPoint label, extensionArrow label⟩ (positiveSection.val (nextPoint label), false)

theorem context_child_same_endpoint (label : Nat) :
    ContextualGeneratedCoalgebras.endState wide allCoalgebra branchEnumerations seed (contextHistory label) =
      ContextualGeneratedCoalgebras.endState wide allCoalgebra branchEnumerations seed (childHistory label) := by
  have values :
      (⟨nextPoint label, wide.map (extensionArrow label) (positiveMember initialPoint)⟩ :
        ContextualGeneratedCoalgebras.State wide) =
      ⟨nextPoint label, positiveMember (nextPoint label)⟩ :=
    Sigma.ext rfl (heq_of_eq (positiveMember_restriction (extensionArrow label)))
  exact (ContextualGeneratedCoalgebras.endState_contextNode wide allCoalgebra branchEnumerations seed
    rootPath (nextPoint label) (extensionArrow label)).trans
      (values.trans
        (ContextualGeneratedCoalgebras.endState_childNode wide allCoalgebra branchEnumerations seed
          rootPath ⟨nextPoint label, extensionArrow label⟩ (positiveSection.val (nextPoint label), false)).symm)

theorem equal_endpoint_distinct_receipts :
    ContextualGeneratedCoalgebras.endState wide allCoalgebra branchEnumerations seed (contextHistory 0) =
      ContextualGeneratedCoalgebras.endState wide allCoalgebra branchEnumerations seed (childHistory 0) ∧
    contextHistory 0 ≠ childHistory 0 :=
  ⟨context_child_same_endpoint 0, contextHistory_ne_childHistory 0⟩

theorem endpoint_does_not_recover_receipt :
    ¬ Function.Injective (ContextualGeneratedCoalgebras.endState wide allCoalgebra branchEnumerations seed) :=
  fun injective => contextHistory_ne_childHistory 0 (injective (context_child_same_endpoint 0))

def taggedChild (tag : Bool) : ContextualGeneratedCoalgebras.PathNode wide allCoalgebra branchEnumerations seed :=
  ContextualGeneratedCoalgebras.childNode wide allCoalgebra branchEnumerations seed rootPath
    ⟨observedPoint model worldCoding futureRaw, futureArrow⟩ (futureArgument, tag)

theorem taggedChild_distinct : taggedChild true ≠ taggedChild false := by
  intro same
  have receipts := ContextualGeneratedCoalgebras.childNode_injective wide allCoalgebra branchEnumerations seed
    rootPath ⟨observedPoint model worldCoding futureRaw, futureArrow⟩ same
  exact Bool.noConfusion (congrArg Prod.snd receipts)

theorem tagged_child_same_endpoint :
    ContextualGeneratedCoalgebras.endState wide allCoalgebra branchEnumerations seed (taggedChild true) =
      ContextualGeneratedCoalgebras.endState wide allCoalgebra branchEnumerations seed (taggedChild false) := rfl

theorem authored_duplicate_receipts_retained :
    taggedChild true ≠ taggedChild false ∧
      ContextualGeneratedCoalgebras.endState wide allCoalgebra branchEnumerations seed (taggedChild true) =
        ContextualGeneratedCoalgebras.endState wide allCoalgebra branchEnumerations seed (taggedChild false) :=
  ⟨taggedChild_distinct, tagged_child_same_endpoint⟩

namespace Ambient

def wide : actualContext.base.Elements ⥤ Type 1 where
  obj _ := HSet.{0}
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def coalgebra : NaturalHom wide (CoveredFuturePowerFamilies.family wide) := CoveredFuturePowerFunctor.unitHom wide

def enumerations (point : actualContext.base.Elements) (value : wide.obj point) :
    CoveredFuturePowerFamilies.Enumeration (coalgebra.app point value).val :=
  CoveredFuturePowerFunctor.singletonEnumeration wide point value

def seed : ContextualGeneratedCoalgebras.State wide := ⟨initialPoint, HSet.quineAtom⟩

abbrev generated := ContextualGeneratedCoalgebras.family wide coalgebra enumerations seed
abbrev readout := ContextualGeneratedCoalgebras.endpoint wide coalgebra enumerations seed
abbrev system := ContextualGeneratedCoalgebras.pathSystem wide coalgebra enumerations

theorem node_value (node : ContextualGeneratedCoalgebras.PathNode wide coalgebra enumerations seed) :
    (ContextualGeneratedCoalgebras.endState wide coalgebra enumerations seed node).2 = HSet.quineAtom := by
  rcases node with ⟨length, path⟩
  induction length with
  | zero => cases path; rfl
  | succ length earlier =>
    rcases path with ⟨previous, branch⟩
    cases branch with
    | inl _move => exact earlier previous
    | inr _child => exact earlier previous

theorem readout_value (point : actualContext.base.Elements) (receipt : generated.obj point) :
    readout.app point receipt = HSet.quineAtom := node_value receipt.1

theorem root_is_generated : Nonempty (generated.obj initialPoint) :=
  ⟨ContextualGeneratedCoalgebras.rootMember wide coalgebra enumerations seed⟩

theorem endpoint_not_surjective : ¬ Function.Surjective (readout.app initialPoint) := by
  intro onto
  obtain ⟨receipt, same⟩ := onto (∅ : HSet)
  exact HSet.empty_ne_quineAtom (same.symm.trans (readout_value initialPoint receipt))

/-- Small generation at a root does not shrink the whole ambient carrier. -/
theorem local_generation_does_not_shrink_ambient :
    Nonempty (generated.obj initialPoint) ∧ ¬ Small.{0} HSet.{0} ∧
      ¬ Function.Surjective (readout.app initialPoint) :=
  ⟨root_is_generated, UniverseSizeObstructions.ambient_not_small, endpoint_not_surjective⟩

end Ambient

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedCoalgebrasControls
