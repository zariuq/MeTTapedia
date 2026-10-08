import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphReceiptFamilies
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphNonThinControls

/-!
# Growing whole-section controls for contextual graph receipts

After the first declared label, every actual continuation retains that
arrival and exposes more ordinal children. The zero child gives one
compatible section on the complete non-thin future category, while the
fibres grow at arbitrarily late stages. Current-empty observations before
the first label do not support such a section or determine its future.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphReceiptControls

open CategoryTheory ContextualWitnessCover ContextualGraphDiagrams
open ContextualSmallFamilyUniverse ContextualGraphReceiptFamilies
open LabelledContextPaths ContextualGraphNonThinControls

def futures : World ⥤ Type where
  obj point := next ⟶ point
  map arrival := TypeCat.ofHom (fun earlier => earlier ≫ arrival)
  map_id _ := by
    apply ConcreteCategory.hom_ext
    exact Category.comp_id
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro history
    exact (Category.assoc history earlier later).symm

def parent (label : Nat) : NaturalHom futures (values World) where
  app _ history := move World history (arrived label (extension label))
  naturality arrival history := (move_composition World history arrival _).symm

def zeroSection (label : Nat) : (along (parent label)).sections :=
  ⟨fun point => moveChild World point.2 (arrived label (extension label)) (firstChild label), by
    intro first second step
    apply eq_of_heq
    have target : HEq
        (moveChild World (first.2 ≫ step.1) (arrived label (extension label)) (firstChild label))
        (moveChild World second.2 (arrived label (extension label)) (firstChild label)) := by
      have histories : first.2 ≫ step.1 = second.2 := step.2
      rw [histories]
    exact (family_map_heq World ((elementMap (parent label)).map step) _).trans
      ((moveChild_comp_heq World first.2 step.1 (arrived label (extension label))
        (firstChild label)).symm.trans target)⟩

theorem zeroSection_reading (label : Nat) (point : World) (history : next ⟶ point) :
    (sectionReading (parent label) (zeroSection label)).app point history =
      ordinalValue label point 0 := rfl

def zeroSection_membership (label : Nat) (point : World) (history : next ⟶ point) :
    ContextualRealizedGraphs.Member (ordinalValue label point 0) ((parent label).app point history) :=
  sectionMembership (parent label) (zeroSection label) point history

theorem zeroSection_roundtrip (label : Nat) :
    sectionOfSelection (parent label)
      ((wholeSectionEquiv (parent label)) (zeroSection label)) = zeroSection label :=
  section_selection (parent label) (zeroSection label)

def continued (label count : Nat) : next ⟶ stage count :=
  ⟨List.replicate count label, by simp [next, stage, Nat.add_comm]⟩

theorem parent_at_stage (label count : Nat) :
    (parent label).app (stage count) (continued label count) =
      arrived label (history label count) := by
  exact (move_composition World (extension label) (continued label count) (root label)).symm

def newestReceipt (label count : Nat) :
    (along (parent label)).obj ⟨stage count, continued label count⟩ :=
  cast (congrArg (Child World) (parent_at_stage label count).symm) (newest label count)

theorem continued_composition (label count : Nat) :
    continued label count ≫ grow label count = continued label (count+1) := by
  apply Subtype.ext
  exact List.replicate_succ'.symm

def growth (label count : Nat) :=
  CategoryOfElements.homMk (F := futures)
    ⟨stage count, continued label count⟩ ⟨stage (count+1), continued label (count+1)⟩
    (grow label count) (continued_composition label count)

theorem newestReceipt_value (label count : Nat) :
    childValue World ((parent label).app (stage count) (continued label count))
      (newestReceipt label count) = ordinalValue label (stage count) count :=
  (childValue_cast World (parent_at_stage label count).symm (newest label count)).trans
    (newest_value label count)

/-- At every stage the next fibre has an actual child receipt outside the
image of the native context map. -/
theorem later_receipt_not_in_image (label count : Nat)
    (receipt : (along (parent label)).obj ⟨stage count, continued label count⟩) :
    (along (parent label)).map (growth label count) receipt ≠ newestReceipt label (count+1) := by
  intro same
  let old := cast (congrArg (Child World) (parent_at_stage label count)) receipt
  have oldRead := childValue_cast World (parent_at_stage label count) receipt
  have oldNodes : old.val = receipt.val := eq_of_heq (Sigma.mk.inj_iff.mp oldRead).2
  have readings := (childValue_map World
    ((elementMap (parent label)).map (growth label count)) receipt).symm.trans
      ((congrArg (childValue World
        ((parent label).app (stage (count+1)) (continued label (count+1)))) same).trans
          (newestReceipt_value label (count+1)))
  have nodeEquality : advance (grow label count) receipt.val = Sum.inr (count+1) :=
    eq_of_heq (Sigma.mk.inj_iff.mp readings).2
  exact newest_not_from_previous label count old ((congrArg (advance (grow label count)) oldNodes).trans
    nodeEquality)

theorem distinct_receipts (label : Nat) :
    (zeroSection label).val ⟨stage 1, continued label 1⟩ ≠ newestReceipt label 1 := by
  intro same
  have readings := congrArg (childValue World
    ((parent label).app (stage 1) (continued label 1))) same
  change ordinalValue label (stage 1) 0 = _ at readings
  rw [newestReceipt_value] at readings
  have nodes := eq_of_heq (Sigma.mk.inj_iff.mp readings).2
  exact Nat.zero_ne_one (Sum.inr.inj nodes)

theorem decoded_receipt_family (label : Nat) :
    decodedFamily (ContextualSmallFamilyUniverse.classifier (along (parent label))) =
      along (parent label) := decoded_classifier_eq _

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphReceiptControls
