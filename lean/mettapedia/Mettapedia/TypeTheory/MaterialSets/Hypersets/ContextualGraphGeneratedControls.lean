import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphGeneratedFamilies
import Mettapedia.GSLT.Logic.ConstructiveObservedGeneratedEnclosure

/-!
# Generated observed families in the varying receipt graph universe

The actual observed continuation family has unbounded stage growth and
a dependent body that separates cyclic and terminal continuations.
Its generated product has no full-future value despite the empty present
argument fibre. These are receipt comparisons, not claims that the leaf
representation preserves the material denotation of those continuations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphGeneratedControls

open CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT
open ContextualGraphFamilyRepresentation ContextualGraphDiagrams ContextualRealizedGraphs
open ConstructiveObservedMaterialControls

abbrev active := ConstructiveObservedGeneratedEnclosure.Controls.active
abbrev product := ConstructiveObservedGeneratedEnclosure.Controls.dependentPi

def childReceipt (stage index : Nat) (positive : 0 < index) (bound : index < stage+1) :
    (literal active.decode.native).obj (task stage) :=
  encode active.decode.native (task stage) (child stage index positive bound)

theorem generated_receipts_grow (stage : Nat) :
    ¬ ∃ earlier : (literal active.decode.native).obj (task stage),
      (literal active.decode.native).map (taskStep (Nat.le_succ stage)) earlier =
        childReceipt (stage+1) (stage+1) (Nat.succ_pos stage) (by omega) := by
  rintro ⟨earlier, same⟩
  exact continuation_family_grows stage ⟨decode _ _ earlier,
    (decode_naturality _ _ earlier).symm.trans (congrArg (decode _ _) same)⟩

def cyclicBodyReceipt : (literal body.native).obj ⟨(task 2).1, ⟨(task 2).2, cyclicChild⟩⟩ :=
  encode body.native _ cyclicBodyMember

theorem generated_body_varies :
    Nonempty ((literal body.native).obj ⟨(task 2).1, ⟨(task 2).2, cyclicChild⟩⟩) ∧
      ¬ Nonempty ((literal body.native).obj ⟨(task 2).1, ⟨(task 2).2, terminalChild⟩⟩) :=
  ⟨⟨cyclicBodyReceipt⟩, fun ⟨receipt⟩ => terminal_body_empty ⟨decode _ _ receipt⟩⟩

theorem generated_complete_product_empty :
    ¬ Nonempty ((literal product.decode.native).obj (task 0)) :=
  fun ⟨receipt⟩ => full_future_product_empty ⟨decode _ _ receipt⟩

def presentProduct : (receipt : (literal active.decode.native).obj (task 0)) →
    (literal body.native).obj ⟨(task 0).1, ⟨(task 0).2, decode _ _ receipt⟩⟩ :=
  fun receipt => False.elim (initial_continuations_empty ⟨decode _ _ receipt⟩)

theorem present_product_is_not_complete_future_product :
    Nonempty ((receipt : (literal active.decode.native).obj (task 0)) →
      (literal body.native).obj ⟨(task 0).1, ⟨(task 0).2, decode _ _ receipt⟩⟩) ∧
      ¬ Nonempty ((literal product.decode.native).obj (task 0)) :=
  ⟨⟨presentProduct⟩, generated_complete_product_empty⟩

def generated_code_member (stage : Nat) :
    Member (ContextualGraphFamilyEnclosure.representedCode
      (PresheafSiteLift.Site.upFunctor.obj (task stage).1)
      (ContextualSmallFamilyUniverse.familyCode active.decode.native (task stage).1 (task stage).2))
      (ContextualGraphFamilyEnclosure.enclosure (PresheafSiteLift.Site.upFunctor.obj (task stage).1)) :=
  Member.transportParent (Equal.ofEq (move_identity _ _ _))
    (ContextualGraphGeneratedFamilies.codeMembership active _ (𝟙 _) (task stage).2)

/-- The enclosing code decodes the original dependent receipt, including
its stage and continuation, without a choice of material representative. -/
theorem enclosed_cyclic_receipt_decodes :
    ContextualGraphGeneratedFamilies.enclosedDecoder active (task 2).1 (task 2).2
      ((ContextualGraphGeneratedFamilies.enclosedDecoder active (task 2).1 (task 2).2).symm cyclicChild) =
        cyclicChild :=
  (ContextualGraphGeneratedFamilies.enclosedDecoder active (task 2).1 (task 2).2).apply_symm_apply cyclicChild

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphGeneratedControls
