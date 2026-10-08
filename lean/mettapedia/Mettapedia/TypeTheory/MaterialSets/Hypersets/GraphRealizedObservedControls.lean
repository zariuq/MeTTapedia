import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedObservedFamilies
import Mettapedia.GSLT.Logic.ConstructiveObservedMaterialControls

/-!
# Infinite varying observed receipt controls

Every natural stage adds a genuinely new continuation. The dependent body
is inhabited at a cyclic child and empty at a terminal child. A product
over the empty present fibre exists, whereas the actual complete-future
product has no receipt. The contextual sum has a directly authored receipt.
These controls instantiate the actual observed execution construction.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedObservedControls

open CategoryTheory Mettapedia.GSLT
open GraphRealizedReceiptFamilies GraphRealizedContextualFamilies


abbrev domain := ConstructiveObservedMaterialControls.domain
abbrev body := ConstructiveObservedMaterialControls.body
abbrev product := (ConstructiveObservedMaterialFamilies.continuationPiCode ConstructiveObservedMaterialControls.worlds ConstructiveObservedMaterialControls.arrows
  ConstructiveObservedMaterialControls.dynamics ConstructiveObservedMaterialControls.atoms ConstructiveObservedMaterialControls.atomCoding).decode
abbrev sum := (ConstructiveObservedMaterialFamilies.continuationSigmaCode ConstructiveObservedMaterialControls.worlds ConstructiveObservedMaterialControls.arrows
  ConstructiveObservedMaterialControls.dynamics ConstructiveObservedMaterialControls.atoms ConstructiveObservedMaterialControls.atomCoding).decode

def childReceipt (stage index : Nat) (positive : 0 < index) (bound : index < stage + 1) :
    (family.{1,1} domain).obj (ConstructiveObservedMaterialControls.task stage) :=
  (decode.{1,1} domain (ConstructiveObservedMaterialControls.task stage)).symm (ConstructiveObservedMaterialControls.child stage index positive bound)

theorem initial_receipts_empty : ¬ Nonempty ((family.{1,1} domain).obj (ConstructiveObservedMaterialControls.task 0)) := by
  rintro ⟨receipt⟩
  exact ConstructiveObservedMaterialControls.initial_continuations_empty ⟨decode.{1,1} domain _ receipt⟩

theorem receipt_family_grows (stage : Nat) :
    ¬ ∃ earlier : (family.{1,1} domain).obj (ConstructiveObservedMaterialControls.task stage),
      (family.{1,1} domain).map (ConstructiveObservedMaterialControls.taskStep (Nat.le_succ stage)) earlier =
        childReceipt (stage + 1) (stage + 1) (Nat.succ_pos stage) (by omega) := by
  rintro ⟨earlier, same⟩
  apply ConstructiveObservedMaterialControls.continuation_family_grows stage
  refine ⟨decode.{1,1} domain _ earlier, ?_⟩
  have decoded := congrArg (decode.{1,1} domain _) same
  exact (restriction_decode.{1,1} domain _ earlier).symm.trans
    (decoded.trans ((decode.{1,1} domain _).apply_symm_apply _))

def cyclicBodyReceipt : (family.{1,1} body).obj
    ⟨(ConstructiveObservedMaterialControls.task 2).1, ⟨(ConstructiveObservedMaterialControls.task 2).2, ConstructiveObservedMaterialControls.cyclicChild⟩⟩ :=
  (decode.{1,1} body _).symm ConstructiveObservedMaterialControls.cyclicBodyMember

theorem terminal_body_receipts_empty : ¬ Nonempty ((family.{1,1} body).obj
    ⟨(ConstructiveObservedMaterialControls.task 2).1, ⟨(ConstructiveObservedMaterialControls.task 2).2, ConstructiveObservedMaterialControls.terminalChild⟩⟩) := by
  rintro ⟨receipt⟩
  exact ConstructiveObservedMaterialControls.terminal_body_empty ⟨decode.{1,1} body _ receipt⟩

theorem actual_dependent_body_varies :
    Nonempty ((family.{1,1} body).obj ⟨(ConstructiveObservedMaterialControls.task 2).1, ⟨(ConstructiveObservedMaterialControls.task 2).2, ConstructiveObservedMaterialControls.cyclicChild⟩⟩) ∧
      ¬ Nonempty ((family.{1,1} body).obj ⟨(ConstructiveObservedMaterialControls.task 2).1, ⟨(ConstructiveObservedMaterialControls.task 2).2, ConstructiveObservedMaterialControls.terminalChild⟩⟩) :=
  ⟨⟨cyclicBodyReceipt⟩, terminal_body_receipts_empty⟩

def presentProduct : (receipt : (family.{1,1} domain).obj (ConstructiveObservedMaterialControls.task 0)) →
    (family.{1,1} body).obj ⟨(ConstructiveObservedMaterialControls.task 0).1,
      ⟨(ConstructiveObservedMaterialControls.task 0).2, decode.{1,1} domain (ConstructiveObservedMaterialControls.task 0) receipt⟩⟩ :=
  fun receipt => (initial_receipts_empty ⟨receipt⟩).elim

theorem full_future_receipts_empty : ¬ Nonempty ((family.{1,1} product).obj (ConstructiveObservedMaterialControls.task 0)) := by
  rintro ⟨receipt⟩
  exact ConstructiveObservedMaterialControls.full_future_product_empty ⟨decode.{1,1} product _ receipt⟩

def sumReceipt : (family.{1,1} sum).obj (ConstructiveObservedMaterialControls.task 2) :=
  (decode.{1,1} sum _).symm ConstructiveObservedMaterialControls.cyclicPair

theorem sumReceipt_first : (decode.{1,1} sum (ConstructiveObservedMaterialControls.task 2) sumReceipt).1 = ConstructiveObservedMaterialControls.cyclicChild :=
  congrArg Sigma.fst ((decode.{1,1} sum _).apply_symm_apply ConstructiveObservedMaterialControls.cyclicPair)

theorem whole_compatible_term_recovery (term : (family.{1,1} product).sections) :
    (sectionEquiv.{1,1} product).symm (sectionEquiv.{1,1} product term) = term :=
  (sectionEquiv.{1,1} product).symm_apply_apply term

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedObservedControls
