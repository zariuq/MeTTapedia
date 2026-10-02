import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationLiteralEncoding
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationNormalization

/-!
# Literal authority transport preserves purse inventory

Relabelling changes only ground signing atoms. Every stored temporal stack,
including stacks quoted as data, is transported without changing occurrence
multiplicity or temporal length.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u v

mutual
  theorem CostName.relabel_purseInventory {Ground : Type u} {Target : Type v}
      (label : Ground → Target) (name : CostName Ground) :
      (name.relabel label).purseInventory = name.purseInventory.map (CostStack.relabel label) := by
    cases name <;> simp [CostName.relabel, CostName.purseInventory, CostTerm.relabel_purseInventory]

  theorem CostProc.relabel_purseInventory {Ground : Type u} {Target : Type v}
      (label : Ground → Target) (process : CostProc Ground) :
      (process.relabel label).purseInventory = process.purseInventory.map (CostStack.relabel label) := by
    cases process <;> simp [CostProc.relabel, CostProc.purseInventory, CostName.relabel_purseInventory,
      CostTerm.relabel_purseInventory, CostProc.relabel_purseInventory]

  theorem CostTerm.relabel_purseInventory {Ground : Type u} {Target : Type v}
      (label : Ground → Target) (term : CostTerm Ground) :
      (term.relabel label).purseInventory = term.purseInventory.map (CostStack.relabel label) := by
    cases term <;> simp [CostTerm.relabel, CostTerm.purseInventory, CostName.relabel_purseInventory,
      CostProc.relabel_purseInventory, CostTerm.relabel_purseInventory]
end

theorem CostTerm.PurseFree.relabel {Ground : Type u} {Target : Type v}
    (label : Ground → Target) {term : CostTerm Ground} (free : term.PurseFree) :
    (term.relabel label).PurseFree := by
  change (term.relabel label).purseInventory = 0
  rw [term.relabel_purseInventory, free]
  rfl

theorem CostStack.relabel_cellCount {Ground : Type u} {Target : Type v}
    (label : Ground → Target) (stack : CostStack Ground) :
    (stack.relabel label).cellCount = stack.cellCount := by
  cases stack with
  | empty => rfl
  | cons signature rest => simp only [CostStack.relabel, CostStack.cellCount, CostStack.relabel_cellCount label rest]

namespace ActivationGenerated

theorem CodeImage.literal_decoded_purseFree {depth : Nat} {source : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    {term : CostTerm LiteralAuthority} (image : CodeImage depth source term) :
    (decodeCostTerm (literalEncodeTerm term)).PurseFree := by
  rw [literalEncodeTerm, decodeCostTerm_encodeCostTerm]
  exact image.purseFree.relabel literalAuthorityKey

theorem CodeImage.literal_normal_decoded_purseFree {depth : Nat}
    {source : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    {term : CostTerm LiteralAuthority} (image : CodeImage depth source term) :
    (decodeCostTerm (literalEncodeTerm term).normalize).PurseFree :=
  (RawCostTerm.purseFree_normalize_iff _).mpr image.literal_decoded_purseFree

end ActivationGenerated

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
