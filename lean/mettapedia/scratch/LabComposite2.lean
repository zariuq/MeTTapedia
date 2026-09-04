import Mettapedia.GSLT.LanguageDef.CostSemanticAtomReifyCongruence

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- PROBE: one pattern reifies identically through both cospan legs when every
name resolves on both sides to atoms with equal keys. -/
theorem CostStaticAtomKeyCospan.reifyWith_eq_of_keyAgreement
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leftResolve : String → Option (Fin leftCount))
    (rightResolve : String → Option (Fin rightCount))
    (pattern : Pattern)
    (agree : ∀ name, ∃ left right,
      leftResolve name = some left ∧ rightResolve name = some right ∧
        leftKey left = rightKey right) :
    cospan.reifyWith leftResolve cospan.leftSlot pattern =
      cospan.reifyWith rightResolve cospan.rightSlot pattern := by
  refine reifyWith_eq_of_fvarAligned cospan leftResolve rightResolve
    cospan.leftSlot cospan.rightSlot (relation := fun left right => left = right)
    ?_ (FvarAligned.refl (fun _ => rfl) pattern)
  rintro leftName rightName rfl
  obtain ⟨left, right, leftSelected, rightSelected, keysEqual⟩ := agree leftName
  exact ⟨left, right, leftSelected, rightSelected,
    (cospan.crossExtensional left right).mpr keysEqual⟩

end Mettapedia.GSLT.LanguageDef
