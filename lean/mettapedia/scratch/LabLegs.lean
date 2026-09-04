import Mettapedia.GSLT.LanguageDef.CostRestorationRelation

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- **The two cospan legs reify a name identically when the name's atoms carry
equal keys.**  `crossExtensional` turns key agreement into slot agreement, and
`commonAtomName` depends only on the common slot. -/
theorem CostStaticAtomKeyCospan.reifyNameWith_eq_of_keys
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leftResolve : String → Option (Fin leftCount))
    (rightResolve : String → Option (Fin rightCount))
    (name : String)
    (agree : ∀ left right, leftResolve name = some left →
      rightResolve name = some right → leftKey left = rightKey right)
    (leftNone : leftResolve name = none → rightResolve name = none)
    (rightNone : rightResolve name = none → leftResolve name = none) :
    cospan.reifyNameWith leftResolve cospan.leftSlot name =
      cospan.reifyNameWith rightResolve cospan.rightSlot name := by
  unfold CostStaticAtomKeyCospan.reifyNameWith
  cases leftSelected : leftResolve name with
  | none =>
      rw [leftNone leftSelected]
  | some left =>
      cases rightSelected : rightResolve name with
      | none => exact absurd (rightNone rightSelected) (by simp [leftSelected])
      | some right =>
          exact congrArg cospan.commonAtomName
            ((cospan.crossExtensional left right).mpr
              (agree left right leftSelected rightSelected))

end Mettapedia.GSLT.LanguageDef
