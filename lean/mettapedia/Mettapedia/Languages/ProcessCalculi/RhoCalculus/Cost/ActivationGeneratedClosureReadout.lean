import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedReadout

/-!
# The readout, one constructor at a time: the remaining constructors

The clauses for quotation, zero, bags and lists, in the same form as the equations of
`ActivationGeneratedReadout`. Fuel is a bound on the depth of the syntax, not on execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax

theorem name_wrapped_quote_readout (fuel depth : Nat) (source : Pattern) :
    (name? (fuel + 1) depth (.apply "$cost:wrapped-constructor:NQuote" [source])).map Subtype.val =
      ((code? fuel 0 source).map Subtype.val).map CostName.quote := by
  simp only [name?_val, code?_val]; rfl

theorem code_zero_readout (fuel depth : Nat) :
    (code? (fuel + 1) depth (.apply "$cost:wrapped-constructor:PZero" [])).map Subtype.val =
      some .nil := code?_val _ _ _

theorem proc_zero_readout (fuel depth : Nat) :
    (proc? (fuel + 1) depth (.apply "$cost:base-constructor:PZero" [])).map Subtype.val =
      some .nil := proc?_val _ _ _

theorem code_collection_readout (fuel depth : Nat) (sources : List Pattern) :
    (code? (fuel + 1) depth (.collection .hashBag sources none)).map Subtype.val =
      (codeList? fuel depth sources).map Subtype.val := by
  simp only [code?_val, codeList?_val]; rfl

theorem codeList_nil_readout (fuel depth : Nat) :
    (codeList? (fuel + 1) depth []).map Subtype.val = some .nil := codeList?_val _ _ _

theorem codeList_cons_readout (fuel depth : Nat) (source : Pattern) (sources : List Pattern) :
    (codeList? (fuel + 1) depth (source :: sources)).map Subtype.val =
      (do
        let head ← (code? fuel depth source).map Subtype.val
        let tail ← (codeList? fuel depth sources).map Subtype.val
        some (CostTerm.par head tail)) := by
  simp only [codeList?_val, code?_val]; rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
