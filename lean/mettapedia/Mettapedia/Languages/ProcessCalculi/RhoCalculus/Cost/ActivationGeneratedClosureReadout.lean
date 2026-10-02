import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedReadout

/-!
# Remaining constructor projections for generated decoder closure

These equations expose only the existing parser's returned syntax. Fuel
remains a structural parser bound, separate from execution and funding.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax

theorem name_wrapped_quote_readout (fuel depth : Nat) (source : Pattern) :
    (name? (fuel + 1) depth (.apply "$cost:wrapped-constructor:NQuote" [source])).map Subtype.val =
      ((code? fuel 0 source).map Subtype.val).map CostName.quote := by
  cases parsed : code? fuel 0 source <;> simp [name?, parsed]

theorem code_zero_readout (fuel depth : Nat) :
    (code? (fuel + 1) depth (.apply "$cost:wrapped-constructor:PZero" [])).map Subtype.val =
      some .nil := rfl

theorem proc_zero_readout (fuel depth : Nat) :
    (proc? (fuel + 1) depth (.apply "$cost:base-constructor:PZero" [])).map Subtype.val =
      some .nil := rfl

theorem code_collection_readout (fuel depth : Nat) (sources : List Pattern) :
    (code? (fuel + 1) depth (.collection .hashBag sources none)).map Subtype.val =
      (codeList? fuel depth sources).map Subtype.val := rfl

theorem codeList_nil_readout (fuel depth : Nat) :
    (codeList? (fuel + 1) depth []).map Subtype.val = some .nil := rfl

theorem codeList_cons_readout (fuel depth : Nat) (source : Pattern) (sources : List Pattern) :
    (codeList? (fuel + 1) depth (source :: sources)).map Subtype.val =
      (do
        let head ← (code? fuel depth source).map Subtype.val
        let tail ← (codeList? fuel depth sources).map Subtype.val
        some (CostTerm.par head tail)) := by
  cases headParsed : code? fuel depth source <;>
    cases tailParsed : codeList? fuel depth sources <;>
    simp [codeList?, headParsed, tailParsed]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
