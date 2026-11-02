import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ProviderCacheExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPrimitiveRowTyping

/-! The actual shared cache accepts typed primitive rows. Its execution
preserves every uninspected plan field and retains existing row positions.
Source authorization is supplied separately by the primitive semantics.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveCache

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit

theorem rows_accepted (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : List (String × TypeExpr)) (table : ProviderSnapshot)
    (signatures : table.signatures = provider.signatures)
    (operator : OCaml.Primitive) (arguments : List OCaml.Value) (result : OCaml.Result) :
    SnapshotClosureExecution.rowsAccepted language free [] table.signatures [primitiveRow operator arguments result] = true := by
  have signature : signature? ⟨table.signatures, [], []⟩ "ml-primitive" 3 =
      some ⟨"ml-primitive", [.base "MlPrimitive", .base "MlValues", .base "MlPrimitiveResult"], [.input, .input, .output]⟩ := by
    unfold signature?
    rw [signatures]
    decide +kernel
  change ((match signature? ⟨table.signatures, [], []⟩ "ml-primitive" 3 with
    | none => false
    | some declared => checkRow language (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList free) []
        declared (primitiveRow operator arguments result)) && true) = true
  rw [signature]
  simpa only [Bool.and_true] using primitive_row_checked language terms
    (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList free) operator arguments result

theorem append_returns (state : State) (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : List (String × TypeExpr)) (table : ProviderSnapshot) (fields : ProviderCacheExecution.Fields)
    (signatures : table.signatures = provider.signatures)
    (operator : OCaml.Primitive) (arguments : List OCaml.Value) (result : OCaml.Result) :
    PureReturns ProviderCacheExecution.runtime [] state
      (apply "gslt:provider-cache:append"
        [encoded (ProviderCacheExecution.planTerm language free [] table fields),
         encoded (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm [primitiveRow operator arguments result])]) state
      (encoded (.application "Some" [ProviderCacheExecution.planTerm language free []
        (ProviderAppend.appendRows table [primitiveRow operator arguments result]) fields])) := by
  have computed := ProviderCacheExecution.append_returns state language free [] table fields [primitiveRow operator arguments result]
  simpa only [ProviderCacheExecution.result?, rows_accepted language terms free table signatures operator arguments result,
    if_true, encodeOption, id_eq] using computed

#print axioms append_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveCache
