import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ProviderCacheExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFailureRowTyping

/-! The loaded provider-cache implementation accepts encoded O0 failure
rows and preserves the other plan fields. Semantic failure authorization
remains supplied by the source/class-runner theorems.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlFailureCacheExecution

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit

theorem failure_rows_accepted (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : List (String × TypeExpr)) (snapshot : ProviderSnapshot)
    (signatures : snapshot.signatures = provider.signatures) (index : Nat) (argument : OCaml.Value) :
    SnapshotClosureExecution.rowsAccepted language free [] snapshot.signatures [failureRow index argument] = true := by
  have signature : signature? ⟨snapshot.signatures, [], []⟩ "ml-pattern-failure" 2 =
      some ⟨"ml-pattern-failure", [.base "MlPattern", .base "MlValue"], [.input, .input]⟩ := by
    unfold signature?
    rw [signatures]
    decide +kernel
  change ((match signature? ⟨snapshot.signatures, [], []⟩ "ml-pattern-failure" 2 with
    | none => false
    | some declared => checkRow language (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList free) []
        declared (failureRow index argument)) && true) = true
  rw [signature]
  simpa only [Bool.and_true] using failure_row_checked language terms
    (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList free) index argument

theorem failure_append_returns (state : State) (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : List (String × TypeExpr)) (snapshot : ProviderSnapshot) (fields : ProviderCacheExecution.Fields)
    (signatures : snapshot.signatures = provider.signatures) (index : Nat) (argument : OCaml.Value) :
    PureReturns ProviderCacheExecution.runtime [] state
      (apply "gslt:provider-cache:append"
        [encoded (ProviderCacheExecution.planTerm language free [] snapshot fields),
         encoded (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm [failureRow index argument])]) state
      (encoded (.application "Some" [ProviderCacheExecution.planTerm language free []
        (ProviderAppend.appendRows snapshot [failureRow index argument]) fields])) := by
  have computed := ProviderCacheExecution.append_returns state language free [] snapshot fields [failureRow index argument]
  simpa only [ProviderCacheExecution.result?, failure_rows_accepted language terms free snapshot signatures index argument,
    if_true, encodeOption, id_eq] using computed

#print axioms failure_rows_accepted
#print axioms failure_append_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlFailureCacheExecution
