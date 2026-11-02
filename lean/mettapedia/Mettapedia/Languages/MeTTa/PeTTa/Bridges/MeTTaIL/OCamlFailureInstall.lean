import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlFailureCacheExecution

/-! Loaded failure-table extension runs through the existing provider
cache. The controller's install step retains the old plan and full runner
as an epoch before starting the new plan at the same request.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlFailureInstall

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

theorem append_returns (state : State) (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : List (String × TypeExpr)) (snapshot : ProviderSnapshot) (fields : ProviderCacheExecution.Fields)
    (signatures : snapshot.signatures = provider.signatures) (index : Nat) (argument : OCaml.Value) :
    PureReturns runtime [] state
      (apply "gslt:provider-cache:append"
        [encoded (ProviderCacheExecution.planTerm language free [] snapshot fields),
         encoded (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm [failureRow index argument])]) state
      (encoded (.application "Some" [ProviderCacheExecution.planTerm language free []
        (ProviderAppend.appendRows snapshot [failureRow index argument]) fields])) := by
  have base := OCamlFailureCacheExecution.failure_append_returns state language terms free snapshot fields signatures index argument
  have integer : PureReturns integerLibrary.runtime [] state
      (apply "gslt:provider-cache:append"
        [encoded (ProviderCacheExecution.planTerm language free [] snapshot fields),
         encoded (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm [failureRow index argument])]) state
      (encoded (.application "Some" [ProviderCacheExecution.planTerm language free []
        (ProviderAppend.appendRows snapshot [failureRow index argument]) fields])) := by
    metta_lift integer_checked ["plan", "rows"] base
  have word : PureReturns wordLibrary.runtime [] state
      (apply "gslt:provider-cache:append"
        [encoded (ProviderCacheExecution.planTerm language free [] snapshot fields),
         encoded (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm [failureRow index argument])]) state
      (encoded (.application "Some" [ProviderCacheExecution.planTerm language free []
        (ProviderAppend.appendRows snapshot [failureRow index argument]) fields])) := by
    metta_lift word_checked ["plan", "rows"] integer
  metta_lift checked ["plan", "rows"] word

#print axioms append_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlFailureInstall
