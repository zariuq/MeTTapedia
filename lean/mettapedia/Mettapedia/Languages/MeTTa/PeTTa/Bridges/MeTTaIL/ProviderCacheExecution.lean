import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureProviderExecution
import Mettapedia.OSLF.MeTTaIL.ProviderAppend

/-! Execution of the actual checked provider-cache source. Plan fields not
inspected by this operation remain verbatim. Row typing is separate from a
service's semantic guarantee about the answers it supplies. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ProviderCacheExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram := petta_source_file%
  "../../../../../../../../metta/gslt/lib/gslt_provider_cache.metta"
  sha256 "8555270a3a281c38483f94951df68b0408eb228f45428cb3c858b505b4f9e38b"

def library : Library := ⟨SnapshotClosureExecution.runtime, source.program, ["gslt:provider-cache:"]⟩
def runtime := library.runtime

theorem checked : library.check = true := by decide +kernel

/-- These fields are transported, rather than reinterpreted by row extension. -/
structure Fields where
  rewrites : Term
  specifications : Term
  reflection : Term
  permissions : Term
  expected : Term
  rules : Term
  equations : Term
  admitted : Term

def planTerm (language : LanguageDef) (free : List (String × TypeExpr)) (bound : List TypeExpr)
    (provider : ProviderSnapshot) (fields : Fields) : Term :=
  .application "CompletePlan"
    [.application "PremiseEnvironment"
      [PremiseOperationsExecution.DeclarationTyping.declarationsTerm language.terms,
       fields.rewrites, fields.specifications,
       PremiseOperationsExecution.GeneralExecution.providerTerm provider, fields.reflection,
       PremiseOperationsExecution.DeclarationTyping.freeContextTerm free],
     fields.permissions, encodeList InferenceCettaWire.AuthoredRule.typeTerm bound,
     fields.expected, fields.rules, fields.equations, fields.admitted]

def result? (language : LanguageDef) (free : List (String × TypeExpr)) (bound : List TypeExpr)
    (provider : ProviderSnapshot) (fields : Fields) (rows : List ProviderRow) : Option Term :=
  if SnapshotClosureExecution.rowsAccepted language free bound provider.signatures rows then
    some (planTerm language free bound (ProviderAppend.appendRows provider rows) fields)
  else none

private theorem append_rows_returns {α : Type} (element : α → Term) (state : State)
    (left right : List α) :
    PureReturns SnapshotClosureExecution.runtime [] state
      (apply "gslt:automata:append" [encoded (encodeList element left), encoded (encodeList element right)])
      state (encoded (encodeList element (left ++ right))) := by
  have runner := runner_from_base% ["left", "right"]
    (CompleteExecution.complete_append_returns element state left right) using
      RetainedMatchingWire.scopedPrimitive_agreement
  metta_lift SnapshotClosureExecution.checked ["left", "right"] runner

theorem list_append_returns {α : Type} (element : α → Term) (state : State) (left right : List α) :
    PureReturns runtime [] state
      (apply "gslt:automata:append" [encoded (encodeList element left), encoded (encodeList element right)])
      state (encoded (encodeList element (left ++ right))) := by
  metta_lift checked ["left", "right"] (append_rows_returns element state left right)

theorem append_returns (state : State) (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (provider : ProviderSnapshot) (fields : Fields) (rows : List ProviderRow) :
    PureReturns runtime [] state
      (apply "gslt:provider-cache:append"
        [encoded (planTerm language free bound provider fields),
         encoded (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm rows)]) state
      (encoded (encodeOption id (result? language free bound provider fields rows))) := by
  have rowCheck := SnapshotClosureExecution.check_rows_returns state language free bound provider.signatures rows
  have extended := append_rows_returns
    PremiseOperationsExecution.GeneralExecution.providerRowTerm state provider.rows rows
  have rowCheckHere : PureReturns runtime [] state
      (apply "gslt:snapshot:check-rows"
        [encoded (PremiseOperationsExecution.DeclarationTyping.declarationsTerm language.terms),
         encoded (PremiseOperationsExecution.DeclarationTyping.freeContextTerm free),
         encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm bound),
         encoded (encodeList PremiseOperationsExecution.GeneralExecution.signatureTerm provider.signatures),
         encoded (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm rows)]) state
      (Effects.boolean (SnapshotClosureExecution.rowsAccepted language free bound provider.signatures rows)) := by
    metta_lift checked ["declarations", "free", "bound", "signatures", "rows"] rowCheck
  have extendedHere : PureReturns runtime [] state
      (apply "gslt:automata:append"
        [encoded (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm provider.rows),
         encoded (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm rows)]) state
      (encoded (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm (provider.rows ++ rows))) := by
    metta_lift checked ["left", "right"] extended
  cases valid : SnapshotClosureExecution.rowsAccepted language free bound provider.signatures rows <;>
    (simp only [result?, valid, Bool.false_eq_true, if_false, if_true]
     rw [valid] at rowCheckHere
     metta_call checked
     metta_eval [rowCheckHere, extendedHere] with checked unfolding
       [planTerm, ProviderAppend.appendRows, PremiseOperationsExecution.GeneralExecution.providerTerm])

#print axioms checked
#print axioms append_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ProviderCacheExecution
