import Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender
import Mettapedia.GSLT.LanguageDef.LF.FirstOrderOperationalCorrespondence
import Mettapedia.GSLT.LanguageDef.LF.FirstOrderMeTTaRender

/-!
# MeTTa export for proof-carrying first-order LF conversion

This exporter serializes the validated conversion source together with closed
beta, eta, and transitive conversion certificates.  The generated artifact
binds each certificate to the LF terms presented to the indexed kernel; the
runtime bridge reconstructs the first-order goals from those terms before
calling the source-indexed generic checker.
-/

namespace Mettapedia.GSLT.LanguageDef.LFFirstOrderConversionMeTTaExport

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFContextualBetaEta
open Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion
open Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualCorrespondence
open Mettapedia.GSLT.LanguageDef.LFFirstOrderOperationalCorrespondence
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender
open Mettapedia.GSLT.LanguageDef.LFFirstOrderMeTTaRender

private def betaContext : LFContextualBetaEta.Context :=
  .lamBody (.srt .type) .hole

private def firstBetaCertificate : ConversionCertificate :=
  .beta betaContext
    (.var 0)
    (.app (.lam (.var 1) (.var 0)) (.var 0))
    (.var 0)

private def secondBetaCertificate : ConversionCertificate :=
  .beta betaContext (.var 0) (.var 0) (.var 0)

private def twoStepBetaCertificate : ConversionCertificate :=
  ConversionCertificate.trans firstBetaCertificate secondBetaCertificate
    (by rfl)

private def betaGoal : Term :=
  .pi (.srt .type) (.srt .type)

private def betaGoalCertificate : ConversionCertificate :=
  .refl betaGoal

private def etaContext : LFContextualBetaEta.Context :=
  .lamBody (.pi (.srt .type) (.srt .type)) .hole

private def etaGoal : Term :=
  .pi
    (.pi (.srt .type) (.srt .type))
    (.pi (.srt .type) (.srt .type))

private def etaGoalCertificate : ConversionCertificate :=
  .refl etaGoal

private def requireSome (message : String) : Option α → Except String α
  | some value => pure value
  | none => throw message

private def reversedTransProof : RawProof :=
  rawProof "lf-fo-conversion-trans"
    [encodeTerm firstBetaCertificate.source,
      encodeTerm firstBetaCertificate.target,
      encodeTerm secondBetaCertificate.target]
    [secondBetaCertificate.proof, firstBetaCertificate.proof]

private def changedMiddleProof : RawProof :=
  rawProof "lf-fo-conversion-trans"
    [encodeTerm firstBetaCertificate.source,
      encodeTerm firstBetaCertificate.source,
      encodeTerm secondBetaCertificate.target]
    [firstBetaCertificate.proof, secondBetaCertificate.proof]

private def missingChildProof : RawProof :=
  rawProof "lf-fo-conversion-trans"
    [encodeTerm firstBetaCertificate.source,
      encodeTerm firstBetaCertificate.target,
      encodeTerm secondBetaCertificate.target]
    [firstBetaCertificate.proof]

private def unknownRuleProof : RawProof :=
  rawProof "lf-fo-unknown-rule" [] []

private def capturedEtaSource : Term :=
  .lam (.srt .type) (.app (.var 0) (.var 0))

private def capturedEtaTarget : Term := .var 0

private def capturedEtaConversionProof : RawProof :=
  rawProof "lf-fo-contextual-conversion"
    [encodeContext .hole, encodeTerm capturedEtaSource,
      encodeTerm capturedEtaTarget, encodeTerm capturedEtaSource,
      encodeTerm capturedEtaTarget]
    [fabricatedCapturedEtaProof,
      plugRawProof .hole capturedEtaSource,
      plugRawProof .hole capturedEtaTarget]

private def renderWitness
    (name : String)
    (termCertificate typeCertificate : ConversionCertificate) : String :=
  s!"(= ({name})\n" ++
    "  (KWCheckConverted\n" ++
    s!"    SNil\n" ++
    s!"    {renderTerm termCertificate.source}\n" ++
    s!"    {renderTerm termCertificate.target}\n" ++
    s!"    {renderRawProof termCertificate.proof}\n" ++
    s!"    {renderTerm typeCertificate.source}\n" ++
    s!"    {renderTerm typeCertificate.target}\n" ++
    s!"    {renderRawProof typeCertificate.proof}))\n"

private def render : Except String String := do
  let etaCertificate ← requireSome "closed eta certificate unavailable"
    (ConversionCertificate.eta? etaContext (.srt .type) (.var 1))
  pure <|
    "!(import! &self kernel_signature_lf_indexed_conversion_frontend_bridge_lib_v0)\n\n" ++
    s!"(= (lf-fo-generated-source) {renderGSLTSource source})\n" ++
    "(= (lf-fo-generated-check $witness)\n" ++
    "  (kw-lf-fo-check-with-source (lf-fo-generated-source) $witness))\n" ++
    "(= (lf-fo-generated-conversion-check $source $target $proof)\n" ++
    "  (lf-fo-conversion-check-with-source\n" ++
    "    (lf-fo-generated-source) $source $target $proof))\n\n" ++
    renderWitness "lf-fo-generated-beta-witness"
      secondBetaCertificate betaGoalCertificate ++
    renderWitness "lf-fo-generated-eta-witness"
      etaCertificate etaGoalCertificate ++
    renderWitness "lf-fo-generated-two-step-witness"
      twoStepBetaCertificate betaGoalCertificate ++
    s!"(= (lf-fo-generated-reversed-trans-proof) " ++
      s!"{renderRawProof reversedTransProof})\n" ++
    s!"(= (lf-fo-generated-changed-middle-proof) " ++
      s!"{renderRawProof changedMiddleProof})\n" ++
    s!"(= (lf-fo-generated-missing-child-proof) " ++
      s!"{renderRawProof missingChildProof})\n" ++
    s!"(= (lf-fo-generated-unknown-rule-proof) " ++
      s!"{renderRawProof unknownRuleProof})\n" ++
    s!"(= (lf-fo-generated-captured-eta-proof) " ++
      s!"{renderRawProof capturedEtaConversionProof})\n\n" ++
    "!(assertEqual\n" ++
    "  (gslt-source-validation-v1 (lf-fo-generated-source))\n" ++
    "  SourceAcceptedV1)\n" ++
    "!(assertEqual\n" ++
    "  (lf-fo-generated-conversion-check\n" ++
    s!"    {renderTerm secondBetaCertificate.source}\n" ++
    s!"    {renderTerm secondBetaCertificate.target}\n" ++
    s!"    {renderRawProof secondBetaCertificate.proof})\n" ++
    "  True)\n" ++
    "!(assertEqual\n" ++
    "  (lf-fo-generated-check (lf-fo-generated-beta-witness))\n" ++
    s!"  (Ok (CheckedPrf ANil {renderTerm secondBetaCertificate.target} " ++
      s!"{renderTerm betaGoal})))\n" ++
    "!(assertEqual\n" ++
    "  (lf-fo-generated-conversion-check\n" ++
    s!"    {renderTerm etaCertificate.source}\n" ++
    s!"    {renderTerm etaCertificate.target}\n" ++
    s!"    {renderRawProof etaCertificate.proof})\n" ++
    "  True)\n" ++
    "!(assertEqual\n" ++
    "  (lf-fo-generated-check (lf-fo-generated-eta-witness))\n" ++
    s!"  (Ok (CheckedPrf ANil {renderTerm etaCertificate.target} " ++
      s!"{renderTerm etaGoal})))\n" ++
    "!(assertEqual\n" ++
    "  (lf-fo-generated-conversion-check\n" ++
    s!"    {renderTerm twoStepBetaCertificate.source}\n" ++
    s!"    {renderTerm twoStepBetaCertificate.target}\n" ++
    s!"    {renderRawProof twoStepBetaCertificate.proof})\n" ++
    "  True)\n" ++
    "!(assertEqual\n" ++
    "  (lf-fo-generated-check (lf-fo-generated-two-step-witness))\n" ++
    s!"  (Ok (CheckedPrf ANil {renderTerm twoStepBetaCertificate.target} " ++
      s!"{renderTerm betaGoal})))\n" ++
    "!(assertEqual\n" ++
    "  (lf-fo-generated-conversion-check\n" ++
    s!"    {renderTerm twoStepBetaCertificate.source}\n" ++
    s!"    {renderTerm twoStepBetaCertificate.target}\n" ++
    "    (lf-fo-generated-reversed-trans-proof))\n" ++
    "  False)\n" ++
    "!(assertEqual\n" ++
    "  (lf-fo-generated-conversion-check\n" ++
    s!"    {renderTerm twoStepBetaCertificate.source}\n" ++
    s!"    {renderTerm twoStepBetaCertificate.target}\n" ++
    "    (lf-fo-generated-changed-middle-proof))\n" ++
    "  False)\n" ++
    "!(assertEqual\n" ++
    "  (lf-fo-generated-conversion-check\n" ++
    s!"    {renderTerm twoStepBetaCertificate.source}\n" ++
    s!"    {renderTerm twoStepBetaCertificate.target}\n" ++
    "    (lf-fo-generated-missing-child-proof))\n" ++
    "  False)\n" ++
    "!(assertEqual\n" ++
    "  (lf-fo-generated-conversion-check\n" ++
    s!"    {renderTerm twoStepBetaCertificate.source}\n" ++
    s!"    {renderTerm twoStepBetaCertificate.target}\n" ++
    "    (lf-fo-generated-unknown-rule-proof))\n" ++
    "  False)\n" ++
    "!(assertEqual\n" ++
    "  (lf-fo-generated-conversion-check\n" ++
    s!"    {renderTerm capturedEtaSource}\n" ++
    s!"    {renderTerm capturedEtaTarget}\n" ++
    "    (lf-fo-generated-captured-eta-proof))\n" ++
    "  False)\n" ++
    "!(assertEqual\n" ++
    "  (lf-fo-generated-check malformed)\n" ++
    "  (Err bad-conversion-witness))\n" ++
    "!(LFFirstOrderConversionLiveSummary 3 5 13 13 0)\n"

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [outputPath] =>
      match render with
      | .error message =>
          IO.eprintln message
          pure 1
      | .ok output =>
          IO.FS.writeFile outputPath output
          IO.println s!"wrote {output.toUTF8.size} bytes to {outputPath}"
          pure 0
  | _ =>
      IO.eprintln "usage: FirstOrderConversionMeTTaExport <output.metta>"
      pure 1

end Mettapedia.GSLT.LanguageDef.LFFirstOrderConversionMeTTaExport

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.GSLT.LanguageDef.LFFirstOrderConversionMeTTaExport.main arguments
