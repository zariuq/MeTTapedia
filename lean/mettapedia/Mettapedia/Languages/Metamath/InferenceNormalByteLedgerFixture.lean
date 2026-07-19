import Mettapedia.Languages.Metamath.InferenceNormalByteLedger
import Mettapedia.Languages.Metamath.InferenceProjectionDVFixture

/-!
# Exact-byte fixture for the normal Metamath ledger

This module exercises `NormalTokenLedger` on the exact 532-byte upstream
disjoint-variable fixture. Tokens are slices of the original source byte
array at their actual offsets. The positive run retains the trimmed theorem
frame and the authored sequence `wy wz th.1 ax-yz`.

The negative checks demonstrate two boundaries that ordinary proof execution
alone cannot enforce: an ambient frame can be laundered through a successful
`finishProof`, and a post-insertion database can validate a literal self-use.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.InferenceNormalByteLedgerFixture

open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceNormalByteLedger
open Mettapedia.Languages.Metamath.InferenceNormalParserTrace
  (submittedNormalLabels)
open Metamath.Verify

open Mettapedia.Languages.Metamath.InferenceProjectionDVFixture

def sourceBytes : ByteArray := fixtureSource.toUTF8
def headerText : String := "  th $p |- z "

#guard sourceBytes.size == 532
#guard headerText.toUTF8.size == 13
#guard (ByteSlice.mk sourceBytes 493 13).toString == headerText

def headerState : ParserState :=
  prefixState.feedAll 493 headerText.toUTF8

def delimiterToken : ByteSlice := ByteSlice.mk sourceBytes 506 2
def firstToken : ByteSlice := ByteSlice.mk sourceBytes 509 2
def secondToken : ByteSlice := ByteSlice.mk sourceBytes 512 2
def thirdToken : ByteSlice := ByteSlice.mk sourceBytes 515 4
def fourthToken : ByteSlice := ByteSlice.mk sourceBytes 520 5
def finishToken : ByteSlice := ByteSlice.mk sourceBytes 526 2

#guard delimiterToken.toString == "$="
#guard firstToken.toString == "wy"
#guard secondToken.toString == "wz"
#guard thirdToken.toString == "th.1"
#guard fourthToken.toString == "ax-yz"
#guard finishToken.toString == "$."

def theoremPos : Pos := ⟨22, 2⟩
def targetFormula : RuntimeFormula := #[.const "|-", .var "z"]
def expectedTargetDV : Array (String × String) := #[("y", "z")]
def expectedTargetHyps : Array String := #["wy", "wz", "th.1"]

def headerShapeMatches : Bool :=
  match headerState.tokp with
  | .math formula ⟨.thm, pos, label⟩ =>
      formula == targetFormula &&
        pos.line == theoremPos.line && pos.col == theoremPos.col &&
        label == "th"
  | _ => false

#guard headerShapeMatches

/-- The live state immediately after the source `$=` token. -/
def proofAnchor : ParserState :=
  headerState.feedToken 506 delimiterToken

def anchorShapeMatches : Bool :=
  match proofAnchor.tokp with
  | .proof proof =>
      proof.pos.line == theoremPos.line &&
        proof.pos.col == theoremPos.col &&
        proof.label == "th" &&
        proof.fmla == targetFormula &&
        proof.frame.dj == expectedTargetDV &&
        proof.frame.hyps == expectedTargetHyps &&
        proof.stack.isEmpty &&
        (match proof.ptp with | .start => true | _ => false) &&
        proofAnchor.db.error?.isNone &&
        (proofAnchor.db.find? "th").isNone
  | _ => false

#guard anchorShapeMatches

/-- Executable construction of the exact four-token proof ledger. -/
def fixtureLedger? : Option NormalTokenLedger := do
  let ledger ← NormalTokenLedger.tryStart proofAnchor theoremPos "th"
    targetFormula firstToken
  let ledger ← ledger.trySnoc secondToken
  let ledger ← ledger.trySnoc thirdToken
  ledger.trySnoc fourthToken

def fixtureLedgerMatches : Bool :=
  match fixtureLedger? with
  | none => false
  | some ledger =>
      ledger.targetLabel == "th" &&
        ledger.targetFormula == targetFormula &&
        ledger.targetFrame.dj == expectedTargetDV &&
        ledger.targetFrame.hyps == expectedTargetHyps &&
        (toLabel ledger.firstToken).2 == "wy" &&
        submittedNormalLabels ledger.firstToken ledger.remainingTokens ==
          proofTokens &&
        ledger.final.stack == #[targetFormula] &&
        (match ledger.final.ptp with | .normal => true | _ => false) &&
        (ledger.anchor.db.find? "th").isNone &&
        (ledger.anchor.finishProof ledger.final).db.error?.isNone &&
        (match (ledger.anchor.finishProof ledger.final).db.find? "th" with
        | some (.assert formula frame embeddedLabel) =>
            formula == targetFormula &&
              frame.dj == expectedTargetDV &&
              frame.hyps == expectedTargetHyps &&
              embeddedLabel == "th"
        | _ => false)

#guard fixtureLedgerMatches

/-- The fixture uses the parser profile required by prefix provenance. -/
example : ModeConfig.soundDefault.prefixCertified := ⟨rfl, rfl⟩

/-! ## Source-level mutations and profile boundary -/

def dvMutationSource : String :=
  fixturePrefix ++ "  th $p |- z $= wy wy th.1 ax-yz $.\n$}\n"

def orderMutationSource : String :=
  fixturePrefix ++ "  th $p |- z $= wz wy th.1 ax-yz $.\n$}\n"

def compressedSource : String :=
  fixturePrefix ++ "  th $p |- z $= ( ax-yz ) ABCD $.\n$}\n"

def unknownSource : String :=
  fixturePrefix ++ "  th $p |- z $= ? $.\n$}\n"

#guard dvMutationSource.toUTF8.size == 532
#guard orderMutationSource.toUTF8.size == 532
#guard compressedSource.toUTF8.size == 530
#guard unknownSource.toUTF8.size == 517

def sourceRejectedWithCode
    (source : String) (config : ModeConfig) (code : ParseErrorCode) : Bool :=
  let db := checkBytes source.toUTF8 config
  db.parseErrorCode?.map ParseErrorCode.toNat == some code.toNat &&
    (db.find? "th").isNone

#guard sourceRejectedWithCode dvMutationSource .soundDefault
  .disjointVariableViolation
#guard sourceRejectedWithCode orderMutationSource .soundDefault
  .typeErrorInSubstitution
#guard sourceRejectedWithCode unknownSource .soundDefault
  .unknownStepQuestionRejected
#guard (checkBytes unknownSource.toUTF8 .zar).error?.isNone
#guard (checkBytes unknownSource.toUTF8 .zar).find? "th" |>.isSome
#guard (checkBytes compressedSource.toUTF8 .soundDefault).error?.isNone
#guard (checkBytes compressedSource.toUTF8 .soundDefault).find? "th" |>.isSome

/-! ## Executable false-green calibrations -/

def executeLabels (db : RuntimeDB) (initial : RuntimeProofState)
    (labels : List String) : Except ProofCheckFail RuntimeProofState :=
  labels.foldlM (fun state label => db.stepNormal state label) initial

/-- Replacing the trimmed target frame by the larger ambient frame still lets
the runtime fold and `finishProof` succeed, but inserts the wrong theorem
frame. This is why a ledger must retain `trim_origin`. -/
def ambientFrameLaunderingAccepted : Bool :=
  let initial := prefixDB.mkProofState theoremPos "th" targetFormula
    prefixDB.frame
  match executeLabels prefixDB { initial with ptp := .normal }
      proofTokens with
  | .error _ => false
  | .ok final =>
      let post := prefixState.finishProof final
      post.db.error?.isNone &&
        (match post.db.find? "th" with
        | some (.assert formula frame embeddedLabel) =>
            formula == targetFormula &&
              frame.dj == expectedCallerDV &&
              frame.hyps == expectedCallerHyps &&
              embeddedLabel == "th"
        | _ => false)

#guard ambientFrameLaunderingAccepted

/-- The target label fails against the retained pre-insertion database but
succeeds as a proof step after the theorem has been inserted. -/
def postInsertSelfUseAccepted : Bool :=
  match fixtureLedger? with
  | none => false
  | some ledger =>
      let prefixLabels := ["wy", "wz", "th.1"]
      let selfLabels := prefixLabels ++ ["th"]
      let before := { ledger.initial with ptp := .normal }
      let postDB := (ledger.anchor.finishProof ledger.final).db
      let after := postDB.mkProofState theoremPos "probe"
        targetFormula ledger.targetFrame
      match executeLabels ledger.anchor.db before prefixLabels with
      | .error _ => false
      | .ok beforeSelf =>
          match ledger.anchor.db.stepNormal beforeSelf "th",
              executeLabels postDB { after with ptp := .normal } selfLabels with
          | .error (.proofCheck (.statementNotFound label)), .ok final =>
              label == "th" && final.stack == #[targetFormula]
          | _, _ => false

#guard postInsertSelfUseAccepted

end Mettapedia.Languages.Metamath.InferenceNormalByteLedgerFixture
