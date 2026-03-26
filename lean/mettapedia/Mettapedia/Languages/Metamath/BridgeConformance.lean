import Mettapedia.Languages.Metamath.GroundedSemantics
import Mettapedia.Languages.Metamath.LanguageDefDSL

/-!
# Metamath Bridge Conformance Checks

These checks assert that mettapedia's Metamath bridge wrappers preserve the
same acceptance/error/step behavior as direct `mm-lean4` entrypoints.
-/

namespace Mettapedia.Languages.Metamath.BridgeConformance

open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.GroundedSemantics
open Mettapedia.Languages.Metamath.LanguageDefDSL
open Mettapedia.OSLF.MeTTaIL.Syntax

private def emptyBytes : ByteArray := "".toUTF8
private def malformedIncludeBytes : ByteArray := "$[ bad.mm ".toUTF8

example :
    checkBytesDB emptyBytes = Metamath.Verify.checkBytes emptyBytes := rfl

example :
    checkBytesDB malformedIncludeBytes =
      Metamath.Verify.checkBytes malformedIncludeBytes := rfl

example :
    acceptsBytes emptyBytes ↔
      (Metamath.Verify.checkBytes emptyBytes).error = false := by
  rfl

example :
    rejectsBytes malformedIncludeBytes ↔
      (Metamath.Verify.checkBytes malformedIncludeBytes).error = true := by
  rfl

example :
    parseErrorCode? malformedIncludeBytes =
      (Metamath.Verify.checkBytes malformedIncludeBytes).parseErrorCode? := rfl

example (rt : RuntimeState) (label : String) :
    RuntimeState.step? rt label =
      match Metamath.Verify.DB.stepNormal rt.db rt.proof label with
      | .ok rtProof => some { rt with proof := rtProof }
      | .error _ => none := by
  cases h : Metamath.Verify.DB.stepNormal rt.db rt.proof label <;>
    simp [RuntimeState.step?, RuntimeState.stepNormal, h]

example (rt : RuntimeState) (label : String) :
    RuntimeState.stepSpec? rt label =
      match Metamath.Verify.DB.stepNormal rt.db rt.proof label with
      | .ok rtProof =>
          RuntimeState.toSpecState? { rt with proof := rtProof }
      | .error _ => none := by
  cases h : Metamath.Verify.DB.stepNormal rt.db rt.proof label <;>
    simp [RuntimeState.stepSpec?, RuntimeState.step?, RuntimeState.stepNormal, h]

example :
    LanguageDef.validate metamathLanguageDef = [] := by
  native_decide

end Mettapedia.Languages.Metamath.BridgeConformance
