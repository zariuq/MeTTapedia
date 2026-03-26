import Mettapedia.Languages.Metamath.GroundedSemantics

/-!
# Metamath Fixture-Driven Parity Checks

Small parser/checker fixtures that pin expected behavior at the grounded
`mm-lean4` boundary.
-/

namespace Mettapedia.Languages.Metamath.Fixtures

open Mettapedia.Languages.Metamath.GroundedSemantics

def emptyBytes : ByteArray := "".toUTF8

def minimalAxiomBytes : ByteArray :=
  "$c wff $. $v ph $. wph $f wff ph $. ax1 $a wff ph $.".toUTF8

def brokenIncludeBytes : ByteArray := "$[ bad.mm ".toUTF8

def brokenConstBytes : ByteArray := "$c wff ".toUTF8

/- Positive fixtures: accepted, no parse/proof error code. -/
example : (checkBytesDB emptyBytes).error = false := by native_decide
example : acceptsBytes emptyBytes := by
  exact (acceptsBytes_iff_noError emptyBytes).2 (by native_decide)
example : parseErrorCode? emptyBytes = none := by native_decide

example : (checkBytesDB minimalAxiomBytes).error = false := by native_decide
example : acceptsBytes minimalAxiomBytes := by
  exact (acceptsBytes_iff_noError minimalAxiomBytes).2 (by native_decide)
example : parseErrorCode? minimalAxiomBytes = none := by native_decide

/- Negative fixtures: rejected with concrete parser diagnostics. -/
example : (checkBytesDB brokenIncludeBytes).error = true := by native_decide
example : rejectsBytes brokenIncludeBytes := by
  exact (rejectsBytes_iff_error brokenIncludeBytes).2 (by native_decide)
example :
    parseErrorCode? brokenIncludeBytes =
      some Metamath.Verify.ParseErrorCode.notACommand := by
  native_decide

example : (checkBytesDB brokenConstBytes).error = true := by native_decide
example : rejectsBytes brokenConstBytes := by
  exact (rejectsBytes_iff_error brokenConstBytes).2 (by native_decide)
example :
    parseErrorCode? brokenConstBytes =
      some Metamath.Verify.ParseErrorCode.unclosedConst := by
  native_decide

end Mettapedia.Languages.Metamath.Fixtures
