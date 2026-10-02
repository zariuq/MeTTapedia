import Mettapedia.GSLT.LanguageDef.NativeOpsCLexAccumulator

/-! An original native header character block and its exact lexer transition. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option Elab.async false

namespace Mettapedia.GSLT.LanguageDef.NativeOpsCGuest

open NativeOps NativeOps.NativeC

attribute [local irreducible] LexSegmentAgreement

def headerPiece_001_chars : List Char := [Char.ofNat 102, Char.ofNat 55, Char.ofNat 49, Char.ofNat 97, Char.ofNat 56, Char.ofNat 97, Char.ofNat 57, Char.ofNat 57, Char.ofNat 52, Char.ofNat 52, Char.ofNat 48, Char.ofNat 50, Char.ofNat 51, Char.ofNat 56, Char.ofNat 53, Char.ofNat 97, Char.ofNat 102, Char.ofNat 54, Char.ofNat 55, Char.ofNat 48, Char.ofNat 54, Char.ofNat 48, Char.ofNat 55, Char.ofNat 51, Char.ofNat 51, Char.ofNat 56, Char.ofNat 51, Char.ofNat 48, Char.ofNat 57, Char.ofNat 52, Char.ofNat 99, Char.ofNat 102, Char.ofNat 101, Char.ofNat 100, Char.ofNat 52, Char.ofNat 102, Char.ofNat 48, Char.ofNat 100, Char.ofNat 54, Char.ofNat 100, Char.ofNat 53, Char.ofNat 100, Char.ofNat 101, Char.ofNat 55, Char.ofNat 49, Char.ofNat 53, Char.ofNat 99, Char.ofNat 50, Char.ofNat 56, Char.ofNat 50, Char.ofNat 98, Char.ofNat 52, Char.ofNat 55, Char.ofNat 50, Char.ofNat 101, Char.ofNat 99, Char.ofNat 52, Char.ofNat 55, Char.ofNat 101, Char.ofNat 101, Char.ofNat 55, Char.ofNat 56, Char.ofNat 101, Char.ofNat 52, Char.ofNat 10, Char.ofNat 32, Char.ofNat 42, Char.ofNat 32, Char.ofNat 65, Char.ofNat 83, Char.ofNat 84, Char.ofNat 32, Char.ofNat 83, Char.ofNat 72, Char.ofNat 65, Char.ofNat 45, Char.ofNat 50, Char.ofNat 53, Char.ofNat 54, Char.ofNat 58, Char.ofNat 32, Char.ofNat 99, Char.ofNat 57, Char.ofNat 98, Char.ofNat 98, Char.ofNat 54, Char.ofNat 99, Char.ofNat 98, Char.ofNat 52, Char.ofNat 57, Char.ofNat 48, Char.ofNat 100, Char.ofNat 56, Char.ofNat 54, Char.ofNat 51, Char.ofNat 99, Char.ofNat 49, Char.ofNat 57, Char.ofNat 53, Char.ofNat 100, Char.ofNat 52, Char.ofNat 57, Char.ofNat 99, Char.ofNat 55, Char.ofNat 52, Char.ofNat 98, Char.ofNat 51, Char.ofNat 55, Char.ofNat 53, Char.ofNat 48, Char.ofNat 50, Char.ofNat 51, Char.ofNat 57, Char.ofNat 101, Char.ofNat 51, Char.ofNat 55, Char.ofNat 100, Char.ofNat 101, Char.ofNat 55, Char.ofNat 50, Char.ofNat 54, Char.ofNat 100, Char.ofNat 57, Char.ofNat 54, Char.ofNat 48, Char.ofNat 49, Char.ofNat 52, Char.ofNat 56, Char.ofNat 49, Char.ofNat 54, Char.ofNat 57, Char.ofNat 54, Char.ofNat 50, Char.ofNat 52, Char.ofNat 57, Char.ofNat 99, Char.ofNat 48, Char.ofNat 49, Char.ofNat 49, Char.ofNat 102, Char.ofNat 57, Char.ofNat 55, Char.ofNat 48, Char.ofNat 55, Char.ofNat 50, Char.ofNat 10, Char.ofNat 32, Char.ofNat 42, Char.ofNat 32, Char.ofNat 80, Char.ofNat 114, Char.ofNat 105, Char.ofNat 109, Char.ofNat 105, Char.ofNat 116, Char.ofNat 105, Char.ofNat 118, Char.ofNat 101, Char.ofNat 32, Char.ofNat 99, Char.ofNat 97, Char.ofNat 116, Char.ofNat 97, Char.ofNat 108, Char.ofNat 111, Char.ofNat 103, Char.ofNat 117, Char.ofNat 101, Char.ofNat 32, Char.ofNat 83, Char.ofNat 72, Char.ofNat 65, Char.ofNat 45, Char.ofNat 50, Char.ofNat 53, Char.ofNat 54, Char.ofNat 58, Char.ofNat 32, Char.ofNat 102, Char.ofNat 99, Char.ofNat 97, Char.ofNat 49, Char.ofNat 99, Char.ofNat 53, Char.ofNat 49, Char.ofNat 55, Char.ofNat 53, Char.ofNat 97, Char.ofNat 52, Char.ofNat 53, Char.ofNat 54, Char.ofNat 102, Char.ofNat 50, Char.ofNat 50, Char.ofNat 48, Char.ofNat 51, Char.ofNat 100, Char.ofNat 49, Char.ofNat 97, Char.ofNat 100, Char.ofNat 52, Char.ofNat 99, Char.ofNat 55, Char.ofNat 97, Char.ofNat 49, Char.ofNat 98, Char.ofNat 55, Char.ofNat 49, Char.ofNat 50, Char.ofNat 55, Char.ofNat 98, Char.ofNat 98, Char.ofNat 55, Char.ofNat 56, Char.ofNat 53, Char.ofNat 100, Char.ofNat 49, Char.ofNat 49, Char.ofNat 57, Char.ofNat 102, Char.ofNat 56, Char.ofNat 49, Char.ofNat 100, Char.ofNat 50, Char.ofNat 101, Char.ofNat 52, Char.ofNat 51, Char.ofNat 97, Char.ofNat 51, Char.ofNat 50, Char.ofNat 99, Char.ofNat 50, Char.ofNat 100, Char.ofNat 56, Char.ofNat 102, Char.ofNat 97, Char.ofNat 55, Char.ofNat 50, Char.ofNat 50, Char.ofNat 50, Char.ofNat 102, Char.ofNat 101, Char.ofNat 10, Char.ofNat 32, Char.ofNat 42, Char.ofNat 32, Char.ofNat 71, Char.ofNat 101, Char.ofNat 110, Char.ofNat 101, Char.ofNat 114, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100, Char.ofNat 32]
def headerPiece_001_tokens : List Token := []
def headerPiece_001_before : LexPoint := ⟨.blockComment, [], none⟩
def headerPiece_001_after : LexPoint := ⟨.blockComment, [], none⟩

theorem headerPiece_001_checked : LexSegmentAgreement headerPiece_001_before headerPiece_001_after
    headerPiece_001_chars headerPiece_001_tokens := by
  apply (segment_agreement_iff_empty_history _ _ _ _).mpr
  decide +kernel

end Mettapedia.GSLT.LanguageDef.NativeOpsCGuest
