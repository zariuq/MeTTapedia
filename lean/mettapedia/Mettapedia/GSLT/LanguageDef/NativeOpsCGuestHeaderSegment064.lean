import Mettapedia.GSLT.LanguageDef.NativeOpsCLexAccumulator

/-! An original native header character block and its exact lexer transition. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option Elab.async false

namespace Mettapedia.GSLT.LanguageDef.NativeOpsCGuest

open NativeOps NativeOps.NativeC

attribute [local irreducible] LexSegmentAgreement

def headerPiece_064_chars : List Char := [Char.ofNat 99, Char.ofNat 116, Char.ofNat 120, Char.ofNat 44, Char.ofNat 32, Char.ofNat 67, Char.ofNat 101, Char.ofNat 116, Char.ofNat 116, Char.ofNat 97, Char.ofNat 71, Char.ofNat 115, Char.ofNat 108, Char.ofNat 116, Char.ofNat 95, Char.ofNat 86, Char.ofNat 105, Char.ofNat 98, Char.ofNat 101, Char.ofNat 73, Char.ofNat 84, Char.ofNat 80, Char.ofNat 75, Char.ofNat 101, Char.ofNat 114, Char.ofNat 110, Char.ofNat 101, Char.ofNat 108, Char.ofNat 95, Char.ofNat 80, Char.ofNat 114, Char.ofNat 111, Char.ofNat 116, Char.ofNat 111, Char.ofNat 99, Char.ofNat 111, Char.ofNat 108, Char.ofNat 86, Char.ofNat 49, Char.ofNat 32, Char.ofNat 42, Char.ofNat 32, Char.ofNat 108, Char.ofNat 111, Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 95, Char.ofNat 115, Char.ofNat 41, Char.ofNat 59, Char.ofNat 10, Char.ofNat 10, Char.ofNat 35, Char.ofNat 101, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 102, Char.ofNat 10]
def headerPiece_064_tokens : List Token := [.punctuation [Char.ofNat 42], .identifier [Char.ofNat 99, Char.ofNat 116, Char.ofNat 120], .punctuation [Char.ofNat 44], .identifier [Char.ofNat 67, Char.ofNat 101, Char.ofNat 116, Char.ofNat 116, Char.ofNat 97, Char.ofNat 71, Char.ofNat 115, Char.ofNat 108, Char.ofNat 116, Char.ofNat 95, Char.ofNat 86, Char.ofNat 105, Char.ofNat 98, Char.ofNat 101, Char.ofNat 73, Char.ofNat 84, Char.ofNat 80, Char.ofNat 75, Char.ofNat 101, Char.ofNat 114, Char.ofNat 110, Char.ofNat 101, Char.ofNat 108, Char.ofNat 95, Char.ofNat 80, Char.ofNat 114, Char.ofNat 111, Char.ofNat 116, Char.ofNat 111, Char.ofNat 99, Char.ofNat 111, Char.ofNat 108, Char.ofNat 86, Char.ofNat 49], .punctuation [Char.ofNat 42], .identifier [Char.ofNat 108, Char.ofNat 111, Char.ofNat 99, Char.ofNat 97, Char.ofNat 108, Char.ofNat 95, Char.ofNat 115], .punctuation [Char.ofNat 41], .punctuation [Char.ofNat 59], .punctuation [Char.ofNat 35], .identifier [Char.ofNat 101, Char.ofNat 110, Char.ofNat 100, Char.ofNat 105, Char.ofNat 102]]
def headerPiece_064_before : LexPoint := ⟨(.pair (Char.ofNat 42)), [], none⟩
def headerPiece_064_after : LexPoint := ⟨.idle, [], none⟩

theorem headerPiece_064_checked : LexSegmentAgreement headerPiece_064_before headerPiece_064_after
    headerPiece_064_chars headerPiece_064_tokens := by
  apply (segment_agreement_iff_empty_history _ _ _ _).mpr
  decide +kernel

end Mettapedia.GSLT.LanguageDef.NativeOpsCGuest
