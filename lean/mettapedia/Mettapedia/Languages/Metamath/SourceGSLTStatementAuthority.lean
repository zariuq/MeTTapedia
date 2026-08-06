import Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
import Mettapedia.Languages.Metamath.SourceGSLT

/-!
# Statement authority: the segmenter answers to the authored GSLT

Tranche item 2, lexical leg.  The raw-source segmenter dispatches on
keyword byte lists and charset predicates.  This module proves each of
them equal to the corresponding entry of the **authored** source GSLT
tables (`literalBindings`, `labelCodepoints`, `mathSymbolCodepoints`,
`compressedCodepoints`) — so the segmentation machine has no lexical
authority of its own.  Every binding is kernel-checked against the
authored data, not restated.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.SourceGSLTStatementAuthority

open Mettapedia.Languages.Metamath.SourceGSLTIncludeDAG
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.Metamath.SourceGSLT

/-- Byte list of an ASCII spelling. -/
def spellingBytes (s : String) : List UInt8 :=
  s.toList.map (fun c => UInt8.ofNat c.toNat)

/-! ## Keyword bytes are the authored literal spellings -/

theorem constKeyword_authored :
    constKeywordBytes = spellingBytes "$c" ∧
      "$c" ∈ literalBindings.map (·.spelling) := by
  constructor <;> decide

theorem varKeyword_authored :
    varKeywordBytes = spellingBytes "$v" ∧
      "$v" ∈ literalBindings.map (·.spelling) := by
  constructor <;> decide

theorem djKeyword_authored :
    djKeywordBytes = spellingBytes "$d" ∧
      "$d" ∈ literalBindings.map (·.spelling) := by
  constructor <;> decide

theorem floatKeyword_authored :
    floatKeywordBytes = spellingBytes "$f" ∧
      "$f" ∈ literalBindings.map (·.spelling) := by
  constructor <;> decide

theorem essentialKeyword_authored :
    essentialKeywordBytes = spellingBytes "$e" ∧
      "$e" ∈ literalBindings.map (·.spelling) := by
  constructor <;> decide

theorem axiomKeyword_authored :
    axiomKeywordBytes = spellingBytes "$a" ∧
      "$a" ∈ literalBindings.map (·.spelling) := by
  constructor <;> decide

theorem provableKeyword_authored :
    provableKeywordBytes = spellingBytes "$p" ∧
      "$p" ∈ literalBindings.map (·.spelling) := by
  constructor <;> decide

theorem proofSeparator_authored :
    proofSeparatorBytes = spellingBytes "$=" ∧
      "$=" ∈ literalBindings.map (·.spelling) := by
  constructor <;> decide

theorem statementEnd_authored :
    SourceGSLTRawSourceComposition.statementEndBytes =
      spellingBytes "$." ∧
      "$." ∈ literalBindings.map (·.spelling) := by
  constructor <;> decide

theorem parenOpen_authored :
    parenOpenBytes = spellingBytes "(" ∧
      "(" ∈ literalBindings.map (·.spelling) := by
  constructor <;> decide

theorem parenClose_authored :
    parenCloseBytes = spellingBytes ")" ∧
      ")" ∈ literalBindings.map (·.spelling) := by
  constructor <;> decide

theorem scopeOpen_authored :
    SourceGSLTIncludeDAG.scopeOpenBytes = spellingBytes "${" ∧
      "${" ∈ literalBindings.map (·.spelling) := by
  constructor <;> decide

theorem scopeClose_authored :
    SourceGSLTIncludeDAG.scopeCloseBytes = spellingBytes "$}" ∧
      "$}" ∈ literalBindings.map (·.spelling) := by
  constructor <;> decide

/-! ## Charsets are the authored codepoint classes -/

theorem labelByte_authored (b : UInt8) :
    labelByte b = true ↔ b.toNat ∈ labelCodepoints := by
  have hfin : ∀ n : Fin 256,
      (labelByte (UInt8.ofNat n.val) = true ↔
        (UInt8.ofNat n.val).toNat ∈ labelCodepoints) := by decide
  have h256 : b.toNat < 256 := b.toBitVec.isLt
  have := hfin ⟨b.toNat, h256⟩
  simpa [UInt8.ofNat_toNat] using this

theorem mathByte_authored (b : UInt8) :
    mathByte b = true ↔ b.toNat ∈ mathSymbolCodepoints := by
  have hfin : ∀ n : Fin 256,
      (mathByte (UInt8.ofNat n.val) = true ↔
        (UInt8.ofNat n.val).toNat ∈ mathSymbolCodepoints) := by decide
  have h256 : b.toNat < 256 := b.toBitVec.isLt
  have := hfin ⟨b.toNat, h256⟩
  simpa [UInt8.ofNat_toNat] using this

theorem compressedWordByte_authored (b : UInt8) :
    compressedWordByte b = true ↔ b.toNat ∈ compressedCodepoints := by
  have hfin : ∀ n : Fin 256,
      (compressedWordByte (UInt8.ofNat n.val) = true ↔
        (UInt8.ofNat n.val).toNat ∈ compressedCodepoints) := by decide
  have h256 : b.toNat < 256 := b.toBitVec.isLt
  have := hfin ⟨b.toNat, h256⟩
  simpa [UInt8.ofNat_toNat] using this

end Mettapedia.Languages.Metamath.SourceGSLTStatementAuthority
