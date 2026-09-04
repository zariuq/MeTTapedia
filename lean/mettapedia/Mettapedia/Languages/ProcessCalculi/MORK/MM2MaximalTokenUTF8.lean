import Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSemantics

/-!
# UTF-8 boundary for maximal-token MM2 parsing

The generated ParserPack consumes Unicode scalar values.  Files and native
readers consume bytes, so this module makes UTF-8 decoding an explicit,
fail-closed stage and joins successful canonical rendering to the exact
generated parser result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenUTF8

open Mettapedia.Languages.MeTTa.OSLFCore
open Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface
open Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenSemantics

/-- Decode bytes to the scalar carrier consumed by the generated ParserPack.
Invalid UTF-8 is rejected before grammar execution. -/
def decodeUtf8Scalars? (bytes : ByteArray) : Option (List Nat) :=
  (String.fromUTF8? bytes).map stringScalars

private theorem fromUTF8?_toUTF8 (value : String) :
    String.fromUTF8? value.toUTF8 = some value := by
  rw [String.toUTF8_eq_toByteArray]
  simp only [String.fromUTF8?, dif_pos value.isValidUTF8]
  cases value
  rfl

theorem decodeUtf8Scalars?_toUTF8 (value : String) :
    decodeUtf8Scalars? value.toUTF8 = some (stringScalars value) := by
  unfold decodeUtf8Scalars?
  rw [fromUTF8?_toUTF8]
  rfl

/-- A byte-level admission retains the exact UTF-8 decoding and the generated
ParserPack witness over the decoded scalar sequence. -/
structure ByteParsedProgram (bytes : ByteArray) where
  input : List Nat
  decoding : decodeUtf8Scalars? bytes = some input
  parsed : ParsedProgram input

def ByteParsedProgram.atoms {bytes : ByteArray}
    (parsed : ByteParsedProgram bytes) : List Atom :=
  parsed.parsed.atoms

/-- Any successful canonical MM2 render is admitted from its actual UTF-8
bytes and lowers to the exact source atom occurrences. -/
theorem successful_render_has_exact_byte_parser_square
    {program : List Atom} {rendered : String}
    (renderedExact : renderProgram? program = some rendered) :
    ∃ parsed : ByteParsedProgram rendered.toUTF8,
      parsed.atoms = program := by
  obtain ⟨parsed, atomsExact⟩ :=
    successful_render_has_exact_parser_square renderedExact
  refine ⟨{
    input := stringScalars rendered
    decoding := decodeUtf8Scalars?_toUTF8 rendered
    parsed := parsed
  }, atomsExact⟩

/-! ## Representation controls -/

theorem multibyte_scalar_decodes_exactly :
    decodeUtf8Scalars? "λ".toUTF8 = some [955] := by
  decide +kernel

theorem invalid_utf8_is_rejected :
    decodeUtf8Scalars? ⟨#[0xff]⟩ = none := by
  decide +kernel

#print axioms decodeUtf8Scalars?_toUTF8
#print axioms successful_render_has_exact_byte_parser_square
#print axioms multibyte_scalar_decodes_exactly
#print axioms invalid_utf8_is_rejected

end Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenUTF8
