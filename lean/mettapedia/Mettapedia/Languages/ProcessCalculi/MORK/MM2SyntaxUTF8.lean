import Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxSemantics

/-!
# UTF-8 input boundary for generated MM2 parsing

The authored MM2 ParserPack consumes Unicode scalar values, while files and
native readers consume bytes.  This module makes the intervening UTF-8 decode
an explicit, fail-closed stage and connects successful rendered programs to
the exact scalar-level parser result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxUTF8

open Mettapedia.Languages.MeTTa.OSLFCore
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface
open Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxSemantics

/-- Decode a native byte buffer to the scalar carrier consumed by the
generated ParserPack.  Invalid UTF-8 is rejected before grammar execution. -/
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

/-- A byte-level parse retains both the exact decoded scalar input and the
generated ParserPack witness over that input. -/
structure ByteParsedProgram (bytes : ByteArray) where
  input : List Nat
  decoding : decodeUtf8Scalars? bytes = some input
  parsed : ParsedProgram input

def ByteParsedProgram.atoms {bytes : ByteArray}
    (parsed : ByteParsedProgram bytes) : List Atom :=
  parsed.parsed.atoms

theorem ByteParsedProgram.safe {bytes : ByteArray}
    (parsed : ByteParsedProgram bytes) :
    programSafe parsed.atoms = true :=
  parsed.parsed.safe

/-- Any successful canonical MM2 render is accepted from its actual UTF-8
bytes, and the resulting canonical parser witness lowers to the exact source
atom occurrences. -/
theorem successful_render_has_exact_byte_parser_lowering
    {program : List Atom} {rendered : String}
    (renderedExact : renderProgram? program = some rendered) :
    ∃ parsed : ByteParsedProgram rendered.toUTF8,
      parsed.atoms = program := by
  obtain ⟨parsed, atomsExact⟩ :=
    successful_render_has_exact_parser_lowering renderedExact
  refine ⟨{
    input := stringScalars rendered
    decoding := decodeUtf8Scalars?_toUTF8 rendered
    parsed := parsed
  }, atomsExact⟩

/-- The byte-decoded parse enters the same reflective MM2 GSLT and OSLF
execution relation; the UTF-8 adapter introduces no execution semantics. -/
theorem ByteParsedProgram.execution_native_type_iff
    {bytes : ByteArray} (parsed : ByteParsedProgram bytes)
    (policy : UnsupportedExecPolicy) (target : List Atom) :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (reflectiveNativeListExecGSLT policy)).satisfies
        parsed.parsed.initialSupport
        (reflectiveNativeListExactTargetNativeType policy target).pred ↔
      ReflectiveComputable.cReflectiveSourceWorkQueueStep
        policy parsed.parsed.initialSupport = some target :=
  parsed.parsed.execution_native_type_iff policy target

/-! ## Representation controls -/

theorem multibyte_scalar_decodes_exactly :
    decodeUtf8Scalars? "λ".toUTF8 = some [955] := by
  decide +kernel

theorem invalid_utf8_is_rejected :
    decodeUtf8Scalars? ⟨#[0xff]⟩ = none := by
  decide +kernel

#print axioms decodeUtf8Scalars?_toUTF8
#print axioms ByteParsedProgram.safe
#print axioms successful_render_has_exact_byte_parser_lowering
#print axioms ByteParsedProgram.execution_native_type_iff
#print axioms multibyte_scalar_decodes_exactly
#print axioms invalid_utf8_is_rejected

end Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxUTF8
