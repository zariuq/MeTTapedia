import Mettapedia.Languages.VibeITP.Native.BuiltinArityArtifact
import Mettapedia.Languages.VibeITP.Native.BuiltinArityLowering
import Mettapedia.GSLT.LanguageDef.NativeOpsCStatementComposition

/-!
# Admission of the generated builtin-arity C body

The separately parsed C function normalizes to the actual operational lowering.
The shared normalizer checks the context guards, parameter read, all switch
arms and default return. This certificate identifies the operational body;
concrete C layout, compiler and machine execution remain separate obligations.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace Mettapedia.Languages.VibeITP.Native.BuiltinArityCNormalization

open Mettapedia.GSLT.LanguageDef
open NativeOps NativeOps.NativeC
open BuiltinArityLowering

theorem actual_body_normalized (representation : Representation) :
    normalizeStatements? representation .word ⟨[("slot", .word)], [], []⟩
      NativeOpsCGuest.function_019.body =
    some ⟨actualFunction.body, ⟨[("slot", .word)], [(1, .word)], []⟩⟩ := by
  simp only [NativeOpsCGuest.function_019, normalizeStatements?, normalizeStatement?,
    normalizeCases?, normalizeArm?, contextCheck?, numericCheck?, nextNumericOperation?,
    ctxExpression, defaultReturn, defaultExpression, declare?, memoryCall?, functionCall?,
    pureOperation?, nativeType?, nativeBaseType?, typedAtom?, atom?, identifierAtom?,
    localBinding?, pureDiscard, actualFunction, actualArms, actualOtherwise,
    List.contains, List.replicate, List.foldl, Option.bind, Option.map, bind]
  rfl

theorem actual_function_normalized :
    normalizeFunction? NativeOpsCGuest.representation NativeOpsCGuest.function_019 =
      some actualFunction := by
  have admitted := normalize_function_of_parts NativeOpsCGuest.representation
    NativeOpsCGuest.function_019 NativeOpsSourceGuestSnapshot.function_040.header
    ⟨actualFunction.body, ⟨[("slot", .word)], [(1, .word)], []⟩⟩
    BuiltinArityArtifact.actual_header_found BuiltinArityArtifact.actual_prototype
    (actual_body_normalized NativeOpsCGuest.representation)
  have maximum : maximumIdentity actualFunction.body = 13 := by decide +kernel
  change normalizeFunction? _ _ = some (NativeIR.Function.mk
    NativeOpsSourceGuestSnapshot.function_040.header actualFunction.body
      (maximumIdentity actualFunction.body)) at admitted
  rw [maximum] at admitted
  exact admitted

theorem generated_and_authored_agree :
    normalizeFunction? NativeOpsCGuest.representation NativeOpsCGuest.function_019 =
      NativeLowering.function? NativeOpsSourceGuestSnapshot.expectedInterface
        NativeOpsSourceGuestSnapshot.function_040 := by
  rw [actual_function_normalized, actual_function_lowered]

end Mettapedia.Languages.VibeITP.Native.BuiltinArityCNormalization
