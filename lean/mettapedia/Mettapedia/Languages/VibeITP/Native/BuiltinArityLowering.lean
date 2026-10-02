import Mettapedia.Languages.VibeITP.Native.BuiltinAritySource
import Mettapedia.GSLT.LanguageDef.NativeOpsLowering

/-!
# Actual builtin-arity operational lowering

The candidate is linked to the admitted operational function by the existing
compiler. Its signature and switch arms are shared with artifact admission;
execution and generated-C provenance are separate certificates.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.BuiltinArityLowering

open Mettapedia.GSLT.LanguageDef
open NativeOps NativeIR
open NativeWord64 (bounded encode)
open Spec

def actualArms : List (BitVec 64 × List Instruction) := Builtin.all.map (fun builtin =>
  (encode (bounded 64 builtin.slot),
    [.temporary builtin.slot .word (.word (encode (bounded 64 builtin.arity))),
      .return (.temporary builtin.slot .word)]))

def actualOtherwise : List Instruction :=
  [.temporary 13 .word (.word 0), .return (.temporary 13 .word)]

def actualFunction : NativeIR.Function :=
  ⟨NativeOpsSourceGuestSnapshot.function_040.header,
    [.checkContextExists, .checkContext, .temporary 1 .word (.readLocal "slot"),
      .switch (.temporary 1 .word) actualArms actualOtherwise], 13⟩

theorem actual_function_lowered (interface : Interface) :
    NativeLowering.function? interface NativeOpsSourceGuestSnapshot.function_040 = some actualFunction := by
  have names : ["slot"].Nodup := List.nodup_singleton _
  have distinct : (BuiltinAritySource.actualArms.map Prod.fst).Nodup := by decide +kernel
  dsimp [BuiltinAritySource.actualArms, NativeOpsSourceGuestSnapshot.function_040, List.map] at distinct
  simp +unfoldPartialApp [NativeLowering.function?, NativeOpsSourceGuestSnapshot.function_040, actualFunction,
    actualArms, actualOtherwise, Builtin.all, Builtin.slot, Builtin.arity,
    checkFunction, checkBlock, checkStatement, checkCases, returnsBlock, returnsStatement, returnsCases,
    validType, lookupVariable, inferExpr, NativeLowering.block?, NativeLowering.statement?, NativeLowering.cases?,
    NativeLowering.expression?, NativeLowering.pureTemporary, NativeIR.fresh, List.map, List.find?, names, distinct]
  rfl

end Mettapedia.Languages.VibeITP.Native.BuiltinArityLowering
