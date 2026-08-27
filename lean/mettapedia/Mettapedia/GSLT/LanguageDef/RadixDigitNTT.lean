import Mettapedia.GSLT.LanguageDef.RadixDigitRelationCatalog
import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory

/-!
# OSLF and native-type diagnostics for the radix-digit machine

The input is the validated, reified `RadixDigitLanguageDef.language`.  Its
spatial types come from the authored constructor graph, while its behavioral
modalities come from the supplied operational relation environment.  The
closed mathematical implementation of the bounded primitive relation remains
`RadixDigitRelationCatalog.executePrimitive`.
-/

namespace Mettapedia.GSLT.LanguageDef.RadixDigitNTT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.GSLT.LanguageDef.RadixDigitMachine
open Mettapedia.GSLT.LanguageDef.RadixDigitLanguageDef
open Mettapedia.GSLT.LanguageDef.RadixDigitRelationCatalog

def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

theorem jump_native_crossing :
    ("radix-digit:jump", "Nat", "Instruction") ∈
      unaryCrossings language := by
  decide

theorem digit_buffer_outcome_crossing :
    ("radix-digit:outcome-value", "DigitBuffer", "Outcome") ∈
      unaryCrossings language := by
  decide

theorem no_registers_outcome_crossing :
    ("radix-digit:invented-registers-outcome", "Registers", "Outcome") ∉
      unaryCrossings language := by
  decide

private def program : Pattern := a "radix-digit:demo-program"
private def pcZero : Pattern := a "radix-digit:demo-pc-zero"
private def pcOne : Pattern := a "radix-digit:demo-pc-one"
private def buffers : Pattern := a "radix-digit:demo-buffers"
private def registers : Pattern := a "radix-digit:demo-registers"
private def fuelZero : Pattern := a "radix-digit:demo-fuel-zero"
private def fuelOne : Pattern := a "radix-digit:demo-fuel-one"
private def receiptNil : Pattern := a "radix-digit:demo-receipt-nil"
private def instruction : Pattern := a "radix-digit:jump" [pcOne]
private def receiptAfter : Pattern :=
  a "radix-digit:receipt-cons"
    [a "radix-digit:execute-event" [pcZero], receiptNil]
private def primitiveResult : Pattern :=
  a "radix-digit:result-next" [buffers, registers, pcOne, receiptAfter]

/-- Finite executable evidence for one jump.  This is an OSLF diagnostic
environment, not a replacement for the universal closed primitive catalog. -/
def demoRelationEnv : RelationEnv where
  tuples := fun relation _arguments =>
    if relation == "RadixDigitConsumeFuel" then
      [[fuelOne, fuelZero]]
    else if relation == "RadixDigitFetch" then
      [[program, pcZero, instruction]]
    else if relation == "RadixDigitExecuteInstruction" then
      [[instruction, buffers, registers, receiptAfter, primitiveResult]]
    else
      []

def radixDigitOSLF :=
  langOSLFUsing demoRelationEnv language "Config"

theorem radixDigit_galois :
    GaloisConnection
      (langDiamondUsing demoRelationEnv language)
      (langBoxUsing demoRelationEnv language) :=
  langGaloisUsing demoRelationEnv language

private def start : Pattern :=
  run program pcZero buffers registers fuelOne receiptNil

private def next : Pattern :=
  run program pcOne buffers registers fuelZero receiptAfter

theorem jump_step_exact :
    rewriteAt (engineBasePremises demoRelationEnv) language 1 start =
      [next] := by
  decide +kernel

theorem halted_is_normal :
    rewriteAt (engineBasePremises demoRelationEnv) language 1
      (halted (a "radix-digit:demo-outcome") receiptNil) = [] := by
  decide +kernel

/-- The independently authored closed primitive catalog justifies the same
jump behavior at the mathematical machine layer. -/
theorem closed_jump_primitive :
    executePrimitive radixTwo 0 [] [] [] (.jump 1) =
      .next [] [] 1 [] := by
  rfl

#print axioms jump_native_crossing
#print axioms radixDigit_galois
#print axioms jump_step_exact
#print axioms closed_jump_primitive

end Mettapedia.GSLT.LanguageDef.RadixDigitNTT
