import Mettapedia.GSLT.LanguageDef.OracleRealization
import Mettapedia.Languages.VibeITP.Presentation.Package
import Mettapedia.Languages.VibeITP.Presentation.Decode

/-!
# Vibe word arithmetic as a specified oracle library

Vibe's kernel computes literal addition, multiplication and division with C
`uint64_t` arithmetic. Here the three operations are an admitted oracle library
over the Vibe kernel's data sort. Their meaning is natural-number arithmetic on
machine words: addition and multiplication modulo `2^64`, division with zero
refused. The backend model is 64-bit wrapping bit-vector arithmetic, which is
how the C standard specifies unsigned arithmetic. The realization meets the
meaning in that model.

Agreement of the compiled C code with this model is not proved here; it is the
remaining implementation dependency of these operations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.WordOracle

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.OracleExtension
open Mettapedia.GSLT.LanguageDef.OracleRealization
open Mettapedia.GSLT.LanguageDef.RuleSchemaArityProjection
open Mettapedia.Languages.VibeITP.Spec
open Mettapedia.Languages.VibeITP.Presentation

/-- The base language of the Vibe kernel. -/
def vibeLanguage : LanguageDef := cacheLanguage kernelProfile constructorArities

def dataType : TypeExpr := .base "VibeData"

def addDecl : OracleDecl := ⟨"vibe:lit-add", [dataType, dataType], dataType⟩
def mulDecl : OracleDecl := ⟨"vibe:lit-mul", [dataType, dataType], dataType⟩
def divDecl : OracleDecl := ⟨"vibe:lit-div", [dataType, dataType], dataType⟩

/-- The admitted word-arithmetic library. -/
def library : AdmittedLibrary vibeLanguage :=
  ⟨[addDecl, mulDecl, divDecl], by decide⟩

/-- The backend operations. -/
inductive WordOp where
  | add
  | mul
  | div
  deriving DecidableEq

/-- The natural-number meaning of an operation on words. -/
def value : WordOp → Nat → Nat → Option Nat
  | .add, a, b => some ((a + b) % wordBound)
  | .mul, a, b => some ((a * b) % wordBound)
  | .div, a, b => if b = 0 then none else some (a / b)

/-- Each declaration is realized by its operation. -/
def opOf (declaration : OracleDecl) : WordOp :=
  if declaration = addDecl then .add else if declaration = mulDecl then .mul else .div

def realization : NativeRealization vibeLanguage library WordOp where
  implementation declaration := opOf declaration.1

/-- The 64-bit bit-vector operation. -/
def bitVecValue : WordOp → BitVec 64 → BitVec 64 → Option (BitVec 64)
  | .add, x, y => some (x + y)
  | .mul, x, y => some (x * y)
  | .div, x, y => if y = 0 then none else some (x / y)

/-- **The backend model**: decode two numerals, check that they are words, and
compute with 64-bit bit vectors. -/
def wordModel : BackendModel WordOp where
  run op arguments :=
    match arguments with
    | [first, second] =>
        match decNat first, decNat second with
        | some a, some b =>
            if a < wordBound ∧ b < wordBound then
              (bitVecValue op (BitVec.ofNat 64 a) (BitVec.ofNat 64 b)).map
                fun result => encNat result.toNat
            else none
        | _, _ => none
    | _ => none

/-- **The meaning of the library**: on two word numerals, the natural-number
arithmetic of the declaration. -/
def meaning : Meaning library where
  relates declaration arguments result :=
    ∃ a b c, a < wordBound ∧ b < wordBound ∧ arguments = [encNat a, encNat b] ∧
      value (opOf declaration.1) a b = some c ∧ result = encNat c

theorem wordBound_eq : wordBound = 2 ^ 64 := rfl

/-- On words, bit-vector arithmetic is the natural-number meaning. -/
theorem bitVecValue_toNat (op : WordOp) {a b : Nat} (aWord : a < wordBound)
    (bWord : b < wordBound) :
    (bitVecValue op (BitVec.ofNat 64 a) (BitVec.ofNat 64 b)).map BitVec.toNat = value op a b := by
  have aMod : a % 18446744073709551616 = a := Nat.mod_eq_of_lt aWord
  have bMod : b % 18446744073709551616 = b := Nat.mod_eq_of_lt bWord
  cases op with
  | add => simp [bitVecValue, value, BitVec.toNat_add, wordBound_eq]
  | mul => simp [bitVecValue, value, BitVec.toNat_mul, wordBound_eq]
  | div =>
      by_cases zero : b = 0
      · subst zero
        simp [bitVecValue, value]
      · have nonzero : ¬ BitVec.ofNat 64 b = 0#64 := by
          intro same
          have := congrArg BitVec.toNat same
          simp only [BitVec.toNat_ofNat] at this
          rw [Nat.pow_succ] at this
          exact zero (by simpa [bMod] using this)
        simp [bitVecValue, value, zero, nonzero, BitVec.toNat_udiv, aMod, bMod]

/-- **The realization meets the meaning** in the bit-vector model. -/
theorem meets : Meets realization wordModel meaning := by
  intro declaration arguments result
  change wordModel.run (opOf declaration.1) arguments = some result ↔ _
  constructor
  · intro returned
    match arguments, returned with
    | [first, second], returned =>
        simp only [wordModel] at returned
        cases firstValue : decNat first with
        | none => simp [firstValue] at returned
        | some a =>
            cases secondValue : decNat second with
            | none => simp [firstValue, secondValue] at returned
            | some b =>
                simp only [firstValue, secondValue] at returned
                by_cases words : a < wordBound ∧ b < wordBound
                · rw [if_pos words] at returned
                  obtain ⟨vector, computed, rfl⟩ := Option.map_eq_some_iff.mp returned
                  have meaningOf := bitVecValue_toNat (opOf declaration.1) words.1 words.2
                  rw [computed, Option.map_some] at meaningOf
                  exact ⟨a, b, vector.toNat, words.1, words.2,
                    by rw [(decNat_eq_iff first a).mp firstValue, (decNat_eq_iff second b).mp secondValue],
                    meaningOf.symm, rfl⟩
                · rw [if_neg words] at returned
                  cases returned
  · rintro ⟨a, b, c, aWord, bWord, rfl, valued, rfl⟩
    simp only [wordModel, decNat_encNat, if_pos (And.intro aWord bWord)]
    have meaningOf := bitVecValue_toNat (opOf declaration.1) aWord bWord
    rw [valued] at meaningOf
    obtain ⟨vector, computed, same⟩ := Option.map_eq_some_iff.mp meaningOf
    rw [computed, Option.map_some, same]

/-! ## Controls -/

/-- A realization that adds without wrapping. -/
def unwrappedModel : BackendModel WordOp where
  run op arguments :=
    match op, arguments with
    | .add, [first, second] =>
        match decNat first, decNat second with
        | some a, some b => some (encNat (a + b))
        | _, _ => none
    | _, _ => wordModel.run op arguments

def addAdmitted : Admitted library := ⟨addDecl, by decide⟩

/-- **Unwrapped addition does not meet the meaning**: at the largest word plus
one it returns `2^64`, which is not the wrapped sum. -/
theorem unwrapped_fails : ¬ Meets realization unwrappedModel meaning := by
  apply not_meets_of_wrong_result (declaration := addAdmitted)
    (arguments := [encNat (wordBound - 1), encNat 1]) (result := encNat wordBound)
  · simp [unwrappedModel, realization, addAdmitted, opOf, decNat_encNat, wordBound_eq]
  · rintro ⟨a, b, c, _, _, same, valued, sameResult⟩
    simp only [List.cons.injEq, and_true] at same
    have aEq := encNat_inj same.1.symm
    have bEq := encNat_inj same.2.symm
    have cEq := encNat_inj sameResult
    subst aEq bEq
    simp only [addAdmitted, opOf, ↓reduceIte, value, Option.some.injEq] at valued
    rw [← valued] at cEq
    simp [wordBound_eq] at cEq

end Mettapedia.Languages.VibeITP.Native.WordOracle
