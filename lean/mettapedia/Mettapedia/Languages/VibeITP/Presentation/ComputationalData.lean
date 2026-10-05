import Mettapedia.Languages.VibeITP.Spec.Basic
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.NaturalData

/-!
# Vibe terms in the shared computational presentation

Fresh symbol identifiers and indices are unbounded natural data, and literal bytes are checked
at the byte boundary. Word-operation bounds belong to the kernel operations,
not to this lossless term encoding. In particular an early-exit operation may
preserve a term whose index is larger than a machine word.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalData

open Spec
open Mettapedia.GSLT.LanguageDef

def encodeByte (byte : UInt8) : DeterministicEquations.Term :=
  DeterministicEquations.natural byte.toNat

def decodeByte (value : DeterministicEquations.Term) : Option UInt8 := do
  let index ← DeterministicEquations.natural? value
  if index < 256 then some (UInt8.ofNat index) else none

@[simp] theorem decode_encodeByte (byte : UInt8) : decodeByte (encodeByte byte) = some byte := by
  have bound : byte.toNat < 256 := byte.toNat_lt
  simp [encodeByte, decodeByte, bound]

def decodeBytes : List DeterministicEquations.Term → Option (List UInt8)
  | [] => some []
  | first :: rest => do
      let byte ← decodeByte first
      let bytes ← decodeBytes rest
      pure (byte :: bytes)

@[simp] theorem decode_encodedBytes (bytes : List UInt8) :
    decodeBytes (bytes.map encodeByte) = some bytes := by
  induction bytes with
  | nil => rfl
  | cons first rest ih => simp [decodeBytes, ih]

def decodeBuiltin : Nat → Option Builtin
  | 2 => some .impl
  | 3 => some .eq
  | 4 => some .litIsNat
  | 5 => some .litLt
  | 6 => some .litAdd
  | 7 => some .litMul
  | 8 => some .litDiv
  | 9 => some .litLength
  | 10 => some .litGet
  | 11 => some .isSafeCode
  | 12 => some .executedTo
  | _ => none

def encodeSymbol : SymId → DeterministicEquations.Term
  | .builtin symbol => .list [.sym "Builtin", DeterministicEquations.natural symbol.slot]
  | .fresh index => .list [.sym "Fresh", DeterministicEquations.natural index]

def decodeSymbol : DeterministicEquations.Term → Option SymId
  | .list [.sym "Builtin", value] => do
      let index ← DeterministicEquations.natural? value
      let symbol ← decodeBuiltin index
      pure (.builtin symbol)
  | .list [.sym "Fresh", value] => (DeterministicEquations.natural? value).map SymId.fresh
  | _ => none

@[simp] theorem decode_encodeSymbol (symbol : SymId) :
    decodeSymbol (encodeSymbol symbol) = some symbol := by
  cases symbol with
  | builtin symbol => cases symbol <;> simp [encodeSymbol, decodeSymbol, Builtin.slot, decodeBuiltin]
  | fresh index => simp [encodeSymbol, decodeSymbol]

theorem encodedSymbol_passive (P : DeterministicEquations.Program)
    (H : DeterministicEquations.Host) (symbol : SymId) :
    DeterministicEquations.PassiveData P H (encodeSymbol symbol) := by
  cases symbol <;> apply DeterministicEquations.PassiveData.list <;>
    intro value member <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at member <;>
    rcases member with rfl | rfl
  · exact .sym _
  · exact DeterministicEquations.natural_passive _ _ _
  · exact .sym _
  · exact DeterministicEquations.natural_passive _ _ _

mutual
def encode : Term → DeterministicEquations.Term
  | .bvar index => .expr [.sym "Vibe:BVar", DeterministicEquations.natural index]
  | .lit bytes => .expr [.sym "Vibe:Lit", .list (bytes.map encodeByte)]
  | .app symbol arguments =>
      .expr [.sym "Vibe:App", encodeSymbol symbol, .list (encodeTerms arguments)]

def encodeTerms : List Term → List DeterministicEquations.Term
  | [] => []
  | first :: rest => encode first :: encodeTerms rest
end

mutual
def decode : DeterministicEquations.Term → Option Term
  | .expr [.sym "Vibe:BVar", index] => (DeterministicEquations.natural? index).map Term.bvar
  | .expr [.sym "Vibe:Lit", .list bytes] => (decodeBytes bytes).map Term.lit
  | .expr [.sym "Vibe:App", symbol, .list arguments] => do
      let symbol' ← decodeSymbol symbol
      let arguments' ← decodeTerms arguments
      pure (.app symbol' arguments')
  | _ => none

def decodeTerms : List DeterministicEquations.Term → Option (List Term)
  | [] => some []
  | first :: rest => do
      let term ← decode first
      let terms ← decodeTerms rest
      pure (term :: terms)
end

mutual
@[simp] theorem decode_encode (term : Term) : decode (encode term) = some term := by
  cases term with
  | bvar index => simp [encode, decode]
  | lit bytes => simp [encode, decode]
  | app symbol arguments => simp [encode, decode, decode_encodeTerms arguments]

@[simp] theorem decode_encodeTerms (terms : List Term) :
    decodeTerms (encodeTerms terms) = some terms := by
  cases terms with
  | nil => rfl
  | cons first rest => simp [encodeTerms, decodeTerms, decode_encode first, decode_encodeTerms rest]
end

theorem encode_injective : Function.Injective encode := by
  intro first second same
  have decoded := congrArg decode same
  simpa using decoded

def constructorHeads : List String := ["Vibe:BVar", "Vibe:Lit", "Vibe:App"]

structure DataSeparated (P : DeterministicEquations.Program) (H : DeterministicEquations.Host) : Prop where
  undefined : ∀ head ∈ constructorHeads, P.defines head = false
  unhandled : ∀ head ∈ constructorHeads, ∀ arguments, H.primitive head arguments = .unhandled

mutual
theorem encoded_passive {P : DeterministicEquations.Program} {H : DeterministicEquations.Host}
    (separated : DataSeparated P H) (term : Term) :
    DeterministicEquations.PassiveData P H (encode term) := by
  cases term with
  | bvar index =>
      apply DeterministicEquations.PassiveData.node
      · simp [DeterministicEquations.Special]
      · exact separated.undefined _ (by simp [constructorHeads])
      · exact separated.unhandled _ (by simp [constructorHeads]) _
      · intro argument member
        have same := List.mem_singleton.mp member
        subst argument
        exact DeterministicEquations.natural_passive _ _ _
  | lit bytes =>
      apply DeterministicEquations.PassiveData.node
      · simp [DeterministicEquations.Special]
      · exact separated.undefined _ (by simp [constructorHeads])
      · exact separated.unhandled _ (by simp [constructorHeads]) _
      · intro argument member
        have same := List.mem_singleton.mp member
        subst argument
        apply DeterministicEquations.PassiveData.list
        intro value member
        obtain ⟨byte, _, rfl⟩ := List.mem_map.mp member
        exact DeterministicEquations.natural_passive _ _ _
  | app symbol arguments =>
      apply DeterministicEquations.PassiveData.node
      · simp [DeterministicEquations.Special]
      · exact separated.undefined _ (by simp [constructorHeads])
      · exact separated.unhandled _ (by simp [constructorHeads]) _
      · intro value member
        simp at member
        rcases member with rfl | rfl
        · exact encodedSymbol_passive _ _ _
        · exact .list (encodedTerms_passive separated arguments)

theorem encodedTerms_passive {P : DeterministicEquations.Program} {H : DeterministicEquations.Host}
    (separated : DataSeparated P H) (terms : List Term) :
    ∀ value ∈ encodeTerms terms, DeterministicEquations.PassiveData P H value := by
  cases terms with
  | nil => simp [encodeTerms]
  | cons first rest =>
      intro value member
      simp only [encodeTerms, List.mem_cons] at member
      rcases member with rfl | tail
      · exact encoded_passive separated first
      · exact encodedTerms_passive separated rest value tail
end

theorem encoded_evaluation {P : DeterministicEquations.Program} {H : DeterministicEquations.Host}
    (separated : DataSeparated P H) (term : Term) (environment : DeterministicEquations.Env)
    (fuel : Nat) (enough : sizeOf (encode term) < fuel) :
    DeterministicEquations.eval P H fuel environment (encode term) = .value (encode term) :=
  (encoded_passive separated term).eval_eq_value environment fuel enough

theorem oversized_byte_refuses : decodeByte (DeterministicEquations.natural 256) = none := by
  simp [decodeByte]

theorem large_index_roundtrip : decode (encode (.bvar 18446744073709551616)) =
    some (.bvar 18446744073709551616) := decode_encode _

theorem mm0_tag_is_not_vibe_data :
    decode (.expr [.sym "MM0:Var", DeterministicEquations.natural 0]) = none := rfl

end Mettapedia.Languages.VibeITP.Presentation.ComputationalData
