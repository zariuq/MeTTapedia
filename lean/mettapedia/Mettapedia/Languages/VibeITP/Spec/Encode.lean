import Mettapedia.Languages.VibeITP.Spec.Instr

/-!
# Vibe-ITP specification: printing certificates

The shortest encoding of words and the printing of instructions.  Printing is
a section of decoding: decoding a printed instruction stream returns it
(`decodeFile_encodeFile`), provided every operand is a machine word.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Spec

/-- Number of payload bytes needed below `256 ^ fuel`. -/
def byteLenAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else 1 + byteLenAux fuel (n / 256)

/-- Payload bytes of the shortest encoding of a word above 247. -/
def byteLen (n : Nat) : Nat := byteLenAux 8 n

/-- Shortest variable-length encoding of a word. -/
def encodeWord (n : Nat) : List UInt8 :=
  if n ≤ 247 then [UInt8.ofNat n]
  else UInt8.ofNat (247 + byteLen n) :: leBytes (byteLen n) n

def encodeWords (ns : List Nat) : List UInt8 := ns.flatMap encodeWord

def encodeCounted (ns : List Nat) : List UInt8 :=
  encodeWord ns.length ++ encodeWords ns

/-- Opcode byte of an instruction. -/
def Instr.opcode : Instr → Nat
  | .fvarNew .. => 0
  | .constNew .. => 1
  | .symbolSwap .. => 2
  | .symbolFree .. => 3
  | .termNewBVar .. => 4
  | .termNewLiteral .. => 5
  | .termNewApp .. => 6
  | .termSwap .. => 7
  | .termFree .. => 8
  | .addAxiom .. => 9
  | .thmExchange .. => 10
  | .thmFree .. => 11
  | .thmSwap .. => 12
  | .challengeAdd .. => 13
  | .challengeSatisfy .. => 14
  | .modusPonens .. => 15
  | .thmInstantiate .. => 16
  | .defineConst .. => 17
  | .litIsNat .. => 18
  | .litLt .. => 19
  | .litAdd .. => 20
  | .litMul .. => 21
  | .litDiv .. => 22
  | .litLength .. => 23
  | .litGet .. => 24
  | .jit .. => 25

/-- Printed operands of an instruction. -/
def Instr.payload : Instr → List UInt8
  | .fvarNew a d => encodeWords [a, d]
  | .constNew bs d => encodeCounted bs ++ encodeWord d
  | .symbolSwap i j => encodeWords [i, j]
  | .symbolFree i => encodeWord i
  | .termNewBVar i d => encodeWords [i, d]
  | .termNewLiteral bytes d => encodeWord bytes.length ++ bytes ++ encodeWord d
  | .termNewApp s args d => encodeWord s ++ encodeCounted args ++ encodeWord d
  | .termSwap i j => encodeWords [i, j]
  | .termFree i => encodeWord i
  | .addAxiom t d => encodeWords [t, d]
  | .thmExchange h t => encodeWords [h, t]
  | .thmFree i => encodeWord i
  | .thmSwap i j => encodeWords [i, j]
  | .challengeAdd t d => encodeWords [t, d]
  | .challengeSatisfy c h => encodeWords [c, h]
  | .modusPonens a b d => encodeWords [a, b, d]
  | .thmInstantiate h f v d => encodeWords [h, f, v, d]
  | .defineConst fvars hints v ds dt =>
      encodeCounted fvars ++ encodeCounted hints ++ encodeWords [v, ds, dt]
  | .litIsNat n d => encodeWords [n, d]
  | .litLt a b d => encodeWords [a, b, d]
  | .litAdd a b d => encodeWords [a, b, d]
  | .litMul a b d => encodeWords [a, b, d]
  | .litDiv a b d => encodeWords [a, b, d]
  | .litLength t d => encodeWords [t, d]
  | .litGet t i d => encodeWords [t, i, d]
  | .jit s d o => encodeWords [s, d, o]

def encodeInstr (instr : Instr) : List UInt8 :=
  UInt8.ofNat instr.opcode :: instr.payload

def encodeFile (instrs : List Instr) : List UInt8 := instrs.flatMap encodeInstr

/-- Every integer an instruction prints, counts and lengths included. -/
def Instr.words : Instr → List Nat
  | .fvarNew a d => [a, d]
  | .constNew bs d => bs.length :: bs ++ [d]
  | .symbolSwap i j => [i, j]
  | .symbolFree i => [i]
  | .termNewBVar i d => [i, d]
  | .termNewLiteral bytes d => [bytes.length, d]
  | .termNewApp s args d => s :: args.length :: args ++ [d]
  | .termSwap i j => [i, j]
  | .termFree i => [i]
  | .addAxiom t d => [t, d]
  | .thmExchange h t => [h, t]
  | .thmFree i => [i]
  | .thmSwap i j => [i, j]
  | .challengeAdd t d => [t, d]
  | .challengeSatisfy c h => [c, h]
  | .modusPonens a b d => [a, b, d]
  | .thmInstantiate h f v d => [h, f, v, d]
  | .defineConst fvars hints v ds dt =>
      fvars.length :: fvars ++ hints.length :: hints ++ [v, ds, dt]
  | .litIsNat n d => [n, d]
  | .litLt a b d => [a, b, d]
  | .litAdd a b d => [a, b, d]
  | .litMul a b d => [a, b, d]
  | .litDiv a b d => [a, b, d]
  | .litLength t d => [t, d]
  | .litGet t i d => [t, i, d]
  | .jit s d o => [s, d, o]

/-- An instruction is printable when all its integers are machine words. -/
def Instr.Bounded (instr : Instr) : Prop := ∀ w ∈ instr.words, w < wordBound

/-! ## Decoding printed certificates -/

open Parser

theorem le_leBytes : ∀ (k n : Nat) (rest : List UInt8), n < 256 ^ k →
    Parser.le k (leBytes k n ++ rest) = .ok (n, rest)
  | 0, n, rest, h => by simp at h; subst h; rfl
  | k + 1, n, rest, h => by
      have ih := le_leBytes k (n / 256) rest (by
        rw [Nat.pow_succ] at h; omega)
      simp only [leBytes, List.cons_append, Parser.le, Parser.bind, ih, Parser.pure]
      simp
      omega

theorem byteLenAux_bound : ∀ (fuel n : Nat), n < 256 ^ fuel →
    n < 256 ^ byteLenAux fuel n ∧ byteLenAux fuel n ≤ fuel
  | 0, n, h => by simp [byteLenAux] at h ⊢; exact h
  | fuel + 1, n, h => by
      simp only [byteLenAux]
      split
      · simp_all
      · have ih := byteLenAux_bound fuel (n / 256) (by rw [Nat.pow_succ] at h; omega)
        constructor
        · rw [Nat.add_comm, Nat.pow_succ]; omega
        · omega

theorem byteLenAux_pos : ∀ (fuel n : Nat), 0 < fuel → 0 < n → 0 < byteLenAux fuel n
  | 0, _, h, _ => by omega
  | fuel + 1, n, _, hn => by simp only [byteLenAux]; split <;> omega

theorem word_encodeWord (n : Nat) (rest : List UInt8) (h : n < wordBound) :
    word (encodeWord n ++ rest) = .ok (n, rest) := by
  unfold encodeWord
  split
  · rename_i hle
    simp only [List.singleton_append, word]
    have : (UInt8.ofNat n).toNat = n := by simp; omega
    simp [this, hle]
  · rename_i hgt
    have hb := byteLenAux_bound 8 n (by simpa [wordBound] using h)
    have hpos := byteLenAux_pos 8 n (by omega) (by omega)
    have hbl : byteLen n = byteLenAux 8 n := rfl
    rw [hbl]
    simp only [List.cons_append, word]
    have hk : (UInt8.ofNat (247 + byteLenAux 8 n)).toNat = 247 + byteLenAux 8 n := by
      simp; omega
    rw [hk, if_neg (by omega), show 247 + byteLenAux 8 n - 247 = byteLenAux 8 n by omega]
    exact le_leBytes _ _ _ hb.1

theorem words_encodeWords : ∀ (ns : List Nat) (rest : List UInt8),
    (∀ n ∈ ns, n < wordBound) → words ns.length (encodeWords ns ++ rest) = .ok (ns, rest)
  | [], rest, _ => rfl
  | n :: ns, rest, h => by
      simp only [List.length_cons, words, encodeWords, List.flatMap_cons, List.append_assoc]
      simp only [Parser.bind]
      rw [word_encodeWord n _ (h n (by simp))]
      simp only
      have := words_encodeWords ns rest (fun m hm => h m (by simp [hm]))
      simp only [encodeWords] at this
      rw [this]
      rfl

theorem counted_encodeCounted (ns : List Nat) (rest : List UInt8)
    (hlen : ns.length < wordBound) (h : ∀ n ∈ ns, n < wordBound) :
    counted (encodeCounted ns ++ rest) = .ok (ns, rest) := by
  simp only [counted, encodeCounted, List.append_assoc, Parser.bind]
  rw [word_encodeWord _ _ hlen]
  exact words_encodeWords ns rest h

theorem raw_self (bytes rest : List UInt8) :
    raw bytes.length (bytes ++ rest) = .ok (bytes, rest) := by
  simp [raw]

theorem bind_ok {α β : Type} {p : Parser α} {f : α → Parser β} {bytes : List UInt8}
    {a : α} {rest : List UInt8} (h : p bytes = .ok (a, rest)) :
    Parser.bind p f bytes = f a rest := by
  simp [Parser.bind, h]

theorem decodeOperands_payload (instr : Instr) (rest : List UInt8)
    (h : instr.Bounded) :
    decodeOperands instr.opcode (instr.payload ++ rest) = .ok (instr, rest) := by
  have hw : ∀ w ∈ instr.words, w < wordBound := h
  cases instr <;>
    simp only [Instr.words, List.mem_cons, List.mem_append,
      forall_eq_or_imp, List.not_mem_nil] at hw <;>
    simp only [Instr.opcode, Instr.payload, decodeOperands, encodeWords,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  all_goals
    repeat (first
      | rw [bind_ok (word_encodeWord _ _ (by first | omega | simp_all))]
      | rw [bind_ok (counted_encodeCounted _ _ (by first | omega | simp_all)
          (by intro n hn; first | simp_all | omega))]
      | rw [bind_ok (raw_self _ _)])
  all_goals rfl

theorem decodeStream_encodeFile : ∀ (instrs : List Instr) (fuel : Nat),
    (∀ i ∈ instrs, i.Bounded) → (encodeFile instrs).length ≤ fuel →
      decodeStream fuel (encodeFile instrs) = .ok instrs
  | [], fuel, _, _ => by cases fuel <;> rfl
  | i :: is, fuel, h, hf => by
      cases fuel with
      | zero => simp [encodeFile, encodeInstr] at hf
      | succ fuel =>
          simp only [encodeFile, List.flatMap_cons, encodeInstr, List.cons_append]
          simp only [decodeStream]
          have hop : (UInt8.ofNat i.opcode).toNat = i.opcode := by
            cases i <;> simp [Instr.opcode]
          rw [hop, decodeOperands_payload i _ (h i (by simp))]
          simp only
          have ih := decodeStream_encodeFile is fuel (fun j hj => h j (by simp [hj]))
            (by simp [encodeFile, encodeInstr] at hf ⊢; omega)
          simp only [encodeFile] at ih
          rw [ih]

/-- Printing is a section of decoding on printable instruction streams. -/
theorem decodeFile_encodeFile (instrs : List Instr) (h : ∀ i ∈ instrs, i.Bounded) :
    decodeFile (encodeFile instrs) = .ok instrs :=
  decodeStream_encodeFile instrs _ h (Nat.le_refl _)

end Mettapedia.Languages.VibeITP.Spec
