import Mettapedia.Languages.VibeITP.Spec.Basic

/-!
# Vibe-ITP specification: certificate syntax

A certificate file is a stream of instructions: one opcode byte followed by
its operands.  Integers are variable-length words: a first byte up to 247 is
the value itself; a first byte `247 + k` announces `k` little-endian payload
bytes (`1 ≤ k ≤ 8`).  Non-shortest encodings are accepted, as by the reference
checker.  Byte strings are a length followed by exactly that many raw bytes.
Counts announce the number of operands that follow.

Decoding stops at the first malformed instruction.  The reference checker
reads every file completely before executing any instruction, so a malformed
file is reported before any semantic error of an earlier file.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Spec

/-- One checker instruction with its operands in stream order.  Slot operands
index the symbol, term, theorem, or challenge slot space of their role. -/
inductive Instr where
  | fvarNew (arity dst : Nat)
  | constNew (binders : List Nat) (dst : Nat)
  | symbolSwap (i j : Nat)
  | symbolFree (i : Nat)
  | termNewBVar (index dst : Nat)
  | termNewLiteral (bytes : List UInt8) (dst : Nat)
  | termNewApp (symbol : Nat) (args : List Nat) (dst : Nat)
  | termSwap (i j : Nat)
  | termFree (i : Nat)
  | addAxiom (statement dst : Nat)
  | thmExchange (thm term : Nat)
  | thmFree (i : Nat)
  | thmSwap (i j : Nat)
  | challengeAdd (statement dst : Nat)
  | challengeSatisfy (challenge thm : Nat)
  | modusPonens (impl premise dst : Nat)
  | thmInstantiate (thm fvar value dst : Nat)
  | defineConst (fvars hints : List Nat) (value dstSymbol dstThm : Nat)
  | litIsNat (n dst : Nat)
  | litLt (a b dst : Nat)
  | litAdd (a b dst : Nat)
  | litMul (a b dst : Nat)
  | litDiv (a b dst : Nat)
  | litLength (term dst : Nat)
  | litGet (term index dst : Nat)
  | jit (safe dst dstTerm : Nat)
deriving DecidableEq, Repr

/-- Decoding failures, matching the reference checker's syntax errors. -/
inductive DecodeError where
  /-- A variable-length integer ends before its payload. -/
  | truncatedInteger
  /-- A byte string ends before its announced length. -/
  | truncatedBytes
  /-- An opcode byte outside `0..25`. -/
  | unknownOpcode (byte : Nat)
deriving DecidableEq, Repr

/-- A byte-stream parser: consumed prefix interpreted, remaining suffix
returned. -/
def Parser (α : Type) : Type := List UInt8 → Except DecodeError (α × List UInt8)

namespace Parser

def pure {α : Type} (a : α) : Parser α := fun bytes => .ok (a, bytes)

def fail {α : Type} (e : DecodeError) : Parser α := fun _ => .error e

def bind {α β : Type} (p : Parser α) (f : α → Parser β) : Parser β := fun bytes =>
  match p bytes with
  | .error e => .error e
  | .ok (a, rest) => f a rest

/-- Read `count` little-endian payload bytes. -/
def le : Nat → Parser Nat
  | 0 => pure 0
  | count + 1 => fun bytes =>
      match bytes with
      | [] => .error .truncatedInteger
      | b :: rest => bind (le count) (fun high => pure (b.toNat + 256 * high)) rest

/-- Read one variable-length integer. -/
def word : Parser Nat := fun bytes =>
  match bytes with
  | [] => .error .truncatedInteger
  | b :: rest => if b.toNat ≤ 247 then .ok (b.toNat, rest) else le (b.toNat - 247) rest

/-- Read `count` variable-length integers. -/
def words : Nat → Parser (List Nat)
  | 0 => pure []
  | count + 1 => bind word fun w => bind (words count) fun ws => pure (w :: ws)

/-- Read exactly `count` raw bytes. -/
def raw (count : Nat) : Parser (List UInt8) := fun bytes =>
  if bytes.length < count then .error .truncatedBytes
  else .ok (bytes.take count, bytes.drop count)

/-- Read a count followed by that many integers. -/
def counted : Parser (List Nat) := bind word words

/-- A parser never returns a longer suffix than its input. -/
def Consumes {α : Type} (p : Parser α) : Prop :=
  ∀ bytes a rest, p bytes = .ok (a, rest) → rest.length ≤ bytes.length

theorem pure_consumes {α : Type} (a : α) : (pure a).Consumes := by
  intro bytes a' rest h
  simp only [pure, Except.ok.injEq, Prod.mk.injEq] at h
  rw [← h.2]; exact Nat.le_refl _

theorem fail_consumes {α : Type} (e : DecodeError) : (fail (α := α) e).Consumes := by
  intro bytes a rest h
  simp [fail] at h

theorem bind_consumes {α β : Type} {p : Parser α} {f : α → Parser β}
    (hp : p.Consumes) (hf : ∀ a, (f a).Consumes) : (bind p f).Consumes := by
  intro bytes b rest h
  simp only [bind] at h
  split at h
  · simp at h
  · rename_i a mid hmid
    exact Nat.le_trans (hf a mid b rest h) (hp bytes a mid hmid)

theorem le_consumes : ∀ count, (le count).Consumes
  | 0 => pure_consumes 0
  | count + 1 => by
      intro bytes a rest h
      cases bytes with
      | nil => simp [le] at h
      | cons b bs =>
          simp only [le] at h
          have := bind_consumes (le_consumes count)
            (fun high => pure_consumes (b.toNat + 256 * high)) bs a rest h
          simp only [List.length_cons]; omega

theorem word_consumes : word.Consumes := by
  intro bytes a rest h
  cases bytes with
  | nil => simp [word] at h
  | cons b bs =>
      simp only [word] at h
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]; simp
      · have := le_consumes _ bs a rest h
        simp only [List.length_cons]; omega

/-- A word always consumes at least its first byte. -/
theorem word_strict (bytes : List UInt8) (a : Nat) (rest : List UInt8)
    (h : word bytes = .ok (a, rest)) : rest.length < bytes.length := by
  cases bytes with
  | nil => simp [word] at h
  | cons b bs =>
      simp only [word] at h
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]; simp
      · have := le_consumes _ bs a rest h
        simp only [List.length_cons]; omega

theorem words_consumes : ∀ count, (words count).Consumes
  | 0 => pure_consumes []
  | count + 1 =>
      bind_consumes word_consumes fun _ =>
        bind_consumes (words_consumes count) fun _ => pure_consumes _

theorem raw_consumes (count : Nat) : (raw count).Consumes := by
  intro bytes a rest h
  simp only [raw] at h
  split at h
  · simp at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]; simp

theorem counted_consumes : counted.Consumes :=
  bind_consumes word_consumes words_consumes

end Parser

open Parser in
/-- Operands of one opcode, in stream order. -/
def decodeOperands : Nat → Parser Instr
  | 0 => bind word fun a => bind word fun d => pure (.fvarNew a d)
  | 1 => bind counted fun bs => bind word fun d => pure (.constNew bs d)
  | 2 => bind word fun i => bind word fun j => pure (.symbolSwap i j)
  | 3 => bind word fun i => pure (.symbolFree i)
  | 4 => bind word fun i => bind word fun d => pure (.termNewBVar i d)
  | 5 => bind word fun len => bind (raw len) fun bytes => bind word fun d =>
      pure (.termNewLiteral bytes d)
  | 6 => bind word fun s => bind counted fun args => bind word fun d =>
      pure (.termNewApp s args d)
  | 7 => bind word fun i => bind word fun j => pure (.termSwap i j)
  | 8 => bind word fun i => pure (.termFree i)
  | 9 => bind word fun t => bind word fun d => pure (.addAxiom t d)
  | 10 => bind word fun h => bind word fun t => pure (.thmExchange h t)
  | 11 => bind word fun i => pure (.thmFree i)
  | 12 => bind word fun i => bind word fun j => pure (.thmSwap i j)
  | 13 => bind word fun t => bind word fun d => pure (.challengeAdd t d)
  | 14 => bind word fun c => bind word fun h => pure (.challengeSatisfy c h)
  | 15 => bind word fun a => bind word fun b => bind word fun d =>
      pure (.modusPonens a b d)
  | 16 => bind word fun h => bind word fun f => bind word fun v => bind word fun d =>
      pure (.thmInstantiate h f v d)
  | 17 => bind counted fun fvars => bind counted fun hints => bind word fun v =>
      bind word fun ds => bind word fun dt => pure (.defineConst fvars hints v ds dt)
  | 18 => bind word fun n => bind word fun d => pure (.litIsNat n d)
  | 19 => bind word fun a => bind word fun b => bind word fun d => pure (.litLt a b d)
  | 20 => bind word fun a => bind word fun b => bind word fun d => pure (.litAdd a b d)
  | 21 => bind word fun a => bind word fun b => bind word fun d => pure (.litMul a b d)
  | 22 => bind word fun a => bind word fun b => bind word fun d => pure (.litDiv a b d)
  | 23 => bind word fun t => bind word fun d => pure (.litLength t d)
  | 24 => bind word fun t => bind word fun i => bind word fun d => pure (.litGet t i d)
  | 25 => bind word fun s => bind word fun d => bind word fun o => pure (.jit s d o)
  | other => fail (.unknownOpcode other)

open Parser in
theorem decodeOperands_consumes (opcode : Nat) : (decodeOperands opcode).Consumes := by
  unfold decodeOperands
  split
  all_goals
    repeat' (first
      | exact pure_consumes _
      | exact fail_consumes _
      | exact word_consumes
      | exact counted_consumes
      | exact raw_consumes _
      | refine bind_consumes ?_ fun _ => ?_)

/-- Decode instructions until the input ends.  Every instruction consumes its
opcode byte, so `fuel = bytes.length` suffices (`decodeStream_fuel`). -/
def decodeStream : Nat → List UInt8 → Except DecodeError (List Instr)
  | _, [] => .ok []
  | 0, _ :: _ => .ok []
  | fuel + 1, op :: rest =>
      match decodeOperands op.toNat rest with
      | .error e => .error e
      | .ok (instr, rest') =>
          match decodeStream fuel rest' with
          | .error e => .error e
          | .ok instrs => .ok (instr :: instrs)

/-- Decode one certificate file. -/
def decodeFile (bytes : List UInt8) : Except DecodeError (List Instr) :=
  decodeStream bytes.length bytes

/-- Any fuel at least the input length yields the same decoding: the fuel
never runs out before the input does. -/
theorem decodeStream_fuel : ∀ (fuel fuel' : Nat) (bytes : List UInt8),
    bytes.length ≤ fuel → bytes.length ≤ fuel' →
      decodeStream fuel bytes = decodeStream fuel' bytes
  | fuel, fuel', [], _, _ => by
      cases fuel <;> cases fuel' <;> simp [decodeStream]
  | 0, _, _ :: _, h, _ => by simp at h
  | _, 0, _ :: _, _, h => by simp at h
  | fuel + 1, fuel' + 1, op :: rest, h, h' => by
      simp only [decodeStream]
      split
      · rfl
      · rename_i instr rest' hop
        have hc := decodeOperands_consumes op.toNat rest instr rest' hop
        simp only [List.length_cons] at h h'
        rw [decodeStream_fuel fuel fuel' rest' (by omega) (by omega)]

end Mettapedia.Languages.VibeITP.Spec
