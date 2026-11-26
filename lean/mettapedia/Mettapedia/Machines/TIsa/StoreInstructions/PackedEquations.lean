import Mettapedia.Machines.TIsa.StoreInstructions.SymbolicExecution
import Mettapedia.Machines.TIsa.StoreInstructions.PackedOccurrences

/-!
# An append-only word arena for residual equations

A nonzero handle is one plus an array ordinal. Its node has
three words: the preceding handle and two open term handles.
The links go strictly backwards. Appending a node cannot change
any earlier handle's interpretation, even when a branch continues
from an older head instead of the latest one.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.PackedEquations

open Mettapedia.Logic.LP
open PackedOccurrences (Codes)

structure Node where
  older : Word
  left : Word
  right : Word
  deriving DecidableEq, Repr

abbrev Arena := Array Node

universe u
variable {T : Type u}

def readAux (codes : Codes T) (arena : Arena) : ℕ → ℕ → Option (List (T × T))
  | _, 0 => some []
  | 0, _ + 1 => none
  | fuel + 1, position + 1 =>
    match arena[position]? with
    | none => none
    | some node =>
      if node.older.toNat < position + 1 then
        match codes.decode node.left, codes.decode node.right, readAux codes arena fuel node.older.toNat with
        | some left, some right, some earlier => some ((left, right) :: earlier)
        | _, _, _ => none
      else none

def read (codes : Codes T) (arena : Arena) (head : Word) : Option (List (T × T)) :=
  readAux codes arena head.toNat head.toNat

/-- A work list can consume the term handles without decoding their terms. -/
def wordCodes : Codes Word := ⟨some, some, fun equal => by cases equal; rfl⟩

theorem word_decode (word : Word) : wordCodes.decode word = some word := rfl

def readWords (arena : Arena) (head : Word) : Option (List (Word × Word)) :=
  read wordCodes arena head

def decodePair (codes : Codes T) (words : Word × Word) : Option (T × T) :=
  (codes.decode words.1).bind fun left => (codes.decode words.2).map fun right => (left, right)

private theorem decode_walk (codes : Codes T) (arena : Arena) (fuel head : ℕ) :
    (readAux wordCodes arena fuel head).bind (List.mapM (decodePair codes)) =
      readAux codes arena fuel head := by
  induction fuel generalizing head with
  | zero => cases head <;> rfl
  | succ fuel ih =>
    cases head with
    | zero => rfl
    | succ index =>
      simp only [readAux]
      cases found : arena[index]? with
      | none => rfl
      | some node =>
        by_cases earlier : node.older.toNat < index + 1
        · simp only [if_pos earlier, word_decode]
          rw [← ih node.older.toNat]
          cases visited : readAux wordCodes arena fuel node.older.toNat with
          | none => cases codes.decode node.left <;> cases codes.decode node.right <;> rfl
          | some old =>
            simp only [Option.bind_some, List.mapM_cons, decodePair]
            cases codes.decode node.left <;> cases codes.decode node.right <;>
              cases old.mapM (decodePair codes) <;> rfl
        · simp only [if_neg earlier]; rfl

/-- Reading the newest-first chain and then decoding gives exactly
the typed history. In particular it preserves its order and duplicates. -/
theorem read_words_exact (codes : Codes T) (arena : Arena) (head : Word) :
    (readWords arena head).bind (List.mapM (decodePair codes)) = read codes arena head :=
  decode_walk codes arena head.toNat head.toNat

theorem read_empty (codes : Codes T) (arena : Arena) : read codes arena 0 = some [] := rfl

theorem read_bound (codes : Codes T) (arena : Arena) (root : Word) {history : List (T × T)}
    (found : read codes arena root = some history) : root.toNat ≤ arena.size := by
  cases eq : root.toNat with
  | zero => omega
  | succ k =>
    by_cases inside : k < arena.size
    · omega
    · have outside : arena[k]? = none := Array.getElem?_eq_none_iff.mpr (by omega)
      simp [read, eq, readAux, outside] at found

private theorem ample_fuel (codes : Codes T) (arena : Arena) (first second head : ℕ)
    (enough : head ≤ first) (also : head ≤ second) :
    readAux codes arena first head = readAux codes arena second head := by
  induction first generalizing second head with
  | zero =>
    have empty : head = 0 := by omega
    subst head
    cases second <;> rfl
  | succ fuel ih =>
    cases head with
    | zero => cases second <;> rfl
    | succ ordinal =>
      cases second with
      | zero => omega
      | succ other =>
        simp only [readAux]
        cases looked : arena[ordinal]? with
        | none => rfl
        | some node =>
          by_cases older : node.older.toNat < ordinal + 1
          · simp only [if_pos older, ih other node.older.toNat (by omega) (by omega)]
          · simp only [if_neg older]

private theorem old_readAux (codes : Codes T) (arena : Arena) (node : Node) (fuel head : ℕ)
    (inside : head ≤ arena.size) :
    readAux codes (arena.push node) fuel head = readAux codes arena fuel head := by
  induction fuel generalizing head with
  | zero => cases head <;> rfl
  | succ fuel ih =>
    cases head with
    | zero => rfl
    | succ ordinal =>
      simp only [readAux, Array.getElem?_push, if_neg (show ordinal ≠ arena.size from by omega)]
      cases looked : arena[ordinal]? with
      | none => rfl
      | some old =>
        by_cases earlier : old.older.toNat < ordinal + 1
        · simp only [if_pos earlier, ih old.older.toNat (by omega)]
        · simp only [if_neg earlier]

theorem read_link (codes : Codes T) (arena : Arena) (head : Word) (node : Node)
    (positive : 0 < head.toNat) (found : arena[head.toNat - 1]? = some node)
    (descends : node.older.toNat < head.toNat) :
    read codes arena head = (do
      let left ← codes.decode node.left
      let right ← codes.decode node.right
      let rest ← read codes arena node.older
      some ((left, right) :: rest)) := by
  obtain ⟨index, size⟩ : ∃ index, head.toNat = index + 1 := ⟨head.toNat - 1, by omega⟩
  have indexRead : arena[index]? = some node := by simpa only [size, Nat.add_sub_cancel] using found
  have descent : node.older.toNat < index + 1 := size ▸ descends
  have enough := ample_fuel codes arena index node.older.toNat node.older.toNat (by omega) (Nat.le_refl _)
  simp only [read, size, readAux, indexRead, if_pos descent, enough]
  cases codes.decode node.left <;> cases codes.decode node.right <;>
    cases readAux codes arena node.older.toNat node.older.toNat <;> rfl

theorem older_handles_unchanged (codes : Codes T) (arena : Arena) (node : Node)
    (head : Word) (inside : head.toNat ≤ arena.size) : read codes (arena.push node) head = read codes arena head :=
  old_readAux codes arena node head.toNat head.toNat inside

def next (arena : Arena) : Word := BitVec.ofNat 64 (arena.size + 1)

def CanAppend (arena : Arena) (head : Word) : Prop :=
  head.toNat ≤ arena.size ∧ arena.size + 1 < 2 ^ 64

instance (arena : Arena) (head : Word) : Decidable (CanAppend arena head) :=
  inferInstanceAs (Decidable (_ ∧ _))

def append (arena : Arena) (node : Node) : Option (Arena × Word) :=
  if CanAppend arena node.older then some (arena.push node, next arena) else none

theorem next_exact {arena : Arena} {head : Word} (fits : CanAppend arena head) :
    (next arena).toNat = arena.size + 1 := by
  rw [next, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits.2]

theorem appended_read (codes : Codes T) {arena : Arena} {node : Node} (fits : CanAppend arena node.older)
    {history : List (T × T)} (older : read codes arena node.older = some history)
    {left right : T} (l : codes.decode node.left = some left) (r : codes.decode node.right = some right) :
    read codes (arena.push node) (next arena) = some ((left, right) :: history) := by
  unfold read
  rw [next_exact fits]
  simp only [readAux, Array.getElem?_push_size]
  have descending : node.older.toNat < arena.size + 1 := by have := fits.1; omega
  rw [if_pos descending, l, r]
  have previous := old_readAux codes arena node arena.size node.older.toNat fits.1
  rw [previous, ample_fuel codes arena arena.size node.older.toNat node.older.toNat fits.1 (Nat.le_refl _)]
  rw [show readAux codes arena node.older.toNat node.older.toNat = some history from older]

def push (codes : Codes T) (arena : Arena) (head : Word) (equation : T × T) : Option (Arena × Word) := do
  let l ← codes.encode equation.1
  let r ← codes.encode equation.2
  append arena ⟨head, l, r⟩

theorem push_exact (codes : Codes T) {arena extended : Arena} {head newHead : Word}
    {history : List (T × T)} (old : read codes arena head = some history)
    (equation : T × T) (pushed : push codes arena head equation = some (extended, newHead)) :
    read codes extended newHead = some (equation :: history) ∧
      ∀ prior : Word, prior.toNat ≤ arena.size → read codes extended prior = read codes arena prior := by
  unfold push at pushed
  obtain ⟨left, l, appended⟩ := Option.bind_eq_some_iff.mp pushed
  obtain ⟨right, r, built⟩ := Option.bind_eq_some_iff.mp appended
  unfold append at built
  split at built
  next fits =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj built)
    exact ⟨appended_read codes fits old (codes.reads l) (codes.reads r),
      older_handles_unchanged codes _ _⟩
  next _ => cases built

/-- Construct an ordered prefix by pushing it right to left. -/
def prependWords (arena : Arena) (root : Word) :
    List (Word × Word) → Option (Arena × Word)
  | [] => some (arena, root)
  | (left, right) :: later => do
    let (saved, tail) ← prependWords arena root later
    append saved ⟨tail, left, right⟩

theorem prepend_words_append (arena : Arena) (root : Word) (first later : List (Word × Word)) :
    prependWords arena root (first ++ later) =
      (prependWords arena root later).bind (fun (saved, tail) => prependWords saved tail first) := by
  induction first with
  | nil =>
    simp only [List.nil_append]
    cases prependWords arena root later with
    | none => rfl
    | some pair => cases pair; rfl
  | cons head rest ih =>
    rcases head with ⟨left, right⟩
    simp only [List.cons_append, prependWords]
    rw [ih]
    cases prependWords arena root later with
    | none => rfl
    | some pair => cases pair; rfl

theorem prepend_words_exact (arena : Arena) (root : Word) (prefixes history : List (Word × Word))
    (known : readWords arena root = some history) (within : root.toNat ≤ arena.size)
    (room : arena.size + prefixes.length < 2 ^ 64) :
    ∃ extended nextRoot, prependWords arena root prefixes = some (extended, nextRoot) ∧
      extended.size = arena.size + prefixes.length ∧ nextRoot.toNat ≤ extended.size ∧
      readWords extended nextRoot = some (prefixes ++ history) ∧
      (∀ earlier : Word, earlier.toNat ≤ arena.size → readWords extended earlier = readWords arena earlier) := by
  induction prefixes with
  | nil => exact ⟨arena, root, rfl, by simp, within, known, fun _ _ => rfl⟩
  | cons first remaining ih =>
    rcases first with ⟨left, right⟩
    have more : arena.size + remaining.length + 1 < 2 ^ 64 := by simpa [Nat.add_assoc] using room
    obtain ⟨saved, tail, installed, size, tailBound, spec, kept⟩ := ih (by omega)
    let node : Node := ⟨tail, left, right⟩
    have fits : CanAppend saved node.older := ⟨tailBound, by omega⟩
    have read := appended_read wordCodes fits spec (word_decode left) (word_decode right)
    refine ⟨saved.push node, next saved, ?_, by simp [size, Nat.add_assoc],
      by rw [next_exact fits, Array.size_push], read, ?_⟩
    · simp [prependWords, installed, append, node, fits]
    · intro earlier inRange
      exact (older_handles_unchanged wordCodes saved node earlier (by omega)).trans (kept earlier inRange)

namespace Symbolic

variable {σ : LPSignature}

def Represents (codes : Codes (Term σ)) (arena : Arena) (root : Word) (work : SymbolicExecution.Work σ) : Prop :=
  read codes arena root = some work.newer ∧ work.answer = none

theorem pushed_represents (codes : Codes (Term σ)) {arena extended : Arena} {root head : Word}
    {work : SymbolicExecution.Work σ} (ready : Represents codes arena root work) (equation : Term σ × Term σ)
    (pushed : push codes arena root equation = some (extended, head)) :
    Represents codes extended head (work.extend equation) ∧
      ∀ prior : Word, prior.toNat ≤ arena.size → read codes extended prior = read codes arena prior :=
  ⟨⟨(push_exact codes ready.1 equation pushed).1, rfl⟩, (push_exact codes ready.1 equation pushed).2⟩

def problem (codes : Codes (Term σ)) (base : SymbolicExecution.Equations σ) (arena : Arena) (head : Word) :
    Option (SymbolicExecution.Equations σ) :=
  (read codes arena head).map (fun work => base ++ work.reverse)

theorem problem_exact (codes : Codes (Term σ)) (base : SymbolicExecution.Equations σ)
    {arena : Arena} {head : Word} {work : SymbolicExecution.Work σ} (known : read codes arena head = some work.newer) :
    problem codes base arena head = some (work.problem base) := by
  rw [problem, known]
  rfl

end Symbolic

namespace Examples

private def branched : Arena := #[⟨0, 3, 5⟩, ⟨1, 7, 11⟩, ⟨1, 13, 17⟩]

theorem branches_retain_different_suffixes :
    readWords branched 2 = some [(7, 11), (3, 5)] ∧
      readWords branched 3 = some [(13, 17), (3, 5)] := by decide +kernel

theorem cyclic_handle_refuses : readWords #[⟨1, 3, 5⟩] 1 = none := by decide +kernel

theorem term_zero_is_not_the_end_of_the_equation_chain :
    readWords #[⟨0, 0, 5⟩] 1 = some [(0, 5)] := by decide +kernel

theorem duplicate_equations_are_loaded_in_full :
    readWords #[⟨0, 0, 5⟩, ⟨1, 0, 5⟩] 2 = some [(0, 5), (0, 5)] := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.PackedEquations
