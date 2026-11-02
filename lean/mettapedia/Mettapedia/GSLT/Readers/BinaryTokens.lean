import Mettapedia.GSLT.Readers.Export
import Mettapedia.GSLT.Readers.TreeCheck
import Mathlib.Data.Nat.Digits.Lemmas
import Batteries.Data.Char.Basic

/-!
# Binary token profiles: the lexical layer of a reader of a byte stream

The text profiles (`TokenProfile`, `TokenProfileV2`) cut a source at separator and delimiter
bytes before the grammar is consulted. A binary stream has no separator: where a token ends
depends on which field comes next, so a reader cuts the next token with the token sorts that the
parser can use in its current state (context-aware scanning). This module is the lexical layer of
such readers, as data in a `.module` message (`ReturnTokenProfile : (GetTokenProfile) ~>
"BinaryTokenProfile"(…)`):

* `Start(S)`: the start sort of the grammar;
* `VarUint(T)`: the code of integer words: a byte `0..T` is its own value; a byte `T + k` is
  followed by the value's `k` little-endian bytes, `k` the fewest that hold it (`encodeWord`).
  With `T = 247`, `300` is the three bytes `249 44 1`; `248 5` is no word (five fits in one byte);
* `Byte(sort, B)`: a token of `sort` is one byte of `B` (opcodes);
* `Word(sort)`: one word;
* `Count(sort)`: one word that governs the repetitions after it in its row;
* `Words(sort)`: as many words as the nearest count to its left in the same row says;
* `Bytes(sort)`: as many raw bytes as the nearest count to its left in the same row says.

The count rule is an attribute of a row, checked on the reader's tree (`countsTree`): within one
node, a `Words` or `Bytes` leaf has as many units as the value of the last `Count` leaf before it
among the node's children. Example: a row `o n bs d` with `n : Count` and `bs : Bytes` reads
`5 2 104 105 7` as `bs = 104 105`; `5 3 104 105 7` gives `bs` three bytes, `104 105 7`, and then
`d` is missing. A count may govern two lists after another operand (Vibe's `THM_INSTANTIATE_N`:
count, theorem, symbols, values).

Results:
* words: `wordLen?_encode` (an encoded word is cut exactly, whatever follows it),
  `wordValue_encode`, `wordLen?_sound` (only encodings are words: one byte string per value),
  `isWord_prefix_unique` (words are prefix-free);
* lists of words: `wordsLen?_encode`, `splitWords?_encode`, `splitWords?_sound`;
* the scanner of each kind (`Kind.scanLen?`), the engines' tokenizer: `scanLen?_word_member`,
  `scanLen?_words`, `scanLen?_bytes`;
* the trusted check of a binary reader, `readB`: the tree prints back from the rows to tokens
  whose bytes are the input, and every row's counts hold; `readB_iff` relates it to the
  token-level derivations of `TreeCheck`;
* the tables a binary reader runs, printed as a C header and MeTTa equations (`Spec.cHeader`,
  `Spec.mettaText`), the specification `gen-tables` mirrors; `Spec.conflictFree` also refuses a
  state in which two terminals could both be cut at one position.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Readers.BinaryTokens

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Readers.TokenProfile (ByteSet name? byteSet? natOfName?)
open Mettapedia.GSLT.Readers.SLR
open Mettapedia.GSLT.Readers.TreeCheck

/-! ## Words -/

/-- The word of value `v` in the code whose largest one-byte value is `T`. -/
def encodeWord (T v : Nat) : List Nat :=
  if v ≤ T then [v] else (T + (Nat.digits 256 v).length) :: Nat.digits 256 v

/-- The length of the word at the front of `bs`: a byte up to `T`; or a header `T + k` and `k`
payload bytes whose last byte is not zero and whose value is above `T` (the fewest bytes). -/
def wordLen? (T : Nat) : List Nat → Option Nat
  | [] => none
  | h :: rest =>
      if h ≤ T then some 1
      else if h < 256 ∧ h - T ≤ rest.length ∧ (rest.take (h - T)).getLast? ≠ some 0 ∧
          T < Nat.ofDigits 256 (rest.take (h - T)) then some (h - T + 1)
      else none

/-- The value of a word. -/
def wordValue : List Nat → Nat
  | [h] => h
  | _ :: p => Nat.ofDigits 256 p
  | [] => 0

def isWord (T : Nat) (tok : List Nat) : Bool := wordLen? T tok == some tok.length

/-- The total length of `n` words at the front of `bs`. -/
def wordsLen? (T : Nat) : Nat → List Nat → Option Nat
  | 0, _ => some 0
  | n + 1, bs =>
      match wordLen? T bs with
      | none => none
      | some l => (wordsLen? T n (bs.drop l)).map (l + ·)

/-- The values of the words a byte string is made of, if it is made of words. -/
def wordsOf? (T : Nat) : Nat → List Nat → Option (List Nat)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, b :: bs =>
      match wordLen? T (b :: bs) with
      | none => none
      | some l => ((wordsOf? T fuel ((b :: bs).drop l)).map (wordValue ((b :: bs).take l) :: ·))

def splitWords? (T : Nat) (bs : List Nat) : Option (List Nat) := wordsOf? T bs.length bs

def encodeWords (T : Nat) (vs : List Nat) : List Nat := vs.flatMap (encodeWord T)

/-! ### Encoded words are read back -/

theorem digits_ne_nil (v : Nat) (hv : v ≠ 0) : Nat.digits 256 v ≠ [] := by
  rw [Ne, Nat.digits_eq_nil_iff_eq_zero]; exact hv

theorem digits_lt (v : Nat) : ∀ b ∈ Nat.digits 256 v, b < 256 :=
  fun _ hb => Nat.digits_lt_base (by norm_num) hb

theorem digits_getLast? (v : Nat) (hv : v ≠ 0) : (Nat.digits 256 v).getLast? ≠ some 0 := by
  rw [List.getLast?_eq_some_getLast (digits_ne_nil v hv)]
  intro h
  exact Nat.getLast_digit_ne_zero 256 hv (Option.some.inj h)

/-- A word whose value needs `k` payload bytes has `k ≤ 255 - T` exactly when the value is below
`256 ^ (255 - T)`. -/
theorem encodeWord_length_bound (T v : Nat) (hv : v < 256 ^ (255 - T)) :
    (Nat.digits 256 v).length ≤ 255 - T :=
  (Nat.digits_length_le_iff (by norm_num) v).mpr hv

theorem wordLen?_encode (T v : Nat) (hT : T ≤ 254) (hv : v < 256 ^ (255 - T)) (rest : List Nat) :
    wordLen? T (encodeWord T v ++ rest) = some (encodeWord T v).length := by
  unfold encodeWord
  split
  · simp [wordLen?, *]
  · rename_i hvT
    have hv0 : v ≠ 0 := by omega
    have hlen := encodeWord_length_bound T v hv
    have hpos : 0 < (Nat.digits 256 v).length :=
      List.length_pos_iff.mpr (digits_ne_nil v hv0)
    simp only [List.cons_append, wordLen?, List.length_cons]
    have h1 : ¬ (T + (Nat.digits 256 v).length ≤ T) := by omega
    have hk : T + (Nat.digits 256 v).length - T = (Nat.digits 256 v).length := by omega
    have htake : (Nat.digits 256 v ++ rest).take (Nat.digits 256 v).length = Nat.digits 256 v :=
      List.take_left' rfl
    rw [if_neg h1, hk, htake, Nat.ofDigits_digits]
    rw [if_pos ⟨by omega, by simp, digits_getLast? v hv0, by omega⟩]

theorem wordValue_encode (T v : Nat) : wordValue (encodeWord T v) = v := by
  unfold encodeWord
  split
  · rfl
  · rename_i hvT
    have hv0 : v ≠ 0 := by omega
    obtain ⟨d, ds, hd⟩ : ∃ d ds, Nat.digits 256 v = d :: ds := by
      cases h : Nat.digits 256 v with
      | nil => exact absurd h (digits_ne_nil v hv0)
      | cons d ds => exact ⟨d, ds, rfl⟩
    rw [hd]
    simp only [wordValue]
    rw [← hd, Nat.ofDigits_digits]

theorem isWord_encode (T v : Nat) (hT : T ≤ 254) (hv : v < 256 ^ (255 - T)) :
    isWord T (encodeWord T v) = true := by
  have := wordLen?_encode T v hT hv []
  simp only [List.append_nil] at this
  simp [isWord, this]

/-! ### Only encodings are words -/

theorem wordLen?_sound (T : Nat) (bs : List Nat) (hb : ∀ b ∈ bs, b < 256) (l : Nat)
    (h : wordLen? T bs = some l) :
    l ≤ bs.length ∧ bs.take l = encodeWord T (wordValue (bs.take l)) := by
  cases bs with
  | nil => simp [wordLen?] at h
  | cons x rest =>
    simp only [wordLen?] at h
    split at h
    · rename_i hx
      simp only [Option.some.injEq] at h
      subst h
      simp [wordValue, encodeWord, hx]
    · rename_i hx
      split at h
      · rename_i hc
        obtain ⟨h256, hk, hlast, hval⟩ := hc
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨by simp; omega, ?_⟩
        have hkpos : 0 < x - T := by omega
        set p := rest.take (x - T) with hp
        have hplen : p.length = x - T := by simp [hp]; omega
        have hpne : p ≠ [] := by intro h; rw [h] at hplen; simp at hplen; omega
        have hpb : ∀ b ∈ p, b < 256 := fun b hb' =>
          hb b (List.mem_cons_of_mem _ (List.mem_of_mem_take hb'))
        have hlast' : ∀ (h : p ≠ []), p.getLast h ≠ 0 := by
          intro h' h0
          apply hlast
          rw [List.getLast?_eq_some_getLast h', h0]
        have hdig : Nat.digits 256 (Nat.ofDigits 256 p) = p :=
          Nat.digits_ofDigits 256 (by norm_num) p hpb hlast'
        have htake : (x :: rest).take (x - T + 1) = x :: p := by simp [hp]
        rw [htake]
        obtain ⟨q, qs, hq⟩ : ∃ q qs, p = q :: qs := by
          cases hpq : p with
          | nil => exact absurd hpq hpne
          | cons q qs => exact ⟨q, qs, rfl⟩
        have hval' : wordValue (x :: p) = Nat.ofDigits 256 p := by
          rw [hq]; rfl
        rw [hval', encodeWord, if_neg (by omega), hdig, hplen]
        congr 1
        omega
      · simp at h

theorem wordLen?_pos (T : Nat) (bs : List Nat) (l : Nat) (h : wordLen? T bs = some l) : 0 < l := by
  cases bs with
  | nil => simp [wordLen?] at h
  | cons x rest =>
    simp only [wordLen?] at h
    split at h
    · simp at h; omega
    · split at h
      · simp at h; omega
      · simp at h

/-- What follows a word does not change where it ends. -/
theorem wordLen?_append (T : Nat) (bs : List Nat) (l : Nat) (h : wordLen? T bs = some l)
    (rest : List Nat) : wordLen? T (bs.take l ++ rest) = some l := by
  cases bs with
  | nil => simp [wordLen?] at h
  | cons x xs =>
    simp only [wordLen?] at h
    split at h
    · rename_i hx
      simp only [Option.some.injEq] at h
      subst h
      simp [wordLen?, hx]
    · rename_i hx
      split at h
      · rename_i hc
        obtain ⟨h256, hk, hlast, hval⟩ := hc
        simp only [Option.some.injEq] at h
        subst h
        have htake : (xs.take (x - T) ++ rest).take (x - T) = xs.take (x - T) := by
          apply List.take_left'; simp; omega
        simp only [List.take_succ_cons, List.cons_append, wordLen?, if_neg hx]
        rw [htake]
        rw [if_pos ⟨h256, by simp; omega, hlast, hval⟩]
      · simp at h

/-- Words are prefix-free: two words at the front of one stream are the same word. -/
theorem isWord_prefix_unique (T : Nat) (a b r s : List Nat) (ha : isWord T a = true)
    (hb : isWord T b = true) (he : a ++ r = b ++ s) : a = b := by
  simp only [isWord, beq_iff_eq] at ha hb
  have h1 := wordLen?_append T a a.length ha r
  have h2 := wordLen?_append T b b.length hb s
  rw [List.take_length] at h1 h2
  rw [he] at h1
  rw [h1] at h2
  simp only [Option.some.injEq] at h2
  have := congrArg (List.take a.length) he
  rw [List.take_left' rfl, h2, List.take_left' rfl] at this
  exact this

/-! ### Lists of words -/

theorem wordsLen?_encode (T : Nat) (hT : T ≤ 254) :
    ∀ (vs : List Nat), (∀ v ∈ vs, v < 256 ^ (255 - T)) → ∀ rest : List Nat,
      wordsLen? T vs.length (encodeWords T vs ++ rest) = some (encodeWords T vs).length
  | [], _, _ => rfl
  | v :: vs, hvs, rest => by
    have hv := hvs v List.mem_cons_self
    have ih := wordsLen?_encode T hT vs (fun w hw => hvs w (List.mem_cons_of_mem _ hw)) rest
    have hw := wordLen?_encode T v hT hv (encodeWords T vs ++ rest)
    have hsplit : encodeWords T (v :: vs) ++ rest = encodeWord T v ++ (encodeWords T vs ++ rest) := by
      simp [encodeWords]
    rw [hsplit, List.length_cons]
    simp only [wordsLen?, hw, List.drop_left, ih, Option.map_some]
    simp [encodeWords]

theorem wordsOf?_encode (T : Nat) (hT : T ≤ 254) :
    ∀ (vs : List Nat), (∀ v ∈ vs, v < 256 ^ (255 - T)) → ∀ fuel : Nat,
      (encodeWords T vs).length ≤ fuel → wordsOf? T fuel (encodeWords T vs) = some vs
  | [], _, fuel, _ => by cases fuel <;> rfl
  | v :: vs, hvs, fuel, hf => by
    have hv := hvs v List.mem_cons_self
    have ih := wordsOf?_encode T hT vs (fun w hw => hvs w (List.mem_cons_of_mem _ hw))
    have hw := wordLen?_encode T v hT hv (encodeWords T vs)
    have hsplit : encodeWords T (v :: vs) = encodeWord T v ++ encodeWords T vs := by
      simp [encodeWords]
    have hpos : 0 < (encodeWord T v).length := by
      unfold encodeWord; split <;> simp
    obtain ⟨b, bs, hbs⟩ : ∃ b bs, encodeWord T v = b :: bs := by
      cases h : encodeWord T v with
      | nil => rw [h] at hpos; simp at hpos
      | cons b bs => exact ⟨b, bs, rfl⟩
    rw [hsplit] at hf ⊢
    simp only [List.length_append] at hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hrest := ih fuel (by omega)
      rw [hbs, List.cons_append]
      simp only [wordsOf?]
      rw [← List.cons_append, ← hbs]
      simp only [hw, List.drop_left, List.take_left, wordValue_encode, hrest, Option.map_some]

theorem splitWords?_encode (T : Nat) (hT : T ≤ 254) (vs : List Nat)
    (hvs : ∀ v ∈ vs, v < 256 ^ (255 - T)) : splitWords? T (encodeWords T vs) = some vs :=
  wordsOf?_encode T hT vs hvs _ (Nat.le_refl _)

theorem wordsOf?_sound (T : Nat) :
    ∀ (fuel : Nat) (bs : List Nat), (∀ b ∈ bs, b < 256) → ∀ vs : List Nat,
      wordsOf? T fuel bs = some vs → bs = encodeWords T vs
  | fuel, [], _, vs, h => by
    have h0 : wordsOf? T fuel [] = some [] := by cases fuel <;> rfl
    rw [h0] at h
    simp only [Option.some.injEq] at h
    subst h
    rfl
  | 0, _ :: _, _, _, h => by simp [wordsOf?] at h
  | fuel + 1, b :: bs, hb, vs, h => by
    simp only [wordsOf?] at h
    split at h
    · simp at h
    · rename_i l hl
      cases hrest : wordsOf? T fuel ((b :: bs).drop l) with
      | none => rw [hrest] at h; simp at h
      | some ws =>
        rw [hrest] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨hle, htake⟩ := wordLen?_sound T (b :: bs) hb l hl
        have hdrop := wordsOf?_sound T fuel ((b :: bs).drop l)
          (fun x hx => hb x (List.mem_of_mem_drop hx)) ws hrest
        calc b :: bs = (b :: bs).take l ++ (b :: bs).drop l := (List.take_append_drop l _).symm
          _ = encodeWord T (wordValue ((b :: bs).take l)) ++ encodeWords T ws := by
              rw [← htake, ← hdrop]
          _ = encodeWords T (wordValue ((b :: bs).take l) :: ws) := by
              simp [encodeWords]

theorem splitWords?_sound (T : Nat) (bs : List Nat) (hb : ∀ b ∈ bs, b < 256) (vs : List Nat)
    (h : splitWords? T bs = some vs) : bs = encodeWords T vs :=
  wordsOf?_sound T bs.length bs hb vs h

/-! ## Token kinds and the profile -/

/-- How a token of a sort is cut from the bytes. -/
inductive Kind where
  | byte (set : ByteSet)
  | word
  | count
  | words
  | bytes
  deriving DecidableEq, Repr

structure TokenClass where
  sort : String
  kind : Kind
  deriving DecidableEq, Repr

/-- A decoded binary profile. -/
structure Profile where
  start : String
  inline : Nat
  classes : List TokenClass
  deriving DecidableEq, Repr

/-- The kind of a token sort, when the profile declares the sort exactly once. -/
def Profile.kindOf? (p : Profile) (sort : String) : Option Kind :=
  match p.classes.filter (·.sort == sort) with
  | [c] => some c.kind
  | _ => none

def class? : Pattern → Option TokenClass
  | .apply "Byte" [sort, set] => do
      let sort ← name? sort
      let set ← byteSet? set
      pure ⟨sort, .byte set⟩
  | .apply "Word" [sort] => (name? sort).map (⟨·, .word⟩)
  | .apply "Count" [sort] => (name? sort).map (⟨·, .count⟩)
  | .apply "Words" [sort] => (name? sort).map (⟨·, .words⟩)
  | .apply "Bytes" [sort] => (name? sort).map (⟨·, .bytes⟩)
  | _ => none

def classes? : List Pattern → Option (List TokenClass)
  | [] => some []
  | p :: ps => do
      let c ← class? p
      let cs ← classes? ps
      pure (c :: cs)

/-- `BinaryTokenProfile(Start(S), VarUint(T), CLASS…)`. -/
def profile? : Pattern → Option Profile
  | .apply "BinaryTokenProfile" (.apply "Start" [start] :: .apply "VarUint" [inline] :: rest) => do
      let start ← name? start
      let inline ← name? inline >>= natOfName?
      let classes ← classes? rest
      pure { start, inline, classes }
  | _ => none

/-! ## Tokens as strings

The tree check reads tokens as strings; a binary token is the string of the characters whose codes
are its bytes. -/

def bytesOf (x : String) : List Nat := x.toList.map Char.toNat

def strOf (bs : List Nat) : String := String.ofList (bs.map Char.ofNat)

theorem bytesOf_strOf (bs : List Nat) (h : ∀ b ∈ bs, b < 256) : bytesOf (strOf bs) = bs := by
  simp only [bytesOf, strOf, String.toList_ofList, List.map_map]
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, Function.comp_apply, Char.toNat_ofNat]
    have hb := h b List.mem_cons_self
    rw [if_pos (Or.inl (by omega)), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-! ## Membership, without the counts -/

/-- A token of a kind, the counts aside: one byte of the set; one word; any whole number of
words; any bytes. -/
def Kind.member (T : Nat) : Kind → List Nat → Bool
  | .byte set, [b] => set.contains b
  | .byte _, _ => false
  | .word, tok => isWord T tok
  | .count, tok => isWord T tok
  | .words, tok => (splitWords? T tok).isSome
  | .bytes, _ => true

def Profile.inSort (p : Profile) (c x : String) : Bool :=
  (bytesOf x).all (· < 256) &&
    match p.kindOf? c with
    | some k => k.member p.inline (bytesOf x)
    | none => false

/-! ## The counts of a row -/

mutual
/-- Every node's counts hold. -/
def countsTree (p : Profile) : Tree → Bool
  | .leaf _ _ => true
  | .node _ kids => countsKids p none kids

/-- A node's children, left to right, with the value of the last count leaf seen. -/
def countsKids (p : Profile) : Option Nat → List Tree → Bool
  | _, [] => true
  | reg, t :: ts =>
      match t with
      | .leaf c x =>
          match p.kindOf? c with
          | some .count => countsKids p (some (wordValue (bytesOf x))) ts
          | some .words =>
              (reg.isSome && (splitWords? p.inline (bytesOf x)).map List.length == reg) &&
                countsKids p reg ts
          | some .bytes => (reg.isSome && some (bytesOf x).length == reg) && countsKids p reg ts
          | _ => countsKids p reg ts
      | .node _ _ => countsTree p t && countsKids p reg ts
end

/-! ## The trusted check of a binary reader -/

def joinBytes (toks : List String) : List Nat := toks.flatMap bytesOf

/-- A tree is the reading of `bs` at sort `s`: it prints back from the rows to tokens whose bytes
are `bs`, and every row's counts hold. -/
def readB (g : Grammar) (p : Profile) (s : String) (bs : List Nat) (t : Tree) : Bool :=
  match printTree g t with
  | some (s', toks) => s' == s && joinBytes toks == bs && countsTree p t
  | none => false

theorem readB_iff (g : Grammar) (wf : WellFormed g) (p : Profile) (s : String) (bs : List Nat)
    (t : Tree) :
    readB g p s bs t = true ↔
      ∃ toks, Derives g s toks t ∧ joinBytes toks = bs ∧ countsTree p t = true := by
  unfold readB
  constructor
  · intro h
    cases hp : printTree g t with
    | none => simp [hp] at h
    | some pr =>
      obtain ⟨s', toks⟩ := pr
      simp only [hp, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, hj⟩, hc⟩ := h
      exact ⟨toks, (printTree_iff g wf t s' toks).mp hp, hj, hc⟩
  · rintro ⟨toks, hd, hj, hc⟩
    rw [(printTree_iff g wf t s toks).mpr hd]
    simp [hj, hc]

/-! ## The scanner the engines run -/

/-- The length of the token of a kind at the front of `bs`, with `reg` the value of the governing
count. -/
def Kind.scanLen? (T : Nat) (reg : Option Nat) : Kind → List Nat → Option Nat
  | .byte set, b :: _ => if set.contains b then some 1 else none
  | .byte _, [] => none
  | .word, bs => wordLen? T bs
  | .count, bs => wordLen? T bs
  | .words, bs => reg.bind fun n => wordsLen? T n bs
  | .bytes, bs => reg.bind fun n => if n ≤ bs.length then some n else none

/-- The register after a token: a count sets it. -/
def Kind.nextReg (reg : Option Nat) : Kind → List Nat → Option Nat
  | .count, tok => some (wordValue tok)
  | _, _ => reg

theorem wordsLen?_sound (T : Nat) :
    ∀ (n : Nat) (bs : List Nat), (∀ b ∈ bs, b < 256) → ∀ l : Nat, wordsLen? T n bs = some l →
      l ≤ bs.length ∧ ∃ vs : List Nat, vs.length = n ∧ bs.take l = encodeWords T vs
  | 0, bs, _, l, h => by
    simp only [wordsLen?, Option.some.injEq] at h
    subst h
    exact ⟨Nat.zero_le _, [], rfl, by simp [encodeWords]⟩
  | n + 1, bs, hb, l, h => by
    simp only [wordsLen?] at h
    split at h
    · simp at h
    · rename_i l1 hl1
      cases hrest : wordsLen? T n (bs.drop l1) with
      | none => rw [hrest] at h; simp at h
      | some l2 =>
        rw [hrest] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨hle1, htake1⟩ := wordLen?_sound T bs hb l1 hl1
        obtain ⟨hle2, vs, hlen, htake2⟩ := wordsLen?_sound T n (bs.drop l1)
          (fun x hx => hb x (List.mem_of_mem_drop hx)) l2 hrest
        simp only [List.length_drop] at hle2
        refine ⟨by omega, wordValue (bs.take l1) :: vs, by simp [hlen], ?_⟩
        rw [List.take_add, htake2]
        simp only [encodeWords, List.flatMap_cons]
        exact congrArg (· ++ vs.flatMap (encodeWord T)) htake1

/-- A word the scanner cuts is a member of its kind. -/
theorem scanLen?_word_member (T : Nat) (reg : Option Nat) (k : Kind) (hk : k = .word ∨ k = .count)
    (bs : List Nat) (hb : ∀ b ∈ bs, b < 256) (l : Nat) (h : k.scanLen? T reg bs = some l) :
    l ≤ bs.length ∧ k.member T (bs.take l) = true := by
  have hw : wordLen? T bs = some l := by
    rcases hk with rfl | rfl <;> simpa [Kind.scanLen?] using h
  obtain ⟨hle, htake⟩ := wordLen?_sound T bs hb l hw
  refine ⟨hle, ?_⟩
  have hm : isWord T (bs.take l) = true := by
    have := wordLen?_append T bs l hw []
    simp only [List.append_nil] at this
    simp [isWord, this, List.length_take, Nat.min_eq_left hle]
  rcases hk with rfl | rfl <;> simpa [Kind.member] using hm


/-- A list of words the scanner cuts is that many words. -/
theorem scanLen?_words (T n : Nat) (bs : List Nat) (hb : ∀ b ∈ bs, b < 256) (l : Nat)
    (h : Kind.words.scanLen? T (some n) bs = some l) :
    l ≤ bs.length ∧ ∃ vs : List Nat, vs.length = n ∧ bs.take l = encodeWords T vs :=
  wordsLen?_sound T n bs hb l (by simpa [Kind.scanLen?] using h)

/-- Raw bytes the scanner cuts are as many as the count says. -/
theorem scanLen?_bytes (T n : Nat) (bs : List Nat) (l : Nat)
    (h : Kind.bytes.scanLen? T (some n) bs = some l) : l = n ∧ n ≤ bs.length := by
  simp only [Kind.scanLen?, Option.bind_some] at h
  split at h
  · simp only [Option.some.injEq] at h
    exact ⟨h.symm, by assumption⟩
  · simp at h

/-- Completeness of the scanner: the encoding of a word, of a list of words, of bytes, is cut
exactly, whatever follows it. -/
theorem scanLen?_word_encode (T v : Nat) (hT : T ≤ 254) (hv : v < 256 ^ (255 - T))
    (reg : Option Nat) (rest : List Nat) :
    Kind.word.scanLen? T reg (encodeWord T v ++ rest) = some (encodeWord T v).length ∧
      Kind.count.scanLen? T reg (encodeWord T v ++ rest) = some (encodeWord T v).length := by
  simp [Kind.scanLen?, wordLen?_encode T v hT hv]

theorem scanLen?_words_encode (T : Nat) (hT : T ≤ 254) (vs : List Nat)
    (hvs : ∀ v ∈ vs, v < 256 ^ (255 - T)) (rest : List Nat) :
    Kind.words.scanLen? T (some vs.length) (encodeWords T vs ++ rest) =
      some (encodeWords T vs).length := by
  simp [Kind.scanLen?, wordsLen?_encode T hT vs hvs rest]

theorem scanLen?_bytes_encode (T : Nat) (bs rest : List Nat) :
    Kind.bytes.scanLen? T (some bs.length) (bs ++ rest) = some bs.length := by
  simp [Kind.scanLen?]

/-! ## One row, read by the scanner

The leaves of a row whose items are all token sorts (a flat row, as every instruction of a binary
record) are valid when each is a token of its kind, the counts aside, and each list or bytes leaf has
as many units as the last count before it (`rowValid`). The scanner reads such a row from a stream
(`readRow`), and it reads back exactly the valid leaves, whatever follows them
(`readRow_complete`). Since `readRow` is a function, two valid readings of one row that are
prefixes of one stream are the same reading (`row_unique`). -/

/-- A token of a kind, with `reg` the value of the governing count. -/
def tokValid (T : Nat) (reg : Option Nat) : Kind → List Nat → Bool
  | .byte set, tok => Kind.member T (.byte set) tok
  | .word, tok => isWord T tok
  | .count, tok => isWord T tok
  | .words, tok => reg.isSome && (splitWords? T tok).map List.length == reg
  | .bytes, tok => reg.isSome && some tok.length == reg

/-- The leaves of a flat row, in order, with the register the counts set. -/
def rowValid (T : Nat) : Option Nat → List Kind → List (List Nat) → Bool
  | _, [], [] => true
  | reg, k :: ks, tok :: toks => tokValid T reg k tok && rowValid T (k.nextReg reg tok) ks toks
  | _, _, _ => false

/-- The scanner on a flat row: each item cut in turn, the register threaded. -/
def readRow (T : Nat) : List Kind → Option Nat → List Nat → Option (List (List Nat) × List Nat)
  | [], _, bs => some ([], bs)
  | k :: ks, reg, bs =>
      match k.scanLen? T reg bs with
      | none => none
      | some l =>
          (readRow T ks (k.nextReg reg (bs.take l)) (bs.drop l)).map fun (toks, rest) =>
            (bs.take l :: toks, rest)

theorem wordLen?_le (T : Nat) (bs : List Nat) (l : Nat) (h : wordLen? T bs = some l) :
    l ≤ bs.length := by
  cases bs with
  | nil => simp [wordLen?] at h
  | cons x rest =>
    simp only [wordLen?] at h
    split at h
    · simp at h; simp; omega
    · split at h
      · rename_i hc
        simp only [Option.some.injEq] at h
        simp; omega
      · simp at h

/-- A word at the front of `bs` ends where it ends whatever follows `bs`. -/
theorem wordLen?_append_right (T : Nat) (bs : List Nat) (l : Nat) (h : wordLen? T bs = some l)
    (rest : List Nat) : wordLen? T (bs ++ rest) = some l := by
  have := wordLen?_append T bs l h (bs.drop l ++ rest)
  rwa [← List.append_assoc, List.take_append_drop] at this

/-- A byte string made of words is cut by `wordsLen?` exactly, whatever follows it. -/
theorem wordsLen?_of_wordsOf? (T : Nat) :
    ∀ (fuel : Nat) (tok : List Nat) (vs : List Nat), wordsOf? T fuel tok = some vs →
      ∀ rest, wordsLen? T vs.length (tok ++ rest) = some tok.length
  | fuel, [], vs, h, rest => by
    have h0 : wordsOf? T fuel [] = some [] := by cases fuel <;> rfl
    rw [h0] at h
    simp only [Option.some.injEq] at h
    subst h
    rfl
  | 0, _ :: _, _, h, _ => by simp [wordsOf?] at h
  | fuel + 1, b :: bs, vs, h, rest => by
    simp only [wordsOf?] at h
    split at h
    · simp at h
    · rename_i l hl
      cases hr : wordsOf? T fuel ((b :: bs).drop l) with
      | none => rw [hr] at h; simp at h
      | some ws =>
        rw [hr] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        have hle := wordLen?_le T _ l hl
        have ih := wordsLen?_of_wordsOf? T fuel ((b :: bs).drop l) ws hr rest
        simp only [List.length_cons, wordsLen?]
        rw [List.cons_append, ← List.cons_append, wordLen?_append_right T (b :: bs) l hl rest]
        simp only [List.drop_append_of_le_length hle, ih, Option.map_some, Option.some.injEq,
          List.length_drop]
        simp only [List.length_cons] at hle ⊢
        omega

theorem tokValid_scan (T : Nat) (reg : Option Nat) (k : Kind) (tok rest : List Nat)
    (h : tokValid T reg k tok = true) : k.scanLen? T reg (tok ++ rest) = some tok.length := by
  cases k with
  | byte set =>
    cases tok with
    | nil => simp [tokValid, Kind.member] at h
    | cons b bs =>
      cases bs with
      | nil => simp only [tokValid, Kind.member] at h; simp [Kind.scanLen?, h]
      | cons _ _ => simp [tokValid, Kind.member] at h
  | word =>
    simp only [tokValid, isWord, beq_iff_eq] at h
    exact wordLen?_append_right T tok tok.length h rest
  | count =>
    simp only [tokValid, isWord, beq_iff_eq] at h
    exact wordLen?_append_right T tok tok.length h rest
  | words =>
    simp only [tokValid, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hs, hm⟩ := h
    obtain ⟨n, rfl⟩ := Option.isSome_iff_exists.mp hs
    cases hw : splitWords? T tok with
    | none => rw [hw] at hm; simp at hm
    | some vs =>
      rw [hw] at hm
      simp only [Option.map_some, Option.some.injEq] at hm
      subst hm
      simp only [Kind.scanLen?, Option.bind_some]
      exact wordsLen?_of_wordsOf? T tok.length tok vs hw rest
  | bytes =>
    simp only [tokValid, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hs, hm⟩ := h
    obtain ⟨n, rfl⟩ := Option.isSome_iff_exists.mp hs
    simp only [Option.some.injEq] at hm
    subst hm
    simp [Kind.scanLen?]

/-- The scanner reads back exactly the valid leaves of a row, whatever follows them. -/
theorem readRow_complete (T : Nat) :
    ∀ (ks : List Kind) (reg : Option Nat) (toks : List (List Nat)) (rest : List Nat),
      rowValid T reg ks toks = true → readRow T ks reg (toks.flatten ++ rest) = some (toks, rest)
  | [], _, [], rest, _ => by simp [readRow]
  | [], _, _ :: _, _, h => by simp [rowValid] at h
  | _ :: _, _, [], _, h => by simp [rowValid] at h
  | k :: ks, reg, tok :: toks, rest, h => by
    simp only [rowValid, Bool.and_eq_true] at h
    obtain ⟨ht, hr⟩ := h
    have hscan := tokValid_scan T reg k tok (toks.flatten ++ rest) ht
    simp only [List.flatten_cons, List.append_assoc, readRow, hscan, List.take_left,
      List.drop_left]
    rw [readRow_complete T ks _ toks rest hr]
    rfl

/-- Two valid readings of one row that are prefixes of one stream are the same reading. -/
theorem row_unique (T : Nat) (ks : List Kind) (reg : Option Nat) (as bs : List (List Nat))
    (r1 r2 : List Nat) (ha : rowValid T reg ks as = true) (hb : rowValid T reg ks bs = true)
    (he : as.flatten ++ r1 = bs.flatten ++ r2) : as = bs ∧ r1 = r2 := by
  have h1 := readRow_complete T ks reg as r1 ha
  have h2 := readRow_complete T ks reg bs r2 hb
  rw [he] at h1
  rw [h1] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact h2

/-! ## The tables of a binary reader

A `Spec` is a grammar, its binary profile, and the start sort the tables are built for (one
`.module` may give several start sorts, for example the files before and after Vibe's `--proofs`).
The grammar part of the tables is that of `Export`; the lexical part is each token sort's kind
and, for the one-byte sorts, their bytes. -/

structure Spec where
  name : String
  grammar : LanguageDef
  profile : Profile
  start : String

namespace Spec

variable (s : Spec)

def tokenSorts : List String := s.profile.classes.map (·.sort)

def productions : List Prod := (SLR.productions s.tokenSorts s.start s.grammar).getD []

def tables : Tables := build s.productions

def terminals : List Sym :=
  .eof :: ((s.tables.prods.flatMap (·.rhs)).filter (fun x => match x with
    | .lit _ => true | _ => false)).eraseDups ++ s.tokenSorts.map .tok

def phraseSorts : List String := (s.tables.prods.map (·.lhs)).eraseDups

def termIndex (x : Sym) : Nat := (s.terminals.findIdx? (· == x)).getD 0
def sortIndex (n : String) : Nat := (s.phraseSorts.findIdx? (· == n)).getD 0

/-- A token of this sort can be empty (a list or bytes whose count is zero). -/
def canBeEmpty (c : String) : Bool :=
  match s.profile.kindOf? c with
  | some .words | some .bytes => true
  | _ => false

/-- Two token sorts that could both be cut at one position: one-byte sorts whose bytes meet, or
any other pair (a word can begin with any byte; a list or bytes can be empty). -/
def sortsMeet (c d : String) : Bool :=
  c == d ||
    match s.profile.kindOf? c, s.profile.kindOf? d with
    | some (.byte x), some (.byte y) => x.members.any (y.members.contains ·)
    | _, _ => true

def meet : Sym → Sym → Bool
  | .tok c, .tok d => s.sortsMeet c d
  | .eof, .tok c => s.canBeEmpty c
  | .tok c, .eof => s.canBeEmpty c
  | .lit _, _ => true
  | _, .lit _ => true
  | _, _ => false

/-- States in which two different terminals that could be cut at one position both have an
action. The scanner tries the terminals of a state in order, so each such pair is refused,
whatever the actions. -/
def cutConflictsIn (t : Tables) : List (Nat × Sym × Sym) :=
  t.actions.flatMap fun (st, a, _) =>
    t.actions.filterMap fun (st', b, _) =>
      if st == st' && a != b && s.meet a b then some (st, a, b) else none

def cutConflicts : List (Nat × Sym × Sym) := s.cutConflictsIn s.tables

def conflictFree : Bool :=
  let t := s.tables
  s.productions.length == s.grammar.terms.length + 1 && t.conflicts.isEmpty &&
    (s.cutConflictsIn t).isEmpty && (t.prods.map (·.rhs.length)).all (· ≤ 24)

end Spec

def Kind.code : Kind → Nat
  | .byte _ => 0
  | .word => 1
  | .count => 2
  | .words => 3
  | .bytes => 4

def Kind.metta : Kind → String
  | .byte _ => "rdr-byte"
  | .word => "rdr-word"
  | .count => "rdr-count"
  | .words => "rdr-words"
  | .bytes => "rdr-bytes"

def Kind.byteSet : Kind → ByteSet
  | .byte set => set
  | _ => .points []

open Mettapedia.GSLT.Readers.Export (quote symMetta actionMetta byteRow natsMetta)

/-- What the printers read, computed once: the tables, the terminals in order (end of input, the
fixed spellings, the token sorts) and the phrase sorts in order. -/
structure Layout where
  t : Tables
  terms : List Sym
  sorts : List String

def Spec.layout (s : Spec) : Layout :=
  let t := s.tables
  { t,
    terms := .eof :: ((t.prods.flatMap (·.rhs)).filter (fun x => match x with
      | .lit _ => true | _ => false)).eraseDups ++ s.tokenSorts.map .tok,
    sorts := (t.prods.map (·.lhs)).eraseDups }

def Layout.termIndex (L : Layout) (x : Sym) : Nat := (L.terms.findIdx? (· == x)).getD 0
def Layout.sortIndex (L : Layout) (n : String) : Nat := (L.sorts.findIdx? (· == n)).getD 0

theorem Spec.layout_tables (s : Spec) : s.layout.t = s.tables := rfl
theorem Spec.layout_terms (s : Spec) : s.layout.terms = s.terminals := rfl
theorem Spec.layout_sorts (s : Spec) : s.layout.sorts = s.phraseSorts := rfl
theorem Spec.layout_termIndex (s : Spec) (x : Sym) : s.layout.termIndex x = s.termIndex x := rfl
theorem Spec.layout_sortIndex (s : Spec) (n : String) : s.layout.sortIndex n = s.sortIndex n := rfl

/-- The tables as MeTTa equations over the language name `lang`. The action and goto tables are
written once per state: the state's actions in terminal order, and its gotos in sort order. CeTTa
looks an equation up among all equations with its head and language, so one equation per state is
read far faster than one per state and terminal (measured: an action lookup among 4,326 equations
took 0.14 s, a kind lookup among 41 equations a few milliseconds). -/
def mettaText (s : Spec) (lang : String) : String :=
  let L := s.layout
  let t := L.t
  let header := s!"; Generated from {s.name}.module by Mettapedia.GSLT.Readers.BinaryTokens.\n" ++
    s!"; {t.prods.length} productions, {t.states.length} states, " ++
    s!"{t.actions.length} actions, {t.gotos.length} gotos. Do not edit.\n"
  let nState := t.states.length
  let p := s.profile
  let lexical :=
    [s!"(= (rdr:start {lang}) {s.start})",
     s!"(= (rdr:binary {lang}) True)",
     s!"(= (rdr:varuint-inline {lang}) {p.inline})",
     s!"(= (rdr:first-token-sort {lang}) {L.terms.length - s.tokenSorts.length})",
     s!"(= (rdr:token-sorts {lang}) (" ++ " ".intercalate (s.tokenSorts.map fun c =>
        s!"({c} {L.termIndex (.tok c)})") ++ "))"]
  let spellings := L.terms.filterMap fun x => match x with
    | .lit w => some s!"(= (rdr:spelling-terminal {lang} {quote w}) {L.termIndex x})"
    | _ => none
  let termSorts := s.tokenSorts.map fun c =>
    s!"(= (rdr:terminal-sort {lang} {L.termIndex (.tok c)}) {c})"
  let prods := (List.range t.prods.length).map fun i =>
    let q := t.prods.getD i default
    s!"(= (rdr:prod {lang} {i}) ({quote q.label} {q.lhs} {q.rhs.length} (" ++
      " ".intercalate (q.rhs.map symMetta) ++ ")))"
  let acts := (List.range nState).map fun st =>
    s!"(= (rdr:actions {lang} {st}) (" ++ " ".intercalate (L.terms.filterMap fun x =>
      match t.actions.find? (fun (s', a, _) => s' == st && a == x) with
      | some (_, _, a) => some s!"({L.termIndex x} {actionMetta a})"
      | none => none) ++ "))"
  let gotos := (List.range nState).map fun st =>
    s!"(= (rdr:gotos {lang} {st}) (" ++ " ".intercalate (L.sorts.filterMap fun n =>
      match t.gotos.find? (fun (s', n', _) => s' == st && n' == n) with
      | some (_, _, x) => some s!"({n} {x})"
      | none => none) ++ "))"
  let kinds := p.classes.map fun c => s!"(= (rdr:kind {lang} {c.sort}) {c.kind.metta})"
  let bytes := p.classes.filterMap fun c => match c.kind with
    | .byte set => some (s!"(= (rdr:byte-set {lang} {c.sort}) " ++ natsMetta set.members ++ ")")
    | _ => none
  header ++ "\n".intercalate (lexical ++ spellings ++ termSorts ++ prods ++ acts ++ gotos ++ kinds ++
    bytes) ++ "\n"

/-- The tables as a C header with prefix `p`. -/
def cHeader (s : Spec) (p : String) : String :=
  let L := s.layout
  let t := L.t
  let nTerm := L.terms.length
  let nSort := L.sorts.length
  let nState := t.states.length
  let prof := s.profile
  let actionCell (st : Nat) (x : Sym) : String :=
    match (t.actions.find? fun (s', a, _) => s' == st && a == x) with
    | some (_, _, .shift n) => s!"{n + 1}"
    | some (_, _, .reduce q) => s!"-{q + 1}"
    | some (_, _, .accept) => s!"{p}_ACCEPT"
    | none => "0"
  let gotoCell (st : Nat) (n : String) : String :=
    match (t.gotos.find? fun (s', n', _) => s' == st && n' == n) with
    | some (_, _, x) => s!"{x}"
    | none => "-1"
  s!"/* Generated from {s.name}.module by Mettapedia.GSLT.Readers.BinaryTokens. Do not edit. */\n" ++
  s!"#define {p}_TERMINALS {nTerm}\n#define {p}_SORTS {nSort}\n#define {p}_STATES {nState}\n" ++
  s!"#define {p}_PRODS {t.prods.length}\n#define {p}_TOKEN_SORTS {s.tokenSorts.length}\n" ++
  s!"#define {p}_FIRST_TOKEN_SORT {nTerm - s.tokenSorts.length}\n" ++
  s!"#define {p}_START_SORT {L.sortIndex s.start}\n" ++
  s!"static const char *{p}_terminal_spelling[] = \{" ++ ", ".intercalate (L.terms.map fun
    | .lit w => quote w | .tok c => quote c | _ => "\"$eof\"") ++ "};\n" ++
  s!"static const int {p}_terminal_is_sort[] = \{" ++ ", ".intercalate (L.terms.map fun
    | .tok _ => "1" | _ => "0") ++ "};\n" ++
  s!"static const char *{p}_sort_name[] = \{" ++ ", ".intercalate (L.sorts.map quote) ++ "};\n" ++
  s!"static const char *{p}_prod_label[] = \{" ++ ", ".intercalate (t.prods.map fun q => quote q.label) ++ "};\n" ++
  s!"static const int {p}_prod_lhs[] = \{" ++ ", ".intercalate (t.prods.map fun q => toString (L.sortIndex q.lhs)) ++ "};\n" ++
  s!"static const int {p}_prod_len[] = \{" ++ ", ".intercalate (t.prods.map fun q => toString q.rhs.length) ++ "};\n" ++
  s!"static const int {p}_prod_rhs[][2 * 24] = \{" ++ ", ".intercalate (t.prods.map fun q =>
    if q.rhs.isEmpty then "{0}" else
    "{" ++ ", ".intercalate (q.rhs.map fun x => match x with
      | .nt n => s!"1, {L.sortIndex n}" | y => s!"0, {L.termIndex y}") ++ "}") ++ "};\n" ++
  s!"#define {p}_ACCEPT 1000000\n" ++
  s!"static const int {p}_action[{nState}][{nTerm}] = \{\n" ++ ",\n".intercalate ((List.range nState).map fun st =>
    "  {" ++ ", ".intercalate (L.terms.map (actionCell st)) ++ "}") ++ "\n};\n" ++
  s!"static const int {p}_goto[{nState}][{nSort}] = \{\n" ++ ",\n".intercalate ((List.range nState).map fun st =>
    "  {" ++ ", ".intercalate (L.sorts.map (gotoCell st)) ++ "}") ++ "\n};\n" ++
  s!"#define {p}_BINARY 1\n" ++
  s!"#define {p}_VARUINT_INLINE {prof.inline}\n" ++
  s!"static const int {p}_class_kind[] = \{" ++ ", ".intercalate (prof.classes.map fun c =>
    toString c.kind.code) ++ "};\n" ++
  s!"static const unsigned char {p}_class_bytes[{s.tokenSorts.length}][256] = \{\n" ++
    ",\n".intercalate (prof.classes.map fun c => byteRow c.kind.byteSet) ++ "\n};\n"

/-! ## Controls -/

/-- Words with 247 as the largest one-byte value: `0`, `247`, `248`, `300`, and the largest
64-bit value. -/
theorem encodeWord_controls :
    encodeWord 247 0 = [0] ∧ encodeWord 247 247 = [247] ∧ encodeWord 247 248 = [248, 248] ∧
      encodeWord 247 300 = [249, 44, 1] ∧
      encodeWord 247 (2 ^ 64 - 1) = [255, 255, 255, 255, 255, 255, 255, 255, 255] := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩ <;> simp [encodeWord]

/-- Refusals: a value that fits in one byte written with a header (`248 5`), a payload ending in a
zero byte (`249 44 0`), a header whose payload is cut short (`249 44`); accepted: `248 248`. -/
theorem wordLen?_controls :
    wordLen? 247 [248, 5] = none ∧ wordLen? 247 [249, 44, 0] = none ∧
      wordLen? 247 [249, 44] = none ∧ wordLen? 247 [248, 248, 7] = some 2 ∧
      wordLen? 247 [7, 248] = some 1 := by
  decide

/-- The scanner: two words after a count of two; three bytes after a count of three; a list or
bytes with no count before them is refused. -/
theorem scan_controls :
    Kind.words.scanLen? 247 (some 2) [5, 249, 44, 1, 9] = some 4 ∧
      Kind.bytes.scanLen? 247 (some 3) [104, 105, 33, 7] = some 3 ∧
      Kind.bytes.scanLen? 247 (some 5) [104, 105] = none ∧
      Kind.words.scanLen? 247 none [5] = none ∧
      Kind.count.nextReg none [249, 44, 1] = some 300 := by
  decide

/-- `splitWords?`: the words of a list, and a refusal for a non-shortest word inside it. -/
theorem splitWords_controls :
    splitWords? 247 [5, 249, 44, 1] = some [5, 300] ∧ splitWords? 247 [5, 248, 5] = none ∧
      splitWords? 247 [] = some [] := by
  decide

end Mettapedia.GSLT.Readers.BinaryTokens
