import Mathlib.Computability.Language
import Mathlib.Data.List.TakeDrop

/-!
# Language-founded longest-prefix and leftmost-longest search

The algorithms query membership in a formal language. Their specifications
refer to that language independently of how its membership decision is
implemented. Empty matches are included, including at the end of the input.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages

universe u
variable {α : Type u}

/-- A bounded prefix whose word belongs to the language. -/
def PrefixMatch (L : Language α) (input : List α) (n : Nat) : Prop :=
  n ≤ input.length ∧ input.take n ∈ L

variable (L : Language α) [DecidablePred (· ∈ L)]

/-- Test prefix lengths in descending order, including the empty prefix. -/
private def longestPrefixUpTo (input : List α) : Nat → Option Nat
  | 0 => if input.take 0 ∈ L then some 0 else none
  | n + 1 => if input.take (n + 1) ∈ L then some (n + 1)
      else longestPrefixUpTo input n

private theorem longestPrefixUpTo_some_iff (input : List α) (k n : Nat) :
    longestPrefixUpTo L input k = some n ↔
      n ≤ k ∧ input.take n ∈ L ∧
        ∀ m, m ≤ k → input.take m ∈ L → m ≤ n := by
  induction k with
  | zero =>
    by_cases empty : input.take 0 ∈ L
    · simp only [longestPrefixUpTo, if_pos empty, Option.some.injEq]
      constructor
      · intro eq
        subst n
        exact ⟨by omega, empty, by omega⟩
      · intro h
        omega
    · rw [longestPrefixUpTo, if_neg empty]
      constructor
      · intro h
        cases h
      · intro h
        have : n = 0 := by omega
        exact False.elim (empty (this ▸ h.2.1))
  | succ k ih =>
    by_cases accepted : input.take (k + 1) ∈ L
    · simp only [longestPrefixUpTo, if_pos accepted, Option.some.injEq]
      constructor
      · intro eq
        subst n
        exact ⟨le_rfl, accepted, fun _ h _ => h⟩
      · intro h
        have := h.2.2 (k + 1) le_rfl accepted
        omega
    · rw [longestPrefixUpTo, if_neg accepted, ih]
      constructor
      · rintro ⟨bound, member, largest⟩
        refine ⟨by omega, member, ?_⟩
        intro m hm hmem
        by_cases lower : m ≤ k
        · exact largest m lower hmem
        · have : m = k + 1 := by omega
          exact False.elim (accepted (this ▸ hmem))
      · rintro ⟨bound, member, largest⟩
        have lower : n ≤ k := by
          by_contra h
          have : n = k + 1 := by omega
          exact accepted (this ▸ member)
        exact ⟨lower, member, fun m hm => largest m (by omega)⟩

/-- The longest accepted prefix, or `none` if even the empty prefix is rejected. -/
def longestPrefix (input : List α) : Option Nat :=
  longestPrefixUpTo L input input.length

theorem longestPrefix_some_iff (input : List α) (n : Nat) :
    longestPrefix L input = some n ↔
      PrefixMatch L input n ∧ ∀ m, PrefixMatch L input m → m ≤ n := by
  rw [longestPrefix, longestPrefixUpTo_some_iff]
  simp only [PrefixMatch]
  constructor
  · rintro ⟨bound, member, largest⟩
    exact ⟨⟨bound, member⟩, fun m h => largest m h.1 h.2⟩
  · rintro ⟨⟨bound, member⟩, largest⟩
    exact ⟨bound, member, fun m hm hmem => largest m ⟨hm, hmem⟩⟩

theorem longestPrefix_none_iff (input : List α) :
    longestPrefix L input = none ↔ ∀ n, ¬ PrefixMatch L input n := by
  constructor
  · intro result n accepted
    cases found : longestPrefix L input with
    | none =>
      unfold longestPrefix at found
      have absent : ∀ k, longestPrefixUpTo L input k = none →
          ∀ n, n ≤ k → input.take n ∉ L := by
        intro k
        induction k with
        | zero =>
          intro h n hn
          have : n = 0 := by omega
          subst n
          intro accepted
          have empty : [] ∈ L := by simpa using accepted
          simp [longestPrefixUpTo, empty] at h
        | succ k ih =>
          intro h n hn
          by_cases top : input.take (k + 1) ∈ L
          · simp [longestPrefixUpTo, top] at h
          · rw [longestPrefixUpTo, if_neg top] at h
            by_cases lower : n ≤ k
            · exact ih h n lower
            · have : n = k + 1 := by omega
              exact this ▸ top
      exact absent input.length found n accepted.1 accepted.2
    | some m => simp [result] at found
  · intro absent
    cases found : longestPrefix L input with
    | none => rfl
    | some n =>
      exact False.elim (absent n ((longestPrefix_some_iff L input n).mp found).1)

/-- A half-open substring interval, represented by its start and length. -/
structure MatchSpan where
  start : Nat
  length : Nat
  deriving DecidableEq, Repr

namespace MatchSpan

/-- The substring designated by a span. Bounds are stated separately. -/
def text (span : MatchSpan) (input : List α) : List α :=
  (input.drop span.start).take span.length

/-- Move a span one position to the right. -/
def shift (span : MatchSpan) : MatchSpan :=
  ⟨span.start + 1, span.length⟩

/-- Move a suffix-relative span into the original input's coordinates. -/
def shiftBy (offset : Nat) (span : MatchSpan) : MatchSpan :=
  ⟨offset + span.start, span.length⟩

theorem shift_predecessor (span : MatchSpan) (positive : 0 < span.start) :
    ({ start := span.start - 1, length := span.length } : MatchSpan).shift = span := by
  cases span
  dsimp only [shift] at positive ⊢
  congr 1
  omega

end MatchSpan

/-- A bounded substring belonging to the language. -/
def SpanMatch (input : List α) (span : MatchSpan) : Prop :=
  span.start + span.length ≤ input.length ∧ span.text input ∈ L

/-- Earliest accepted start, with the longest accepted substring at that start. -/
def LeftmostLongest (input : List α) (span : MatchSpan) : Prop :=
  SpanMatch L input span ∧
    (∀ other, SpanMatch L input other → span.start ≤ other.start) ∧
    ∀ other, SpanMatch L input other → other.start = span.start →
      other.length ≤ span.length

omit [DecidablePred (· ∈ L)] in
theorem spanMatch_zero_iff (input : List α) (n : Nat) :
    SpanMatch L input ⟨0, n⟩ ↔ PrefixMatch L input n := by
  simp [SpanMatch, MatchSpan.text, PrefixMatch]

omit [DecidablePred (· ∈ L)] in
theorem spanMatch_shift_iff (a : α) (input : List α) (span : MatchSpan) :
    SpanMatch L (a :: input) span.shift ↔ SpanMatch L input span := by
  simp only [SpanMatch, MatchSpan.shift, MatchSpan.text, List.drop_succ_cons,
    List.length_cons]
  constructor <;> intro h <;> exact ⟨by omega, h.2⟩

omit [DecidablePred (· ∈ L)] in
theorem spanMatch_shiftBy_iff (input : List α) (offset : Nat)
    (bounded : offset ≤ input.length) (span : MatchSpan) :
    SpanMatch L input (span.shiftBy offset) ↔ SpanMatch L (input.drop offset) span := by
  simp only [SpanMatch, MatchSpan.shiftBy, MatchSpan.text, List.drop_drop, List.length_drop]
  constructor <;> intro h <;> exact ⟨by omega, h.2⟩

/-- If the initial suffix has no accepted prefix, every match starts later. -/
theorem spanMatch_start_pos_of_longestPrefix_none (input : List α) (span : MatchSpan)
    (absent : longestPrefix L input = none) (matched : SpanMatch L input span) :
    0 < span.start := by
  by_contra hn
  have zero : span.start = 0 := by omega
  have acceptedPrefix : PrefixMatch L input span.length := by
    cases span with
    | mk start length =>
      simp only at zero
      subst start
      exact (spanMatch_zero_iff L input length).mp matched
  exact (longestPrefix_none_iff L input).mp absent _ acceptedPrefix

omit [DecidablePred (· ∈ L)] in
theorem leftmostLongest_unique (input : List α) {a b : MatchSpan}
    (ha : LeftmostLongest L input a) (hb : LeftmostLongest L input b) : a = b := by
  have starts : a.start = b.start := Nat.le_antisymm (ha.2.1 b hb.1) (hb.2.1 a ha.1)
  have lengths : a.length = b.length :=
    Nat.le_antisymm (hb.2.2 a ha.1 starts) (ha.2.2 b hb.1 starts.symm)
  cases a
  cases b
  simp_all

private theorem leftmostLongest_zero (input : List α) (n : Nat)
    (result : longestPrefix L input = some n) : LeftmostLongest L input ⟨0, n⟩ := by
  obtain ⟨accepted, largest⟩ := (longestPrefix_some_iff L input n).mp result
  refine ⟨(spanMatch_zero_iff L input n).mpr accepted, fun _ _ => Nat.zero_le _, ?_⟩
  intro other ho hs
  cases other with
  | mk start length =>
    simp only at hs
    subst start
    exact largest length ((spanMatch_zero_iff L input length).mp ho)

private theorem leftmostLongest_shift_iff (a : α) (input : List α)
    (absent : longestPrefix L (a :: input) = none) (span : MatchSpan) :
    LeftmostLongest L (a :: input) span.shift ↔ LeftmostLongest L input span := by
  constructor
  · intro h
    refine ⟨(spanMatch_shift_iff L a input span).mp h.1, ?_, ?_⟩
    · intro other ho
      have := h.2.1 other.shift ((spanMatch_shift_iff L a input other).mpr ho)
      simp only [MatchSpan.shift] at this
      omega
    · intro other ho hs
      exact h.2.2 other.shift ((spanMatch_shift_iff L a input other).mpr ho)
        (by simp [MatchSpan.shift, hs])
  · intro h
    refine ⟨(spanMatch_shift_iff L a input span).mpr h.1, ?_, ?_⟩
    · intro other ho
      have pos := spanMatch_start_pos_of_longestPrefix_none L (a :: input) other absent ho
      let previous : MatchSpan := ⟨other.start - 1, other.length⟩
      have restored : previous.shift = other := MatchSpan.shift_predecessor other pos
      have hp := (spanMatch_shift_iff L a input previous).mp (restored.symm ▸ ho)
      have := h.2.1 previous hp
      simp only [MatchSpan.shift]
      simp only [previous] at this
      omega
    · intro other ho hs
      have pos := spanMatch_start_pos_of_longestPrefix_none L (a :: input) other absent ho
      let previous : MatchSpan := ⟨other.start - 1, other.length⟩
      have restored : previous.shift = other := MatchSpan.shift_predecessor other pos
      have hp := (spanMatch_shift_iff L a input previous).mp (restored.symm ▸ ho)
      have starts : previous.start = span.start := by
        simp only [MatchSpan.shift] at hs
        simp only [previous]
        omega
      exact h.2.2 previous hp starts

/-- Scan suffixes from left to right, taking the longest prefix at the first
accepted position. The final empty suffix is scanned once. -/
def search : List α → Option MatchSpan
  | [] => (longestPrefix L []).map (fun n => ⟨0, n⟩)
  | a :: input => match longestPrefix L (a :: input) with
      | some n => some ⟨0, n⟩
      | none => (search input).map MatchSpan.shift

theorem search_some_iff (input : List α) (span : MatchSpan) :
    search L input = some span ↔ LeftmostLongest L input span := by
  induction input generalizing span with
  | nil =>
    cases hp : longestPrefix L [] with
    | none =>
      simp only [search, hp, Option.map_none]
      constructor
      · intro h
        cases h
      · intro h
        have bound := h.1.1
        simp only [List.length_nil] at bound
        have hs : span.start = 0 := by omega
        have hl : span.length = 0 := by omega
        have member : [] ∈ L := by simpa [MatchSpan.text, hl] using h.1.2
        exact False.elim ((longestPrefix_none_iff L []).mp hp 0 ⟨by simp, member⟩)
    | some n =>
      have canonical := leftmostLongest_zero L [] n hp
      simp only [search, hp, Option.map_some, Option.some.injEq]
      constructor
      · intro eq
        exact eq ▸ canonical
      · intro h
        exact leftmostLongest_unique L [] canonical h
  | cons a input ih =>
    cases hp : longestPrefix L (a :: input) with
    | some n =>
      have canonical := leftmostLongest_zero L (a :: input) n hp
      simp only [search, hp, Option.some.injEq]
      constructor
      · intro eq
        exact eq ▸ canonical
      · intro h
        exact leftmostLongest_unique L (a :: input) canonical h
    | none =>
      simp only [search, hp, Option.map_eq_some_iff]
      constructor
      · rintro ⟨previous, found, rfl⟩
        exact (leftmostLongest_shift_iff L a input hp previous).mpr ((ih previous).mp found)
      · intro h
        have positive := spanMatch_start_pos_of_longestPrefix_none L (a :: input) span hp h.1
        let previous : MatchSpan := ⟨span.start - 1, span.length⟩
        have restored : previous.shift = span := MatchSpan.shift_predecessor span positive
        refine ⟨previous, (ih previous).mpr ?_, restored⟩
        exact (leftmostLongest_shift_iff L a input hp previous).mp (restored.symm ▸ h)

theorem search_exists_of_match (input : List α) (span : MatchSpan)
    (matched : SpanMatch L input span) : ∃ found, search L input = some found := by
  induction input generalizing span with
  | nil =>
    have bound := matched.1
    simp only [List.length_nil] at bound
    have zero : span.length = 0 := by omega
    have member : [] ∈ L := by simpa [MatchSpan.text, zero] using matched.2
    have prefixMatch : PrefixMatch L [] 0 := ⟨by simp, member⟩
    cases h : longestPrefix L [] with
    | none => exact False.elim ((longestPrefix_none_iff L []).mp h 0 prefixMatch)
    | some n => exact ⟨⟨0, n⟩, by simp [search, h]⟩
  | cons a input ih =>
    cases hp : longestPrefix L (a :: input) with
    | some n => exact ⟨⟨0, n⟩, by simp [search, hp]⟩
    | none =>
      have positive := spanMatch_start_pos_of_longestPrefix_none L (a :: input) span hp matched
      let previous : MatchSpan := ⟨span.start - 1, span.length⟩
      have restored : previous.shift = span := MatchSpan.shift_predecessor span positive
      obtain ⟨found, hf⟩ := ih previous
        ((spanMatch_shift_iff L a input previous).mp (restored.symm ▸ matched))
      exact ⟨found.shift, by simp [search, hp, hf]⟩

theorem search_none_iff (input : List α) :
    search L input = none ↔ ∀ span, ¬ SpanMatch L input span := by
  constructor
  · intro absent span matched
    obtain ⟨found, hf⟩ := search_exists_of_match L input span matched
    simp [absent] at hf
  · intro absent
    cases found : search L input with
    | none => rfl
    | some span =>
      exact False.elim (absent span ((search_some_iff L input span).mp found).1)

theorem search_sound (input : List α) (span : MatchSpan)
    (found : search L input = some span) : SpanMatch L input span :=
  ((search_some_iff L input span).mp found).1

theorem search_leftmost (input : List α) (span : MatchSpan)
    (found : search L input = some span) (other : MatchSpan)
    (matched : SpanMatch L input other) : span.start ≤ other.start :=
  ((search_some_iff L input span).mp found).2.1 other matched

theorem search_longest (input : List α) (span : MatchSpan)
    (found : search L input = some span) (other : MatchSpan)
    (matched : SpanMatch L input other) (sameStart : other.start = span.start) :
    other.length ≤ span.length :=
  ((search_some_iff L input span).mp found).2.2 other matched sameStart

section Examples

private def oneOrTwoA : Language Char := fun word => word = ['a'] ∨ word = ['a', 'a']
private instance : DecidablePred (· ∈ oneOrTwoA) := fun _ => inferInstanceAs
  (Decidable (_ = ['a'] ∨ _ = ['a', 'a']))

/-- Ordered alternatives do not override longest-match selection. -/
theorem longestPrefix_oneOrTwoA : longestPrefix oneOrTwoA ['a', 'a'] = some 2 := by
  decide

theorem search_oneOrTwoA_leftmost_longest :
    search oneOrTwoA ['b', 'a', 'a', 'a'] = some ⟨1, 2⟩ := by
  decide

theorem search_oneOrTwoA_rejects : search oneOrTwoA ['b', 'b'] = none := by
  decide

end Examples

end Mettapedia.Computability.RegularLanguages
