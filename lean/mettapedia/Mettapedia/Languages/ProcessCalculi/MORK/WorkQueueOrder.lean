import Mettapedia.Languages.ProcessCalculi.MORK.Conformance

/-!
# MORK: Work-Queue Location Ordering

Defines a structural ordering on `Atom` that approximates the PathMap byte order
used by the real MORK runtime to schedule exec facts.

## PathMap byte ordering (reference)

PathMap is a 256-radix trie. Tag bytes determine the first level of ordering:
- `[n]` (Arity tag, byte < 0x40) — expressions
- `<n>` (SymbolSize tag, byte 0x40–0x7F) — symbols
- `$` (NewVar tag, byte 0xC0) — variables
- `&i` (VarRef tag, byte 0x80–0xBF) — variable references

This means expressions sort before symbols, symbols before variables.
Within symbols, shorter names sort before longer (smaller SymbolSize tag byte).
Within the same length, lexicographic by raw ASCII bytes.

## Approximation

`atomKey : Atom → List ℕ` assigns a `List ℕ` key that preserves the relative
ordering of the PathMap byte representation for the common cases:
- `(N name)` location tuples with numeric or symbolic priorities
- Nested tuple priorities like `($p (1 (0)))`

This is NOT byte-identical to PathMap serialization. A future refinement module
can connect `atomKey` to exact byte encoding.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Lexicographic comparison -/

/-- Lexicographic comparison of `List ℕ`. -/
def lexLt : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
    if x < y then true
    else if x > y then false
    else lexLt xs ys

/-! ## Atom key for ordering -/

/-- Convert a `GroundedValue` to a string representation for key generation. -/
private def groundedToChars : GroundedValue → List Char
  | .int n    => toString n |>.toList
  | .string s => s.toList
  | .bool b   => (if b then "True" else "False").toList
  | .custom t d => (t ++ ":" ++ d).toList

/-- Structural key for ordering atoms, approximating PathMap byte order.

    Key prefix encodes the tag-byte ordering:
    - `0` → expression (Arity tag, byte < 0x40)
    - `1` → symbol / grounded (SymbolSize tag, byte 0x40+)
    - `3` → variable (NewVar/VarRef tag, byte 0x80+)

    For symbols: length then char values (mirrors SymbolSize then raw bytes).
    For expressions: arity then recursive keys of children. -/
def atomKey : Atom → List ℕ
  | .expression es => 0 :: es.length :: atomKeyList es
  | .symbol s      => let cs := s.toList; 1 :: cs.length :: cs.map (·.toNat)
  | .grounded g    => let cs := groundedToChars g; 1 :: cs.length :: cs.map (·.toNat)
  | .var v         => let cs := v.toList; 3 :: cs.length :: cs.map (·.toNat)
where
  atomKeyList : List Atom → List ℕ
    | []      => []
    | a :: as => atomKey a ++ atomKeyList as

/-! ## Ordering canaries

All proofs are `rfl` (kernel-checked). -/

section OrderCanaries

/-- `(0 a)` < `(0 b)`: same priority, name "a" < "b" lexicographically. -/
theorem order_0a_lt_0b :
    lexLt (atomKey (.expression [.symbol "0", .symbol "a"]))
          (atomKey (.expression [.symbol "0", .symbol "b"])) = true := rfl

/-- `(0 x)` < `(1 x)`: priority 0 < priority 1 (ASCII '0' < '1'). -/
theorem order_p0_lt_p1 :
    lexLt (atomKey (.expression [.symbol "0", .symbol "x"]))
          (atomKey (.expression [.symbol "1", .symbol "x"])) = true := rfl

/-- `(1 x)` < `(10 x)`: single-digit < double-digit (shortlex on symbol length). -/
theorem order_1_lt_10 :
    lexLt (atomKey (.expression [.symbol "1", .symbol "x"]))
          (atomKey (.expression [.symbol "10", .symbol "x"])) = true := rfl

/-- `(0 (0))` < `(1 (0))`: nested tuple priorities, first child determines order. -/
theorem order_nested_00_lt_10 :
    lexLt (atomKey (.expression [.symbol "0", .expression [.symbol "0"]]))
          (atomKey (.expression [.symbol "1", .expression [.symbol "0"]])) = true := rfl

/-- Expressions sort before symbols (arity tag < symbol tag in PathMap). -/
theorem order_expr_lt_symbol :
    lexLt (atomKey (.expression [.symbol "a"]))
          (atomKey (.symbol "a")) = true := rfl

/-- Shorter symbols sort before longer symbols. -/
theorem order_short_lt_long :
    lexLt (atomKey (.symbol "a"))
          (atomKey (.symbol "ab")) = true := rfl

/-- Variables sort after symbols. -/
theorem order_symbol_lt_var :
    lexLt (atomKey (.symbol "x"))
          (atomKey (.var "x")) = true := rfl

end OrderCanaries

/-! ## Structural properties of lexLt -/

/-- `lexLt` is asymmetric: `lexLt a b = true → lexLt b a = false`. -/
theorem lexLt_asymm : ∀ (a b : List ℕ), lexLt a b = true → lexLt b a = false
  | [], [] => by simp [lexLt]
  | [], _ :: _ => by simp [lexLt]
  | _ :: _, [] => by simp [lexLt]
  | x :: xs, y :: ys => by
    unfold lexLt
    by_cases hxy : x < y
    · simp only [hxy, ite_true]
      intro _
      have : ¬(y < x) := by omega
      have : y > x := by omega
      simp [*]
    · by_cases hgt : x > y
      · simp only [hxy, ite_false, hgt, ite_true]
        intro h; exact absurd h Bool.noConfusion
      · have hxeq : x = y := by omega
        subst hxeq
        simp only [show ¬(x < x) from Nat.lt_irrefl x, ite_false]
        exact lexLt_asymm xs ys

/-- If neither `lexLt a b` nor `lexLt b a`, then `a = b`. -/
theorem lexLt_eq_of_not_both : ∀ (a b : List ℕ),
    lexLt a b = false → lexLt b a = false → a = b
  | [], [] => by intros; rfl
  | [], _ :: _ => by simp [lexLt]
  | _ :: _, [] => by simp [lexLt]
  | x :: xs, y :: ys => by
    unfold lexLt
    by_cases hxy : x < y
    · simp only [hxy, ite_true]; intro h; exact absurd h Bool.noConfusion
    · by_cases hgt : x > y
      · simp only [hxy, ite_false, hgt, ite_true]; intro _ h
        exact absurd h Bool.noConfusion
      · have hxeq : x = y := by omega
        subst hxeq
        simp only [show ¬(x < x) from Nat.lt_irrefl x, ite_false]
        intro h1 h2
        congr 1; exact lexLt_eq_of_not_both xs ys h1 h2

/-- `lexLt` is transitive. -/
theorem lexLt_trans : ∀ (a b c : List ℕ),
    lexLt a b = true → lexLt b c = true → lexLt a c = true
  | [], [], _ => by simp [lexLt]
  | [], _ :: _, [] => by simp [lexLt]
  | [], _ :: _, _ :: _ => by simp [lexLt]
  | _ :: _, _, [] => by
    intro h1 h2; cases ‹List ℕ› <;> simp [lexLt] at h2
  | x :: xs, [], _ => by simp [lexLt]
  | x :: xs, y :: ys, z :: zs => by
    unfold lexLt
    by_cases hxy : x < y
    · simp only [hxy, ite_true]; intro _
      by_cases hyz : y < z
      · simp only [hyz, ite_true]; intro _
        simp only [show x < z from by omega, ite_true]
      · simp only [hyz, ite_false]
        by_cases hyz2 : y > z
        · simp only [hyz2, ite_true]; intro h; exact absurd h Bool.noConfusion
        · have hyeq : y = z := by omega
          subst hyeq
          simp only [show ¬(y > y) from by omega, ite_false]
          intro _; simp only [show x < y from hxy, ite_true]
    · simp only [hxy, ite_false]
      by_cases hxy2 : x > y
      · simp only [hxy2, ite_true]; intro h; exact absurd h Bool.noConfusion
      · have hxeq : x = y := by omega
        subst hxeq
        simp only [show ¬(x > x) from by omega, ite_false]
        intro h1
        by_cases hxz : x < z
        · simp only [hxz, ite_true]; intro _; simp
        · simp only [hxz, ite_false]
          by_cases hxz2 : x > z
          · simp only [hxz2, ite_true]; intro h; exact absurd h Bool.noConfusion
          · have hxzeq : x = z := by omega
            subst hxzeq
            simp only [show ¬(x > x) from by omega, ite_false]
            exact lexLt_trans xs ys zs h1

/-! ## Irreflexivity -/

/-- `lexLt` is irreflexive. -/
theorem lexLt_irrefl : ∀ (a : List ℕ), lexLt a a = false
  | [] => rfl
  | x :: xs => by
    simp only [lexLt, show ¬(x < x) from Nat.lt_irrefl x, ite_false]
    exact lexLt_irrefl xs

/-! ## Bridge to Mathlib's `List.Lex`

Connects the computable `lexLt` to Mathlib's `List.Lex (· < ·)`,
which provides a `LinearOrder (List ℕ)` instance via `Mathlib.Data.List.Lex`. -/

/-- `lexLt` agrees with Mathlib's `List.Lex (· < ·)`. -/
theorem lexLt_iff_lex : ∀ (a b : List ℕ),
    lexLt a b = true ↔ List.Lex (· < ·) a b
  | [], [] => by simp [lexLt]
  | [], _ :: _ => by simp [lexLt]
  | _ :: _, [] => by simp [lexLt]
  | x :: xs, y :: ys => by
    unfold lexLt
    by_cases hxy : x < y
    · simp only [hxy, ite_true]
      exact ⟨fun _ => List.Lex.rel hxy, fun _ => trivial⟩
    · simp only [hxy, ite_false]
      by_cases hgt : x > y
      · simp only [hgt, ite_true]
        exact ⟨Bool.noConfusion, fun h => by cases h with
          | rel h => exact absurd h hxy
          | cons h => omega⟩
      · have heq : x = y := by omega
        subst heq
        simp only [show ¬(x > x) from by omega, ite_false]
        constructor
        · intro h; exact .cons ((lexLt_iff_lex xs ys).mp h)
        · intro h; cases h with
          | rel h => exact absurd h hxy
          | cons h => exact (lexLt_iff_lex xs ys).mpr h

/-! ## Exec-location fragment

The exec-location fragment is the subset of `Atom` that `extractExecFact`
recognizes as well-formed location tuples: `(priority_string name_string)`.
On this fragment, `atomKey` is injective and the ordering is shortlex on
the priority string followed by shortlex on the name string. -/

/-- Well-formed exec location: a 2-element expression with symbol children.
    Covers `(priority name)` tuples as used by `extractExecFact`. -/
def schedulerLocFragment (loc : Atom) : Prop :=
  ∃ (p n : String), loc = .expression [.symbol p, .symbol n]

/-- Extract priority and name strings from a well-formed location. -/
def locToPriorityName : Atom → Option (String × String)
  | .expression [.symbol p, .symbol n] => some (p, n)
  | _ => none

/-- `locToPriorityName` succeeds on fragment members. -/
theorem locToPriorityName_of_fragment {loc : Atom} (h : schedulerLocFragment loc) :
    ∃ p n, locToPriorityName loc = some (p, n) := by
  obtain ⟨p, n, rfl⟩ := h
  exact ⟨p, n, rfl⟩

/-- `List.map Char.toNat` is injective (char-to-nat encoding is faithful). -/
private theorem map_char_toNat_injective :
    ∀ (l1 l2 : List Char), l1.map Char.toNat = l2.map Char.toNat → l1 = l2
  | [], [] => fun _ => rfl
  | [], _ :: _ => fun h => by simp at h
  | _ :: _, [] => fun h => by simp at h
  | c1 :: cs1, c2 :: cs2 => fun h => by
    simp only [List.map_cons, List.cons.injEq] at h
    have hc : c1 = c2 := by
      exact Char.ext (UInt32.ext h.1)
    have hcs := map_char_toNat_injective cs1 cs2 h.2
    exact congrArg₂ (· :: ·) hc hcs

/-- `atomKey` is injective on the exec-location fragment. -/
theorem atomKey_injective_on_fragment (loc1 loc2 : Atom)
    (h1 : schedulerLocFragment loc1) (h2 : schedulerLocFragment loc2)
    (heq : atomKey loc1 = atomKey loc2) : loc1 = loc2 := by
  obtain ⟨p1, n1, rfl⟩ := h1
  obtain ⟨p2, n2, rfl⟩ := h2
  -- atomKey (.expression [.symbol p, .symbol n]) =
  --   0 :: 2 :: atomKey (.symbol p) ++ atomKey (.symbol n) ++ []
  -- = 0 :: 2 :: 1 :: p.len :: p.chars ++ 1 :: n.len :: n.chars ++ []
  simp only [atomKey, atomKey.atomKeyList, List.length_cons, List.length_nil,
    List.append_nil] at heq
  -- Now heq : 0 :: 2 :: 1 :: p1.len :: map(p1) ++ 1 :: n1.len :: map(n1) =
  --           0 :: 2 :: 1 :: p2.len :: map(p2) ++ 1 :: n2.len :: map(n2)
  -- Strip the leading 0 :: 2 :: 1
  have h3 := (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).2
  -- h3 : p1.len :: map(p1) ++ ... = p2.len :: map(p2) ++ ...
  have hp_len : p1.toList.length = p2.toList.length :=
    (List.cons.inj h3).1
  -- The tails: map(p1) ++ ... = map(p2) ++ ...
  have h4 := (List.cons.inj h3).2
  -- Use List.append_inj with matching lengths
  have hsame_len : (List.map Char.toNat p1.toList).length =
      (List.map Char.toNat p2.toList).length := by
    simp [hp_len]
  obtain ⟨hp_map_eq, hn_tail⟩ := List.append_inj h4 hsame_len
  -- hp_map_eq : map(p1) = map(p2)
  -- hn_tail : 1 :: n1.len :: map(n1) = 1 :: n2.len :: map(n2)
  have hp : p1 = p2 :=
    String.ext (map_char_toNat_injective _ _ hp_map_eq)
  have hn_map_eq := (List.cons.inj (List.cons.inj hn_tail).2).2
  have hn : n1 = n2 :=
    String.ext (map_char_toNat_injective _ _ hn_map_eq)
  subst hp; subst hn; rfl

/-! ### Fragment ordering canaries -/

section FragmentCanaries

/-- Priority "5" < "10": shortlex orders single-digit before double-digit. -/
theorem order_p5_lt_p10 :
    lexLt (atomKey (.expression [.symbol "5", .symbol "x"]))
          (atomKey (.expression [.symbol "10", .symbol "x"])) = true := rfl

/-- Same priority, name "a" < "c": same-length names, lex on first differing char. -/
theorem order_same_prio_a_lt_c :
    lexLt (atomKey (.expression [.symbol "0", .symbol "a"]))
          (atomKey (.expression [.symbol "0", .symbol "c"])) = true := rfl

/-- Priority "9" < "10": shortlex works because "9" has length 1 < length 2. -/
theorem order_p9_lt_p10 :
    lexLt (atomKey (.expression [.symbol "9", .symbol "x"]))
          (atomKey (.expression [.symbol "10", .symbol "x"])) = true := rfl

/-- Phase-band ordering: unfold (priority 0) < base (priority 32). -/
theorem order_unfold_lt_base_concrete :
    lexLt (atomKey (.expression [.symbol "0", .symbol "rule1"]))
          (atomKey (.expression [.symbol "32", .symbol "rule2"])) = true := rfl

/-- Phase-band ordering: base (priority 32) < fold (priority 64). -/
theorem order_base_lt_fold_concrete :
    lexLt (atomKey (.expression [.symbol "32", .symbol "rule1"]))
          (atomKey (.expression [.symbol "64", .symbol "rule2"])) = true := rfl

end FragmentCanaries

/-! ## Semantic ordering on exec-location fragment

We define a semantic ordering `locLt` based on shortlex comparison of
(priority, name) string pairs, and prove it agrees with `lexLt ∘ atomKey`
on the `schedulerLocFragment`. -/

/-- Shortlex comparison on strings: shorter < longer; same length → lex on char codes. -/
def stringShortlexLt (s1 s2 : String) : Bool :=
  if s1.length < s2.length then true
  else if s1.length > s2.length then false
  else lexLt (s1.toList.map Char.toNat) (s2.toList.map Char.toNat)

/-- Semantic ordering on well-formed location atoms:
    shortlex on priority string, then shortlex on name string. -/
def locLt (loc1 loc2 : Atom) : Bool :=
  match locToPriorityName loc1, locToPriorityName loc2 with
  | some (p1, n1), some (p2, n2) =>
    if stringShortlexLt p1 p2 then true
    else if stringShortlexLt p2 p1 then false
    else stringShortlexLt n1 n2
  | _, _ => false

/-! ### Helper: lexLt decomposes over length-prefixed segments -/

/-- `lexLt (x :: xs) (x :: ys) = lexLt xs ys`: equal heads cancel. -/
private theorem lexLt_cons_eq (x : ℕ) (xs ys : List ℕ) :
    lexLt (x :: xs) (x :: ys) = lexLt xs ys := by
  simp [lexLt, Nat.lt_irrefl]

/-- `lexLt` with strictly smaller head = true. -/
private theorem lexLt_cons_lt (x y : ℕ) (xs ys : List ℕ) (h : x < y) :
    lexLt (x :: xs) (y :: ys) = true := by
  simp [lexLt, h, Nat.not_lt.mpr (Nat.le_of_lt h)]

/-- `lexLt` with strictly larger head = false. -/
private theorem lexLt_cons_gt (x y : ℕ) (xs ys : List ℕ) (h : y < x) :
    lexLt (x :: xs) (y :: ys) = false := by
  simp [lexLt, Nat.not_lt.mpr (Nat.le_of_lt h), h]

/-- When two lists of equal length are lex-equal, `lexLt` returns `false` for both directions. -/
private theorem lexLt_eq_of_equal : ∀ (l : List ℕ), lexLt l l = false
  | [] => rfl
  | x :: xs => by simp [lexLt, Nat.lt_irrefl, lexLt_eq_of_equal xs]

/-- `lexLt` on `x :: l1 ++ rest1` vs `y :: l2 ++ rest2` when `l1.length = l2.length`:
    first compare `x` vs `y`, then lex-compare `l1` vs `l2`, then fall through to rest. -/
private theorem lexLt_append_of_same_length :
    ∀ (l1 l2 : List ℕ) (rest1 rest2 : List ℕ),
      l1.length = l2.length →
      lexLt (l1 ++ rest1) (l2 ++ rest2) =
        if lexLt l1 l2 then true
        else if lexLt l2 l1 then false
        else lexLt rest1 rest2
  | [], [], rest1, rest2, _ => by simp [lexLt]
  | x :: xs, y :: ys, rest1, rest2, hlen => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    simp only [List.cons_append, lexLt]
    by_cases hxy : x < y
    · simp [hxy, Nat.not_lt.mpr (Nat.le_of_lt hxy)]
    · simp only [hxy, ite_false]
      by_cases hyx : y < x
      · simp [hyx, Nat.not_lt.mpr (Nat.le_of_lt hyx)]
      · have heq : x = y := Nat.le_antisymm (Nat.not_lt.mp hyx) (Nat.not_lt.mp hxy)
        simp only [hyx, heq, Nat.lt_irrefl, ite_false]
        exact lexLt_append_of_same_length xs ys rest1 rest2 hlen

/-- `lexLt` on length-prefixed segments decomposes into shortlex comparison.
    Note: explicit parens around `(l1 ++ rest1)` to avoid `::` vs `++` precedence. -/
private theorem lexLt_lengthPrefixed (l1 l2 rest1 rest2 : List ℕ) :
    lexLt (l1.length :: (l1 ++ rest1)) (l2.length :: (l2 ++ rest2)) =
      if l1.length < l2.length then true
      else if l2.length < l1.length then false
      else if lexLt l1 l2 then true
      else if lexLt l2 l1 then false
      else lexLt rest1 rest2 := by
  by_cases h1 : l1.length < l2.length
  · rw [lexLt_cons_lt _ _ _ _ h1]; (split_ifs; all_goals rfl)
  · by_cases h2 : l2.length < l1.length
    · rw [lexLt_cons_gt _ _ _ _ h2]; (split_ifs; all_goals rfl)
    · have hlen : l1.length = l2.length := by omega
      rw [hlen, lexLt_cons_eq]
      simp only [Nat.lt_irrefl, ite_false]
      exact lexLt_append_of_same_length l1 l2 rest1 rest2 hlen

/-- `lexLt` on a string's length-prefixed char list = `stringShortlexLt`. -/
private theorem lexLt_stringShortlex (s1 s2 : String) :
    lexLt (s1.toList.length :: s1.toList.map Char.toNat)
          (s2.toList.length :: s2.toList.map Char.toNat) =
      stringShortlexLt s1 s2 := by
  unfold stringShortlexLt
  simp only [show s1.length = s1.toList.length from rfl,
    show s2.length = s2.toList.length from rfl]
  by_cases h1 : s1.toList.length < s2.toList.length
  · rw [lexLt_cons_lt _ _ _ _ h1, if_pos h1]
  · by_cases h2 : s2.toList.length < s1.toList.length
    · rw [lexLt_cons_gt _ _ _ _ h2, if_neg h1, if_pos h2]
    · have heq : s1.toList.length = s2.toList.length := by omega
      rw [heq, lexLt_cons_eq]
      simp only [Nat.lt_irrefl, ite_false]

/-- `lexLt` on two length-prefixed string char lists with a separator.
    This handles the shape: `s1_len :: (s1_chars ++ (1 :: s2_len :: s2_chars))`. -/
private theorem lexLt_twoStrings (s1a s1b s2a s2b : String) :
    lexLt (s1a.toList.length :: (s1a.toList.map Char.toNat ++
             (1 :: s1b.toList.length :: s1b.toList.map Char.toNat)))
          (s2a.toList.length :: (s2a.toList.map Char.toNat ++
             (1 :: s2b.toList.length :: s2b.toList.map Char.toNat))) =
      (if stringShortlexLt s1a s2a then true
       else if stringShortlexLt s2a s1a then false
       else stringShortlexLt s1b s2b) := by
  by_cases h1 : s1a.toList.length < s2a.toList.length
  · rw [lexLt_cons_lt _ _ _ _ h1]
    have : stringShortlexLt s1a s2a = true := by
      unfold stringShortlexLt; exact if_pos h1
    simp only [this, ite_true]
  · by_cases h2 : s2a.toList.length < s1a.toList.length
    · rw [lexLt_cons_gt _ _ _ _ h2]
      have hf : stringShortlexLt s1a s2a = false := by
        unfold stringShortlexLt
        simp only [show s1a.length = s1a.toList.length from rfl,
          show s2a.length = s2a.toList.length from rfl]
        rw [if_neg h1, if_pos h2]
      have ht : stringShortlexLt s2a s1a = true := by
        unfold stringShortlexLt
        simp only [show s1a.length = s1a.toList.length from rfl,
          show s2a.length = s2a.toList.length from rfl]
        exact if_pos h2
      simp only [hf, ht]; simp
    · have hlen : s1a.toList.length = s2a.toList.length := by omega
      rw [hlen, lexLt_cons_eq]
      rw [lexLt_append_of_same_length _ _ _ _
            (by rw [List.length_map, List.length_map, hlen])]
      have hf1 : stringShortlexLt s1a s2a = lexLt (s1a.toList.map Char.toNat) (s2a.toList.map Char.toNat) := by
        unfold stringShortlexLt
        simp only [show s1a.length = s1a.toList.length from rfl,
          show s2a.length = s2a.toList.length from rfl]
        rw [if_neg h1, if_neg (show ¬ s1a.toList.length > s2a.toList.length from by omega)]
      have hf2 : stringShortlexLt s2a s1a = lexLt (s2a.toList.map Char.toNat) (s1a.toList.map Char.toNat) := by
        unfold stringShortlexLt
        simp only [show s1a.length = s1a.toList.length from rfl,
          show s2a.length = s2a.toList.length from rfl]
        rw [if_neg (show ¬ s2a.toList.length < s1a.toList.length from by omega),
            if_neg (show ¬ s2a.toList.length > s1a.toList.length from by omega)]
      simp only [hf1, hf2]
      split_ifs <;> rfl

/-! ### Main order characterization -/

/-- On the `schedulerLocFragment`, `lexLt ∘ atomKey` agrees with `locLt`.

    This means the scheduler's ordering (via `atomKey`) is exactly shortlex
    on (priority_string, name_string) for well-formed exec locations. -/
theorem atomKey_order_on_fragment (loc1 loc2 : Atom)
    (h1 : schedulerLocFragment loc1) (h2 : schedulerLocFragment loc2) :
    lexLt (atomKey loc1) (atomKey loc2) = locLt loc1 loc2 := by
  obtain ⟨p1, n1, rfl⟩ := h1
  obtain ⟨p2, n2, rfl⟩ := h2
  simp only [atomKey, atomKey.atomKeyList, List.length_cons, List.length_nil,
    List.append_nil]
  -- Strip identical prefix 0 :: 2 :: 1 ::
  rw [lexLt_cons_eq, lexLt_cons_eq]
  simp only [List.cons_append]
  rw [lexLt_cons_eq]
  -- Normalize anonymous lambda to Char.toNat
  simp only [show (fun x : Char => x.toNat) = Char.toNat from rfl]
  -- Apply the two-string decomposition
  rw [lexLt_twoStrings p1 n1 p2 n2]
  simp only [locLt, locToPriorityName]

/-! ### Derived properties of locLt -/

theorem locLt_irrefl (loc : Atom) (h : schedulerLocFragment loc) :
    locLt loc loc = false := by
  rw [← atomKey_order_on_fragment loc loc h h]
  exact lexLt_eq_of_equal (atomKey loc)

theorem locLt_asymm (loc1 loc2 : Atom)
    (h1 : schedulerLocFragment loc1) (h2 : schedulerLocFragment loc2)
    (hlt : locLt loc1 loc2 = true) : locLt loc2 loc1 = false := by
  rw [← atomKey_order_on_fragment loc1 loc2 h1 h2] at hlt
  rw [← atomKey_order_on_fragment loc2 loc1 h2 h1]
  exact lexLt_asymm (atomKey loc1) (atomKey loc2) hlt

theorem locLt_trans (loc1 loc2 loc3 : Atom)
    (h1 : schedulerLocFragment loc1) (h2 : schedulerLocFragment loc2)
    (h3 : schedulerLocFragment loc3)
    (h12 : locLt loc1 loc2 = true) (h23 : locLt loc2 loc3 = true) :
    locLt loc1 loc3 = true := by
  rw [← atomKey_order_on_fragment loc1 loc2 h1 h2] at h12
  rw [← atomKey_order_on_fragment loc2 loc3 h2 h3] at h23
  rw [← atomKey_order_on_fragment loc1 loc3 h1 h3]
  exact lexLt_trans (atomKey loc1) (atomKey loc2) (atomKey loc3) h12 h23

/-! ### locLt canaries -/

section LocLtCanaries

/-- Priority "5" < "10" via locLt. -/
theorem locLt_p5_lt_p10 :
    locLt (.expression [.symbol "5", .symbol "x"])
          (.expression [.symbol "10", .symbol "x"]) = true := rfl

/-- Same priority "0", name "a" < "c" via locLt. -/
theorem locLt_same_prio_a_lt_c :
    locLt (.expression [.symbol "0", .symbol "a"])
          (.expression [.symbol "0", .symbol "c"]) = true := rfl

/-- Phase-band: unfold (0) < base (32) via locLt. -/
theorem locLt_unfold_lt_base :
    locLt (.expression [.symbol "0", .symbol "r1"])
          (.expression [.symbol "32", .symbol "r2"]) = true := rfl

/-- Phase-band: base (32) < fold (64) via locLt. -/
theorem locLt_base_lt_fold :
    locLt (.expression [.symbol "32", .symbol "r1"])
          (.expression [.symbol "64", .symbol "r2"]) = true := rfl

end LocLtCanaries

end Mettapedia.Languages.ProcessCalculi.MORK
