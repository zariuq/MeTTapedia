import Mettapedia.OSLF.MeTTaIL.Syntax
import Mathlib.Data.List.Sort
import Mettapedia.Data.List.CachedMergeSort

/-!
# A lexicographic order on patterns that a MeTTa runtime can evaluate

`ser` is a prefix-free serialization of the shared `Pattern` carrier into natural numbers;
`lexLe` compares serializations lexicographically. Both are simple structural recursions, so a
MeTTa runtime computes them directly, unlike the `Nat.pair` code of `PatternCode`, whose values
grow far too fast to compute outside proofs.

- `ser_injective`: distinct patterns have distinct serializations;
- `lexLe` is a total, transitive, antisymmetric order on serializations, hence `PatternLe` a linear
  order on patterns;
- `sortLex` (insertion sort by `PatternLe`) is a permutation and depends only on the presented
  multiset (`sortLex_eq_of_perm`).

The same definitions were first written for rho's lexicographic canonical form
(`RhoCalculus.LexCanonical`); they are language independent.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.PatternLexOrder

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A string as its length followed by its character codes. -/
def serString (s : String) : List Nat := s.length :: s.toList.map Char.toNat

def serOptString : Option String → List Nat
  | none => [0]
  | some s => 1 :: serString s

def serStringList (strings : List String) : List Nat := strings.length :: strings.flatMap serString

def collectionTag : CollType → Nat
  | .vec => 0
  | .hashBag => 1
  | .hashSet => 2

mutual
  /-- A prefix-free serialization of the shared `Pattern` carrier. -/
  def ser : Pattern → List Nat
    | .bvar index => [0, index]
    | .fvar name => 1 :: serString name
    | .apply constructor arguments => 2 :: serString constructor ++ arguments.length :: serList arguments
    | .lambda binder body => 3 :: serOptString binder ++ ser body
    | .multiLambda arity binders body => 4 :: arity :: serStringList binders ++ ser body
    | .subst body replacement => 5 :: ser body ++ ser replacement
    | .collection kind elements rest =>
        6 :: collectionTag kind :: elements.length :: serList elements ++ serOptString rest

  def serList : List Pattern → List Nat
    | [] => []
    | pattern :: patterns => ser pattern ++ serList patterns
end

/-! ## Prefix freedom -/

theorem codes_prefix : ∀ {left right : List Char} {rest rest' : List Nat},
    left.length = right.length →
    left.map Char.toNat ++ rest = right.map Char.toNat ++ rest' → left = right ∧ rest = rest'
  | [], [], _, _, _, same => ⟨rfl, by simpa using same⟩
  | _ :: _, [], _, _, lengths, _ => by simp at lengths
  | [], _ :: _, _, _, lengths, _ => by simp at lengths
  | a :: left, b :: right, rest, rest', lengths, same => by
    simp only [List.map_cons, List.cons_append, List.cons.injEq] at same
    have heads : a = b := by
      have := same.1
      exact Char.toNat_inj.mp this
    obtain ⟨tails, rests⟩ := codes_prefix (by simpa using lengths) same.2
    exact ⟨by rw [heads, tails], rests⟩

theorem serString_prefix {left right : String} {rest rest' : List Nat}
    (same : serString left ++ rest = serString right ++ rest') : left = right ∧ rest = rest' := by
  simp only [serString, List.cons_append, List.cons.injEq] at same
  have lengths : left.toList.length = right.toList.length := by
    rw [String.length_toList, String.length_toList]
    exact same.1
  obtain ⟨chars, rests⟩ := codes_prefix lengths same.2
  exact ⟨String.toList_inj.mp chars, rests⟩

theorem serOptString_prefix {left right : Option String} {rest rest' : List Nat}
    (same : serOptString left ++ rest = serOptString right ++ rest') : left = right ∧ rest = rest' := by
  cases left <;> cases right <;> simp only [serOptString, List.cons_append, List.cons.injEq, List.nil_append] at same
  · exact ⟨rfl, same.2⟩
  · simp at same
  · simp at same
  · obtain ⟨strings, rests⟩ := serString_prefix same.2
    exact ⟨by rw [strings], rests⟩

theorem serStrings_prefix : ∀ {left right : List String} {rest rest' : List Nat},
    left.length = right.length →
    left.flatMap serString ++ rest = right.flatMap serString ++ rest' → left = right ∧ rest = rest'
  | [], [], _, _, _, same => ⟨rfl, by simpa using same⟩
  | _ :: _, [], _, _, lengths, _ => by simp at lengths
  | [], _ :: _, _, _, lengths, _ => by simp at lengths
  | a :: left, b :: right, rest, rest', lengths, same => by
    simp only [List.flatMap_cons, List.append_assoc] at same
    obtain ⟨heads, tailsSame⟩ := serString_prefix same
    obtain ⟨tails, rests⟩ := serStrings_prefix (by simpa using lengths) tailsSame
    exact ⟨by rw [heads, tails], rests⟩

theorem serStringList_prefix {left right : List String} {rest rest' : List Nat}
    (same : serStringList left ++ rest = serStringList right ++ rest') : left = right ∧ rest = rest' := by
  simp only [serStringList, List.cons_append, List.cons.injEq] at same
  exact serStrings_prefix same.1 same.2

theorem collectionTag_injective : Function.Injective collectionTag := by
  intro left right same
  cases left <;> cases right <;> first | rfl | (simp [collectionTag] at same)

mutual
  theorem ser_prefix : ∀ (left right : Pattern) {rest rest' : List Nat},
      ser left ++ rest = ser right ++ rest' → left = right ∧ rest = rest'
    | .bvar a, .bvar b, rest, rest', same => by
      simp only [ser, List.cons_append, List.nil_append, List.cons.injEq] at same
      exact ⟨by rw [same.2.1], same.2.2⟩
    | .fvar a, .fvar b, rest, rest', same => by
      simp only [ser, List.cons_append, List.cons.injEq, true_and] at same
      obtain ⟨names, rests⟩ := serString_prefix same
      exact ⟨by rw [names], rests⟩
    | .apply c args, .apply d args', rest, rest', same => by
      simp only [ser, List.cons_append, List.append_assoc, List.cons.injEq, true_and] at same
      obtain ⟨names, afterName⟩ := serString_prefix same
      simp only [List.cons.injEq] at afterName
      obtain ⟨arguments, rests⟩ := serList_prefix args args' afterName.1 afterName.2
      exact ⟨by rw [names, arguments], rests⟩
    | .lambda a body, .lambda b body', rest, rest', same => by
      simp only [ser, List.cons_append, List.append_assoc, List.cons.injEq, true_and] at same
      obtain ⟨binders, afterBinder⟩ := serOptString_prefix same
      obtain ⟨bodies, rests⟩ := ser_prefix body body' afterBinder
      exact ⟨by rw [binders, bodies], rests⟩
    | .multiLambda n bs body, .multiLambda m cs body', rest, rest', same => by
      simp only [ser, List.cons_append, List.append_assoc, List.cons.injEq, true_and] at same
      obtain ⟨arities, afterArity⟩ := same
      obtain ⟨binders, afterBinders⟩ := serStringList_prefix afterArity
      obtain ⟨bodies, rests⟩ := ser_prefix body body' afterBinders
      exact ⟨by rw [arities, binders, bodies], rests⟩
    | .subst body replacement, .subst body' replacement', rest, rest', same => by
      simp only [ser, List.cons_append, List.append_assoc, List.cons.injEq, true_and] at same
      obtain ⟨bodies, afterBody⟩ := ser_prefix body body' same
      obtain ⟨replacements, rests⟩ := ser_prefix replacement replacement' afterBody
      exact ⟨by rw [bodies, replacements], rests⟩
    | .collection k es r, .collection k' es' r', rest, rest', same => by
      simp only [ser, List.cons_append, List.append_assoc, List.cons.injEq, true_and] at same
      obtain ⟨kinds, lengths, afterLength⟩ := same
      obtain ⟨elements, afterElements⟩ := serList_prefix es es' lengths afterLength
      obtain ⟨rests, remaining⟩ := serOptString_prefix afterElements
      exact ⟨by rw [collectionTag_injective kinds, elements, rests], remaining⟩
    | .bvar _, .fvar _, _, _, same | .bvar _, .apply _ _, _, _, same | .bvar _, .lambda _ _, _, _, same
    | .bvar _, .multiLambda _ _ _, _, _, same | .bvar _, .subst _ _, _, _, same
    | .bvar _, .collection _ _ _, _, _, same
    | .fvar _, .bvar _, _, _, same | .fvar _, .apply _ _, _, _, same | .fvar _, .lambda _ _, _, _, same
    | .fvar _, .multiLambda _ _ _, _, _, same | .fvar _, .subst _ _, _, _, same
    | .fvar _, .collection _ _ _, _, _, same
    | .apply _ _, .bvar _, _, _, same | .apply _ _, .fvar _, _, _, same | .apply _ _, .lambda _ _, _, _, same
    | .apply _ _, .multiLambda _ _ _, _, _, same | .apply _ _, .subst _ _, _, _, same
    | .apply _ _, .collection _ _ _, _, _, same
    | .lambda _ _, .bvar _, _, _, same | .lambda _ _, .fvar _, _, _, same | .lambda _ _, .apply _ _, _, _, same
    | .lambda _ _, .multiLambda _ _ _, _, _, same | .lambda _ _, .subst _ _, _, _, same
    | .lambda _ _, .collection _ _ _, _, _, same
    | .multiLambda _ _ _, .bvar _, _, _, same | .multiLambda _ _ _, .fvar _, _, _, same
    | .multiLambda _ _ _, .apply _ _, _, _, same | .multiLambda _ _ _, .lambda _ _, _, _, same
    | .multiLambda _ _ _, .subst _ _, _, _, same | .multiLambda _ _ _, .collection _ _ _, _, _, same
    | .subst _ _, .bvar _, _, _, same | .subst _ _, .fvar _, _, _, same | .subst _ _, .apply _ _, _, _, same
    | .subst _ _, .lambda _ _, _, _, same | .subst _ _, .multiLambda _ _ _, _, _, same
    | .subst _ _, .collection _ _ _, _, _, same
    | .collection _ _ _, .bvar _, _, _, same | .collection _ _ _, .fvar _, _, _, same
    | .collection _ _ _, .apply _ _, _, _, same | .collection _ _ _, .lambda _ _, _, _, same
    | .collection _ _ _, .multiLambda _ _ _, _, _, same | .collection _ _ _, .subst _ _, _, _, same => by
      simp [ser] at same

  theorem serList_prefix : ∀ (left right : List Pattern) {rest rest' : List Nat},
      left.length = right.length → serList left ++ rest = serList right ++ rest' → left = right ∧ rest = rest'
    | [], [], _, _, _, same => ⟨rfl, by simpa [serList] using same⟩
    | _ :: _, [], _, _, lengths, _ => by simp at lengths
    | [], _ :: _, _, _, lengths, _ => by simp at lengths
    | a :: left, b :: right, rest, rest', lengths, same => by
      simp only [serList, List.append_assoc] at same
      obtain ⟨heads, tailsSame⟩ := ser_prefix a b same
      obtain ⟨tails, rests⟩ := serList_prefix left right (by simpa using lengths) tailsSame
      exact ⟨by rw [heads, tails], rests⟩
end

theorem ser_injective : Function.Injective ser := by
  intro left right same
  exact (ser_prefix left right (rest := []) (rest' := []) (by rw [same])).1

/-- A computable linear order on patterns: lexicographic order of serializations. -/
@[reducible] def lexOrder : LinearOrder Pattern := LinearOrder.lift' ser ser_injective

/-! ## The comparator -/

/-- Lexicographic comparison of number lists; a proper prefix comes first. -/
def lexLe : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => decide (x < y) || (x == y && lexLe xs ys)

theorem lexLe_refl : ∀ xs : List Nat, lexLe xs xs = true
  | [] => rfl
  | x :: xs => by simp [lexLe, lexLe_refl xs]

theorem lexLe_total : ∀ xs ys : List Nat, lexLe xs ys = true ∨ lexLe ys xs = true
  | [], _ => Or.inl rfl
  | _ :: _, [] => Or.inr rfl
  | x :: xs, y :: ys => by
    rcases Nat.lt_trichotomy x y with less | same | more
    · left; simp [lexLe, less]
    · subst same
      rcases lexLe_total xs ys with first | second
      · left; simp [lexLe, first]
      · right; simp [lexLe, second]
    · right; simp [lexLe, more]

theorem lexLe_trans : ∀ xs ys zs : List Nat, lexLe xs ys = true → lexLe ys zs = true → lexLe xs zs = true
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, first, _ => by simp [lexLe] at first
  | _ :: _, _ :: _, [], _, second => by simp [lexLe] at second
  | x :: xs, y :: ys, z :: zs, first, second => by
    simp only [lexLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at first second ⊢
    rcases first with less | ⟨rfl, tail⟩
    · rcases second with less' | ⟨rfl, _⟩
      · exact Or.inl (Nat.lt_trans less less')
      · exact Or.inl less
    · rcases second with less' | ⟨rfl, tail'⟩
      · exact Or.inl less'
      · exact Or.inr ⟨rfl, lexLe_trans xs ys zs tail tail'⟩

theorem lexLe_antisymm : ∀ xs ys : List Nat, lexLe xs ys = true → lexLe ys xs = true → xs = ys
  | [], [], _, _ => rfl
  | [], _ :: _, _, second => by simp [lexLe] at second
  | _ :: _, [], first, _ => by simp [lexLe] at first
  | x :: xs, y :: ys, first, second => by
    simp only [lexLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at first second
    rcases first with less | ⟨rfl, tail⟩
    · rcases second with less' | ⟨same, _⟩
      · exact absurd (Nat.lt_trans less less') (Nat.lt_irrefl x)
      · subst same; exact absurd less (Nat.lt_irrefl _)
    · rcases second with less' | ⟨_, tail'⟩
      · exact absurd less' (Nat.lt_irrefl _)
      · rw [lexLe_antisymm xs ys tail tail']

/-- The order on patterns: lexicographic order of serializations. -/
def PatternLe (left right : Pattern) : Prop := lexLe (ser left) (ser right) = true

instance : DecidableRel PatternLe := fun left right => inferInstanceAs (Decidable (lexLe (ser left) (ser right) = true))

instance : Std.Total PatternLe := ⟨fun left right => lexLe_total (ser left) (ser right)⟩
instance : IsTrans Pattern PatternLe := ⟨fun first second third => lexLe_trans (ser first) (ser second) (ser third)⟩
instance : Std.Antisymm PatternLe :=
  ⟨fun left right first second => ser_injective (lexLe_antisymm (ser left) (ser right) first second)⟩

/-- Insertion sort by the lexicographic order. -/
def sortLex (patterns : List Pattern) : List Pattern := patterns.insertionSort PatternLe

/-- The lexicographic value agrees with merge sort using the same keys. -/
theorem sortLex_eq_mergeSort (patterns : List Pattern) :
    sortLex patterns = patterns.mergeSort (fun x y => lexLe (ser x) (ser y)) := by
  have compare_eq (first second : Pattern) :
      decide (PatternLe first second) = lexLe (ser first) (ser second) := by
    change decide (lexLe (ser first) (ser second) = true) = lexLe (ser first) (ser second)
    cases lexLe (ser first) (ser second) <;> rfl
  simpa only [sortLex, compare_eq] using
    (List.mergeSort_eq_insertionSort PatternLe patterns).symm

private def sortLexCached (patterns : List Pattern) : List Pattern :=
  List.mergeSortWithOrderedCheck ser lexLe patterns

@[csimp] theorem sortLex_eq_cached : sortLex = sortLexCached := by
  funext patterns
  exact (sortLex_eq_mergeSort patterns).trans
    (List.mergeSortWithOrderedCheck_eq ser lexLe lexLe_trans patterns).symm

theorem sortLex_perm (patterns : List Pattern) : List.Perm (sortLex patterns) patterns :=
  List.perm_insertionSort PatternLe patterns

theorem sortLex_pairwise (patterns : List Pattern) : List.Pairwise PatternLe (sortLex patterns) :=
  List.pairwise_insertionSort PatternLe patterns

/-- Sorting depends only on the presented multiset. -/
theorem sortLex_eq_of_perm {left right : List Pattern} (permutation : List.Perm left right) :
    sortLex left = sortLex right :=
  List.Perm.eq_of_pairwise' (sortLex_pairwise left) (sortLex_pairwise right)
    ((sortLex_perm left).trans (permutation.trans (sortLex_perm right).symm))

end Mettapedia.OSLF.MeTTaIL.PatternLexOrder
