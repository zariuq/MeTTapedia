import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness
import Mettapedia.Machines.Cursor.Fold

/-!
# Lexicographic canonical forms for pure rho

The library's canonical representative `Canonical.canonicalize` sorts parallel
components by `patternCode`, an injective `Nat.pair` code whose values grow far
too fast to compute outside proofs. An executable runtime needs an order it can
evaluate. This module orders components by the lexicographic order of a
prefix-free serialization, `ser`, and proves that nothing else changes:

- `lexCanon_eq`: the lexicographic form is the library's canonical form with
  every bare parallel bag re-sorted;
- `lexCanon_eq_iff`: two processes have the same lexicographic form exactly when
  they have the same canonical form, and `lexCanon_sound` places every process in
  the structural congruence class of its lexicographic form;
- `lexStep_complete`: every rho step, at any depth, is matched up to canonical
  form by a depth-one COMM on the lexicographic form;
- `lexCanon_channelsDecided`: on lexicographic forms, canonically equivalent
  channels are equal, so a literal matcher finds every communicating pair.

The sort is insertion sort by `lexLe` on serializations, both simple structural
recursions that a MeTTa runtime can carry out.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.LexCanonical

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

theorem sortLex_perm (patterns : List Pattern) : List.Perm (sortLex patterns) patterns :=
  List.perm_insertionSort PatternLe patterns

theorem sortLex_pairwise (patterns : List Pattern) : List.Pairwise PatternLe (sortLex patterns) :=
  List.pairwise_insertionSort PatternLe patterns

/-- Sorting depends only on the presented multiset. -/
theorem sortLex_eq_of_perm {left right : List Pattern} (permutation : List.Perm left right) :
    sortLex left = sortLex right :=
  List.Perm.eq_of_pairwise' (sortLex_pairwise left) (sortLex_pairwise right)
    ((sortLex_perm left).trans (permutation.trans (sortLex_perm right).symm))


/-! ## The lexicographic canonical form -/

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (bagSplice bagContents collapseBag normalizeQuote
  canonicalize canonicalizeList canonicalizeList_eq_map canonicalize_apply_general canonicalize_collection_general
  normalizeBagElements_eq_sort_bagContents sortPatterns_perm collapseBag_eq_bag_of_length_ge_two
  sortPatterns_eq_of_perm canonicalize_idempotent canonicalize_sound applyCongruence_of_forall₂
  collectionCongruence_of_forall₂)

mutual
  /-- The canonical form with bags sorted lexicographically. -/
  def lexCanon : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply "NQuote" [argument] => normalizeQuote (lexCanon argument)
    | .apply constructor arguments => .apply constructor (lexCanonList arguments)
    | .lambda binderName body => .lambda binderName (lexCanon body)
    | .multiLambda arity binderNames body => .multiLambda arity binderNames (lexCanon body)
    | .subst body replacement => .subst (lexCanon body) (lexCanon replacement)
    | .collection .hashBag elements none => collapseBag (sortLex (bagContents (lexCanonList elements)))
    | .collection collectionType elements rest => .collection collectionType (lexCanonList elements) rest

  def lexCanonList : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => lexCanon pattern :: lexCanonList patterns
end

mutual
  /-- Sort every bare parallel bag lexicographically, hereditarily, changing nothing else. -/
  def resortLex : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply constructor arguments => .apply constructor (resortLexList arguments)
    | .lambda binderName body => .lambda binderName (resortLex body)
    | .multiLambda arity binderNames body => .multiLambda arity binderNames (resortLex body)
    | .subst body replacement => .subst (resortLex body) (resortLex replacement)
    | .collection .hashBag elements none => .collection .hashBag (sortLex (resortLexList elements)) none
    | .collection collectionType elements rest => .collection collectionType (resortLexList elements) rest

  def resortLexList : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => resortLex pattern :: resortLexList patterns
end

theorem lexCanonList_eq_map : ∀ patterns : List Pattern, lexCanonList patterns = patterns.map lexCanon
  | [] => rfl
  | pattern :: patterns => by simp [lexCanonList, lexCanonList_eq_map patterns]

theorem resortLexList_eq_map : ∀ patterns : List Pattern, resortLexList patterns = patterns.map resortLex
  | [] => rfl
  | pattern :: patterns => by simp [resortLexList, resortLexList_eq_map patterns]

theorem lexCanon_apply_general (constructor : String) (arguments : List Pattern)
    (notQuote : ¬ (constructor = "NQuote" ∧ ∃ argument, arguments = [argument])) :
    lexCanon (.apply constructor arguments) = .apply constructor (lexCanonList arguments) := by
  unfold lexCanon
  split <;> simp_all

theorem lexCanon_collection_general (collectionType : CollType) (elements : List Pattern) (rest : Option String)
    (notParallel : ¬ (collectionType = .hashBag ∧ rest = none)) :
    lexCanon (.collection collectionType elements rest) = .collection collectionType (lexCanonList elements) rest := by
  unfold lexCanon
  split <;> simp_all

theorem resortLex_collection_general (collectionType : CollType) (elements : List Pattern) (rest : Option String)
    (notParallel : ¬ (collectionType = .hashBag ∧ rest = none)) :
    resortLex (.collection collectionType elements rest) =
      .collection collectionType (resortLexList elements) rest := by
  unfold resortLex
  split <;> simp_all

theorem resortLex_bag (elements : List Pattern) :
    resortLex (.collection .hashBag elements none) =
      .collection .hashBag (sortLex (elements.map resortLex)) none := by
  simp [resortLex, resortLexList_eq_map]

theorem resortLex_zero : resortLex (.apply "PZero" []) = .apply "PZero" [] := rfl

theorem resortLex_eq_zero_iff (pattern : Pattern) :
    resortLex pattern = .apply "PZero" [] ↔ pattern = .apply "PZero" [] := by
  constructor
  · intro same
    match pattern with
    | .bvar _ | .fvar _ => simp [resortLex] at same
    | .apply constructor arguments =>
      simp only [resortLex, Pattern.apply.injEq] at same
      obtain ⟨rfl, emptyArgs⟩ := same
      rw [resortLexList_eq_map, List.map_eq_nil_iff] at emptyArgs
      rw [emptyArgs]
    | .lambda _ _ | .multiLambda _ _ _ | .subst _ _ => simp [resortLex] at same
    | .collection kind elements rest =>
      by_cases parallel : kind = .hashBag ∧ rest = none
      · obtain ⟨rfl, rfl⟩ := parallel
        simp [resortLex_bag] at same
      · rw [resortLex_collection_general kind elements rest parallel] at same
        simp at same
  · rintro rfl
    rfl

/-- `resortLex` keeps a bare parallel bag a bag and anything else not one. -/
theorem bagSplice_resortLex (pattern : Pattern) :
    List.Perm (bagSplice (resortLex pattern)) ((bagSplice pattern).map resortLex) := by
  by_cases parallel : ∃ elements, pattern = .collection .hashBag elements none
  · obtain ⟨elements, rfl⟩ := parallel
    rw [resortLex_bag]
    simpa [bagSplice] using sortLex_perm (elements.map resortLex)
  · have notBag : ∀ elements, resortLex pattern ≠ .collection .hashBag elements none := by
      intro elements same
      match pattern with
      | .bvar _ | .fvar _ | .apply _ _ | .lambda _ _ | .multiLambda _ _ _ | .subst _ _ =>
        simp [resortLex] at same
      | .collection kind inner rest =>
        by_cases bare : kind = .hashBag ∧ rest = none
        · obtain ⟨rfl, rfl⟩ := bare
          exact parallel ⟨inner, rfl⟩
        · rw [resortLex_collection_general kind inner rest bare] at same
          simp only [Pattern.collection.injEq] at same
          exact bare ⟨same.1, same.2.2⟩
    have spliceSelf : bagSplice pattern = [pattern] := by
      unfold bagSplice
      split
      · rename_i elements
        exact absurd ⟨elements, rfl⟩ parallel
      · rfl
    have spliceResorted : bagSplice (resortLex pattern) = [resortLex pattern] := by
      unfold bagSplice
      split
      · rename_i elements same
        exact absurd same (notBag elements)
      · rfl
    rw [spliceSelf, spliceResorted]
    rfl

theorem resortLex_drop_inv {pattern name : Pattern} (same : resortLex pattern = .apply "PDrop" [name]) :
    ∃ original, pattern = .apply "PDrop" [original] ∧ name = resortLex original := by
  match pattern with
  | .apply constructor arguments =>
    simp only [resortLex, Pattern.apply.injEq, resortLexList_eq_map] at same
    obtain ⟨rfl, mapped⟩ := same
    match arguments, mapped with
    | [original], mapped =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
      exact ⟨original, rfl, mapped.symm⟩
  | .bvar _ | .fvar _ | .lambda _ _ | .multiLambda _ _ _ | .subst _ _ => simp [resortLex] at same
  | .collection kind elements rest =>
    by_cases bare : kind = .hashBag ∧ rest = none
    · obtain ⟨rfl, rfl⟩ := bare
      simp [resortLex_bag] at same
    · rw [resortLex_collection_general kind elements rest bare] at same
      simp at same

theorem normalizeQuote_resortLex (pattern : Pattern) :
    resortLex (normalizeQuote pattern) = normalizeQuote (resortLex pattern) := by
  by_cases dropped : ∃ name, pattern = .apply "PDrop" [name]
  · obtain ⟨name, rfl⟩ := dropped
    simp [normalizeQuote, resortLex, resortLexList]
  · have notDropped : ∀ name, resortLex pattern ≠ .apply "PDrop" [name] := by
      intro name same
      obtain ⟨original, rfl, _⟩ := resortLex_drop_inv same
      exact dropped ⟨original, rfl⟩
    have quoted : normalizeQuote pattern = .apply "NQuote" [pattern] := by
      unfold normalizeQuote
      split
      · rename_i name
        exact absurd ⟨name, rfl⟩ dropped
      · rfl
    have quotedResorted : normalizeQuote (resortLex pattern) = .apply "NQuote" [resortLex pattern] := by
      unfold normalizeQuote
      split
      · rename_i name same
        exact absurd same (notDropped name)
      · rfl
    rw [quoted, quotedResorted]
    simp [resortLex, resortLexList]

theorem flatMap_perm_of_forall {α β : Type} {f g : α → List β} :
    ∀ items : List α, (∀ item ∈ items, List.Perm (f item) (g item)) →
      List.Perm (items.flatMap f) (items.flatMap g)
  | [], _ => List.Perm.refl _
  | item :: items, pointwise => by
    simp only [List.flatMap_cons]
    exact (pointwise item List.mem_cons_self).append
      (flatMap_perm_of_forall items fun other member => pointwise other (List.mem_cons_of_mem _ member))

/-- Bag contents commute with lexicographic resorting, up to order. -/
theorem bagContents_map_resortLex (patterns : List Pattern) :
    List.Perm (bagContents (patterns.map resortLex)) ((bagContents patterns).map resortLex) := by
  unfold bagContents
  have spliced : List.Perm ((patterns.map resortLex).flatMap bagSplice)
      ((patterns.flatMap bagSplice).map resortLex) := by
    rw [List.flatMap_map, List.map_flatMap]
    exact flatMap_perm_of_forall patterns fun pattern _ => bagSplice_resortLex pattern
  have filtered := spliced.filter (fun pattern => decide (pattern ≠ .apply "PZero" []))
  rw [List.filter_map] at filtered
  have sameTest : ((fun pattern => decide (pattern ≠ Pattern.apply "PZero" [])) ∘ resortLex) =
      fun pattern => decide (pattern ≠ .apply "PZero" []) := by
    funext pattern
    simp [resortLex_eq_zero_iff]
  rw [sameTest] at filtered
  exact filtered

theorem sortLex_singleton (pattern : Pattern) : sortLex [pattern] = [pattern] := rfl

theorem resortLex_collapseBag (patterns : List Pattern) :
    resortLex (collapseBag patterns) = collapseBag (sortLex (patterns.map resortLex)) := by
  match patterns with
  | [] => rfl
  | [pattern] => simp [collapseBag, sortLex_singleton]
  | first :: second :: rest =>
    have twoElements : 2 ≤ (sortLex ((first :: second :: rest).map resortLex)).length := by
      rw [(sortLex_perm _).length_eq]
      simp
    rw [collapseBag_eq_bag_of_length_ge_two twoElements]
    simp [collapseBag, resortLex_bag]

mutual
  /-- **The lexicographic canonical form is the library's canonical form with every bare bag
  re-sorted.** -/
  theorem lexCanon_eq : ∀ pattern : Pattern, lexCanon pattern = resortLex (canonicalize pattern)
    | .bvar _ => rfl
    | .fvar _ => rfl
    | .apply constructor arguments => by
        by_cases isQuote : constructor = "NQuote" ∧ ∃ argument, arguments = [argument]
        · obtain ⟨rfl, argument, rfl⟩ := isQuote
          simp only [lexCanon, canonicalize]
          rw [lexCanon_eq argument, normalizeQuote_resortLex]
        · rw [lexCanon_apply_general constructor arguments isQuote,
            canonicalize_apply_general constructor arguments isQuote]
          simp only [resortLex, lexCanonList_eq_map, resortLexList_eq_map, canonicalizeList_eq_map, List.map_map]
          rw [lexCanon_map_eq arguments]
    | .lambda binderName body => by
        simp only [lexCanon, canonicalize, resortLex]
        rw [lexCanon_eq body]
    | .multiLambda arity binderNames body => by
        simp only [lexCanon, canonicalize, resortLex]
        rw [lexCanon_eq body]
    | .subst body replacement => by
        simp only [lexCanon, canonicalize, resortLex]
        rw [lexCanon_eq body, lexCanon_eq replacement]
    | .collection collectionType elements rest => by
        by_cases bare : collectionType = .hashBag ∧ rest = none
        · obtain ⟨rfl, rfl⟩ := bare
          simp only [lexCanon, canonicalize, lexCanonList_eq_map, canonicalizeList_eq_map]
          rw [lexCanon_map_eq elements, ← List.map_map, normalizeBagElements_eq_sort_bagContents,
            resortLex_collapseBag, sortLex_eq_of_perm (bagContents_map_resortLex _),
            sortLex_eq_of_perm (((sortPatterns_perm _).symm).map resortLex)]
        · rw [lexCanon_collection_general collectionType elements rest bare,
            canonicalize_collection_general collectionType elements rest bare,
            resortLex_collection_general collectionType (canonicalizeList elements) rest bare]
          simp only [lexCanonList_eq_map, resortLexList_eq_map, canonicalizeList_eq_map, List.map_map]
          rw [lexCanon_map_eq elements]

  theorem lexCanon_map_eq : ∀ patterns : List Pattern,
      patterns.map lexCanon = patterns.map (resortLex ∘ canonicalize)
    | [] => rfl
    | pattern :: patterns => by
        simp only [List.map_cons, Function.comp_apply]
        rw [lexCanon_eq pattern, lexCanon_map_eq patterns]
end

/-! ## Equal lexicographic forms are equal canonical forms -/

theorem bagContents_perm {left right : List Pattern} (permutation : List.Perm left right) :
    List.Perm (bagContents left) (bagContents right) := by
  unfold bagContents
  exact (permutation.flatMap_right bagSplice).filter _

mutual
  /-- Re-sorting bags never changes the library's canonical form. -/
  theorem canonicalize_resortLex : ∀ pattern : Pattern, canonicalize (resortLex pattern) = canonicalize pattern
    | .bvar _ => rfl
    | .fvar _ => rfl
    | .apply constructor arguments => by
        by_cases isQuote : constructor = "NQuote" ∧ ∃ argument, arguments = [argument]
        · obtain ⟨rfl, argument, rfl⟩ := isQuote
          simp only [resortLex, resortLexList, canonicalize]
          rw [canonicalize_resortLex argument]
        · have resortedQuote : ¬ (constructor = "NQuote" ∧ ∃ argument, resortLexList arguments = [argument]) := by
            rintro ⟨same, argument, single⟩
            rw [resortLexList_eq_map] at single
            match arguments, single with
            | [original], _ => exact isQuote ⟨same, original, rfl⟩
          simp only [resortLex]
          rw [canonicalize_apply_general constructor _ resortedQuote,
            canonicalize_apply_general constructor arguments isQuote]
          simp only [canonicalizeList_eq_map, resortLexList_eq_map, List.map_map]
          rw [canonicalize_resortLex_map arguments]
    | .lambda binderName body => by
        simp only [resortLex, canonicalize]
        rw [canonicalize_resortLex body]
    | .multiLambda arity binderNames body => by
        simp only [resortLex, canonicalize]
        rw [canonicalize_resortLex body]
    | .subst body replacement => by
        simp only [resortLex, canonicalize]
        rw [canonicalize_resortLex body, canonicalize_resortLex replacement]
    | .collection collectionType elements rest => by
        by_cases bare : collectionType = .hashBag ∧ rest = none
        · obtain ⟨rfl, rfl⟩ := bare
          rw [resortLex_bag]
          simp only [canonicalize, canonicalizeList_eq_map, normalizeBagElements_eq_sort_bagContents]
          congr 1
          apply sortPatterns_eq_of_perm
          apply bagContents_perm
          rw [← canonicalize_resortLex_map elements, ← List.map_map]
          exact (sortLex_perm _).map canonicalize
        · rw [resortLex_collection_general collectionType elements rest bare,
            canonicalize_collection_general collectionType _ rest bare,
            canonicalize_collection_general collectionType elements rest bare]
          simp only [canonicalizeList_eq_map, resortLexList_eq_map, List.map_map]
          rw [canonicalize_resortLex_map elements]

  theorem canonicalize_resortLex_map : ∀ patterns : List Pattern,
      patterns.map (canonicalize ∘ resortLex) = patterns.map canonicalize
    | [] => rfl
    | pattern :: patterns => by
        simp only [List.map_cons, Function.comp_apply]
        rw [canonicalize_resortLex pattern, canonicalize_resortLex_map patterns]
end

theorem canonicalize_lexCanon (pattern : Pattern) : canonicalize (lexCanon pattern) = canonicalize pattern := by
  rw [lexCanon_eq, canonicalize_resortLex, canonicalize_idempotent]

/-- **The lexicographic form decides structural congruence exactly as the library's form does.** -/
theorem lexCanon_eq_iff (left right : Pattern) :
    lexCanon left = lexCanon right ↔ canonicalize left = canonicalize right := by
  constructor
  · intro same
    rw [← canonicalize_lexCanon left, same, canonicalize_lexCanon]
  · intro same
    rw [lexCanon_eq, lexCanon_eq, same]

theorem lexCanon_idempotent (pattern : Pattern) : lexCanon (lexCanon pattern) = lexCanon pattern := by
  rw [lexCanon_eq (lexCanon pattern), canonicalize_lexCanon, ← lexCanon_eq]

mutual
  /-- Re-sorting bags is a structural congruence. -/
  theorem resortLex_sound : ∀ pattern : Pattern, StructuralCongruence pattern (resortLex pattern)
    | .bvar _ => StructuralCongruence.refl _
    | .fvar _ => StructuralCongruence.refl _
    | .apply constructor arguments => by
        simp only [resortLex]
        exact applyCongruence_of_forall₂ constructor (resortLexList_sound arguments)
    | .lambda binderName body =>
        StructuralCongruence.lambda_cong binderName body (resortLex body) (resortLex_sound body)
    | .multiLambda arity binderNames body =>
        StructuralCongruence.multiLambda_cong arity binderNames body (resortLex body) (resortLex_sound body)
    | .subst body replacement =>
        StructuralCongruence.subst_cong body (resortLex body) replacement (resortLex replacement)
          (resortLex_sound body) (resortLex_sound replacement)
    | .collection collectionType elements rest => by
        by_cases bare : collectionType = .hashBag ∧ rest = none
        · obtain ⟨rfl, rfl⟩ := bare
          simp only [resortLex]
          exact StructuralCongruence.trans _ _ _
            (collectionCongruence_of_forall₂ .hashBag none (resortLexList_sound elements))
            (StructuralCongruence.par_perm _ _ (sortLex_perm _).symm)
        · rw [resortLex_collection_general collectionType elements rest bare]
          exact collectionCongruence_of_forall₂ collectionType rest (resortLexList_sound elements)

  theorem resortLexList_sound : ∀ patterns : List Pattern,
      List.Forall₂ StructuralCongruence patterns (resortLexList patterns)
    | [] => List.Forall₂.nil
    | pattern :: patterns => List.Forall₂.cons (resortLex_sound pattern) (resortLexList_sound patterns)
end

/-- Every pattern is structurally congruent to its lexicographic form. -/
theorem lexCanon_sound (pattern : Pattern) : StructuralCongruence pattern (lexCanon pattern) := by
  rw [lexCanon_eq]
  exact StructuralCongruence.trans _ _ _ (canonicalize_sound pattern) (resortLex_sound _)

/-! ## Re-sorting keeps typing, quotation sealing and hash-set freedom -/

open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping (procListWellSorted_iff_forall_mem)
open Mettapedia.OSLF.MeTTaIL.ScopedPattern (binderSafeAt binderSafeListAt binderSafeListAt_eq_true_iff)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (HashSetFree HashSetFreeList)

/-- Resorting keeps the canonical form, hence quote admission. -/
private theorem quoteAdmits_resortLex (process : Pattern) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.quoteAdmits
        rhoReflectivePresentation.toReflectivePresentationDecl (resortLex process) =
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.quoteAdmits
        rhoReflectivePresentation.toReflectivePresentationDecl process :=
  Mettapedia.OSLF.MeTTaIL.ReflectiveQuoteAdmission.quoteAdmits_of_canonicalize_eq (by
    rw [CanonicalMatch.derivedCanonicalize_eq, CanonicalMatch.derivedCanonicalize_eq,
      canonicalize_resortLex])

mutual
  theorem resortLex_name {free : FreeSortContext} {bound : List String} {name : Pattern} :
      NameWellSorted rhoReflectivePresentation free bound name →
        NameWellSorted rhoReflectivePresentation free bound (resortLex name)
    | .bvar found => .bvar found
    | .fvar found => .fvar found
    | .quote processTyped admitted => by
        have resorted := NameWellSorted.quote (resortLex_proc processTyped)
          ((quoteAdmits_resortLex _).trans admitted)
        simpa [resortLex, resortLexList] using resorted

  theorem resortLex_proc {free : FreeSortContext} {bound : List String} {process : Pattern} :
      ProcWellSorted rhoReflectivePresentation free bound process →
        ProcWellSorted rhoReflectivePresentation free bound (resortLex process)
    | .bvar found => .bvar found
    | .fvar found => .fvar found
    | .unit => .unit
    | .drop nameTyped => by
        have resorted := ProcWellSorted.drop (resortLex_name nameTyped)
        simpa [resortLex, resortLexList] using resorted
    | .output channelTyped payloadTyped => by
        have resorted := ProcWellSorted.output (resortLex_name channelTyped) (resortLex_proc payloadTyped)
        simpa [resortLex, resortLexList] using resorted
    | .input channelTyped bodyTyped => by
        have resorted := ProcWellSorted.input (resortLex_name channelTyped) (resortLex_proc bodyTyped)
        simpa [resortLex, resortLexList] using resorted
    | .parallel processesTyped => by
        change ProcWellSorted rhoReflectivePresentation free bound (resortLex (.collection .hashBag _ none))
        rw [resortLex_bag]
        apply ProcWellSorted.parallel
        apply procListWellSorted_iff_forall_mem.mpr
        intro member membership
        exact procListWellSorted_iff_forall_mem.mp (resortLex_procList processesTyped) member
          ((sortLex_perm _).mem_iff.mp membership)

  theorem resortLex_procList {free : FreeSortContext} {bound : List String} {processes : List Pattern} :
      ProcListWellSorted rhoReflectivePresentation free bound processes →
        ProcListWellSorted rhoReflectivePresentation free bound (processes.map resortLex)
    | .nil => .nil
    | .cons head tail => .cons (resortLex_proc head) (resortLex_procList tail)
end

mutual
  theorem resortLex_binderSafe (quote : String) : ∀ (depth : Nat) (pattern : Pattern),
      binderSafeAt quote depth pattern = true → binderSafeAt quote depth (resortLex pattern) = true
    | _, .bvar _, safe => safe
    | _, .fvar _, safe => safe
    | depth, .apply constructor arguments, safe => by
        match arguments with
        | [body] =>
          simp only [resortLex, resortLexList, binderSafeAt] at safe ⊢
          split at safe
          · rename_i isQuote
            rw [if_pos isQuote]
            exact resortLex_binderSafe quote 0 body safe
          · rename_i isQuote
            rw [if_neg isQuote]
            simp only [binderSafeListAt, Bool.and_true] at safe ⊢
            exact resortLex_binderSafe quote depth body safe
        | [] => simpa [resortLex, resortLexList] using safe
        | first :: second :: rest =>
          have listSafe : binderSafeListAt quote depth (first :: second :: rest) = true := by
            simpa [binderSafeAt] using safe
          have resorted := resortLex_binderSafeList quote depth (first :: second :: rest) listSafe
          simp only [resortLex, resortLexList_eq_map, List.map_cons]
          simpa [binderSafeAt] using resorted
    | depth, .lambda binderName body, safe => by
        simp only [resortLex, binderSafeAt] at safe ⊢
        exact resortLex_binderSafe quote (depth + 1) body safe
    | depth, .multiLambda arity binderNames body, safe => by
        simp only [resortLex, binderSafeAt] at safe ⊢
        exact resortLex_binderSafe quote (depth + arity) body safe
    | depth, .subst body replacement, safe => by
        simp only [resortLex, binderSafeAt, Bool.and_eq_true] at safe ⊢
        exact ⟨resortLex_binderSafe quote (depth + 1) body safe.1,
          resortLex_binderSafe quote depth replacement safe.2⟩
    | depth, .collection collectionType elements rest, safe => by
        have listSafe : binderSafeListAt quote depth elements = true := by simpa [binderSafeAt] using safe
        have resorted := resortLex_binderSafeList quote depth elements listSafe
        by_cases bare : collectionType = .hashBag ∧ rest = none
        · obtain ⟨rfl, rfl⟩ := bare
          rw [resortLex_bag]
          simp only [binderSafeAt]
          apply (binderSafeListAt_eq_true_iff quote depth _).mpr
          intro member membership
          exact (binderSafeListAt_eq_true_iff quote depth _).mp resorted member
            ((sortLex_perm _).mem_iff.mp membership)
        · rw [resortLex_collection_general collectionType elements rest bare, resortLexList_eq_map]
          simpa [binderSafeAt] using resorted

  theorem resortLex_binderSafeList (quote : String) : ∀ (depth : Nat) (patterns : List Pattern),
      binderSafeListAt quote depth patterns = true →
        binderSafeListAt quote depth (patterns.map resortLex) = true
    | _, [], _ => rfl
    | depth, pattern :: patterns, safe => by
        simp only [binderSafeListAt, Bool.and_eq_true, List.map_cons] at safe ⊢
        exact ⟨resortLex_binderSafe quote depth pattern safe.1,
          resortLex_binderSafeList quote depth patterns safe.2⟩
end

theorem hashSetFreeList_iff_forall_mem : ∀ patterns : List Pattern,
    HashSetFreeList patterns ↔ ∀ pattern ∈ patterns, HashSetFree pattern
  | [] => by simp [HashSetFreeList]
  | pattern :: patterns => by
    simp only [HashSetFreeList, List.mem_cons, forall_eq_or_imp]
    rw [hashSetFreeList_iff_forall_mem patterns]

mutual
  theorem resortLex_hashSetFree : ∀ pattern : Pattern, HashSetFree pattern → HashSetFree (resortLex pattern)
    | .bvar _, free => free
    | .fvar _, free => free
    | .apply constructor arguments, free => by
        simp only [resortLex, HashSetFree] at free ⊢
        rw [resortLexList_eq_map]
        exact resortLex_hashSetFreeList arguments free
    | .lambda binderName body, free => by
        simp only [resortLex, HashSetFree] at free ⊢
        exact resortLex_hashSetFree body free
    | .multiLambda arity binderNames body, free => by
        simp only [resortLex, HashSetFree] at free ⊢
        exact resortLex_hashSetFree body free
    | .subst body replacement, free => by
        simp only [resortLex, HashSetFree] at free ⊢
        exact ⟨resortLex_hashSetFree body free.1, resortLex_hashSetFree replacement free.2⟩
    | .collection collectionType elements rest, free => by
        cases collectionType with
        | hashSet => simp [HashSetFree] at free
        | hashBag =>
          have listFree : HashSetFreeList elements := by
            cases rest <;> simpa [HashSetFree] using free
          have resorted := resortLex_hashSetFreeList elements listFree
          cases rest with
          | none =>
            rw [resortLex_bag]
            simp only [HashSetFree]
            apply (hashSetFreeList_iff_forall_mem _).mpr
            intro member membership
            exact (hashSetFreeList_iff_forall_mem _).mp resorted member ((sortLex_perm _).mem_iff.mp membership)
          | some name =>
            rw [resortLex_collection_general .hashBag elements (some name) (by simp), resortLexList_eq_map]
            simpa [HashSetFree] using resorted
        | vec =>
          have listFree : HashSetFreeList elements := by simpa [HashSetFree] using free
          rw [resortLex_collection_general .vec elements rest (by simp), resortLexList_eq_map]
          simpa [HashSetFree] using resortLex_hashSetFreeList elements listFree

  theorem resortLex_hashSetFreeList : ∀ patterns : List Pattern,
      HashSetFreeList patterns → HashSetFreeList (patterns.map resortLex)
    | [], _ => trivial
    | pattern :: patterns, free => by
        simp only [HashSetFreeList, List.map_cons] at free ⊢
        exact ⟨resortLex_hashSetFree pattern free.1, resortLex_hashSetFreeList patterns free.2⟩
end

mutual
  theorem name_hashSetFree {free : FreeSortContext} {bound : List String} {name : Pattern} :
      NameWellSorted rhoReflectivePresentation free bound name → HashSetFree name
    | .bvar _ => trivial
    | .fvar _ => trivial
    | .quote processTyped _ => by
        simp only [HashSetFree, HashSetFreeList]
        exact ⟨proc_hashSetFree processTyped, trivial⟩

  theorem proc_hashSetFree {free : FreeSortContext} {bound : List String} {process : Pattern} :
      ProcWellSorted rhoReflectivePresentation free bound process → HashSetFree process
    | .bvar _ => trivial
    | .fvar _ => trivial
    | .unit => trivial
    | .drop nameTyped => by
        simp only [HashSetFree, HashSetFreeList]
        exact ⟨name_hashSetFree nameTyped, trivial⟩
    | .output channelTyped payloadTyped => by
        simp only [HashSetFree, HashSetFreeList]
        exact ⟨name_hashSetFree channelTyped, proc_hashSetFree payloadTyped, trivial⟩
    | .input channelTyped bodyTyped => by
        simp only [HashSetFree, HashSetFreeList]
        exact ⟨name_hashSetFree channelTyped, proc_hashSetFree bodyTyped, trivial⟩
    | .parallel processesTyped => by
        change HashSetFree (.collection .hashBag _ none)
        simp only [HashSetFree]
        exact procList_hashSetFree processesTyped

  theorem procList_hashSetFree {free : FreeSortContext} {bound : List String} {processes : List Pattern} :
      ProcListWellSorted rhoReflectivePresentation free bound processes → HashSetFreeList processes
    | .nil => trivial
    | .cons head tail => ⟨proc_hashSetFree head, procList_hashSetFree tail⟩
end

theorem perm_extract_two (elements : List Pattern) (first second : Nat) (firstBound : first < elements.length)
    (secondBound : second < (elements.eraseIdx first).length) :
    elements.Perm (elements[first] :: (elements.eraseIdx first)[second] ::
      (elements.eraseIdx first).eraseIdx second) :=
  (List.getElem_cons_eraseIdx_perm firstBound).symm.trans ((List.getElem_cons_eraseIdx_perm secondBound).symm.cons _)

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness (rho_parallel_wellSorted_inv
  locate_pair rhoStepAt_one_inv rhoStepAt_one_comm apply_commBindingsAt_resolved rhoCanonicalEquivalent_iff
  canonicalize_bag
  canonicalStep_complete_of_rhoStep closed_canonicalize)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep (RhoStepAt RhoStep rhoComm_match_shape
  rho_input_wellSorted_inv rho_output_wellSorted_inv)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.SubstitutionCanonicalCommutation
  (canonicalize_semanticCommSubst_canonicalize canonicalize_semanticCommSubst_resolveQuotes)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus (semanticCommSubst)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalMatch (rhoCanonicalEquivalent)

/-- **A depth-one step survives re-sorting.** On a well-sorted bag, every depth-one
step is matched, up to canonical form, by a depth-one step of the re-sorted bag. -/
theorem stepAt_one_resortLex {free : FreeSortContext} {source target : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] source)
    (step : RhoStepAt 1 source target) :
    ∃ target', RhoStepAt 1 (resortLex source) target' ∧ canonicalize target' = canonicalize target := by
  obtain ⟨bindings, matched, applied⟩ := rhoStepAt_one_inv step
  obtain ⟨elements, termRest, inputIndex, inputBound, outputIndex, outputBound, inputChannel, body,
    inputBinder, outputChannel, payload, rfl, inputEq, outputEq, equivalent, rfl⟩ :=
    rhoComm_match_shape matched
  obtain ⟨rfl, elementsTyped⟩ := rho_parallel_wellSorted_inv typed
  have inputMember := List.getElem_mem inputBound
  have outputMember := List.mem_of_mem_eraseIdx (List.getElem_mem outputBound)
  have inputTyped := procListWellSorted_iff_forall_mem.mp elementsTyped _ inputMember
  rw [inputEq] at inputTyped
  obtain ⟨rfl, _, bodyTyped⟩ := rho_input_wellSorted_inv inputTyped
  have outputTyped := procListWellSorted_iff_forall_mem.mp elementsTyped _ outputMember
  rw [outputEq] at outputTyped
  obtain ⟨_, payloadTyped⟩ := rho_output_wellSorted_inv outputTyped
  have originalTarget : target = .collection .hashBag (semanticCommSubst (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.resolveQuotes rhoReflectivePresentation body) payload ::
      (elements.eraseIdx inputIndex).eraseIdx outputIndex) none := by
    rw [← applied]
    exact apply_commBindingsAt_resolved bodyTyped payloadTyped elements inputIndex outputIndex inputChannel
  have extracted := perm_extract_two elements inputIndex outputIndex inputBound outputBound
  rw [inputEq, outputEq] at extracted
  have resortedPerm := (sortLex_perm (elements.map resortLex)).trans (extracted.map resortLex)
  simp only [List.map_cons, resortLex, resortLexList] at resortedPerm
  obtain ⟨i, iBound, j, jBound, inputEq', outputEq', residuePerm⟩ := locate_pair resortedPerm
  have channels : rhoCanonicalEquivalent (resortLex inputChannel) (resortLex outputChannel) = true := by
    rw [rhoCanonicalEquivalent_iff, canonicalize_resortLex, canonicalize_resortLex]
    exact (rhoCanonicalEquivalent_iff _ _).mp equivalent
  have bodyTyped' := resortLex_proc bodyTyped
  have payloadTyped' := resortLex_proc payloadTyped
  have step' := rhoStepAt_one_comm iBound jBound inputEq' outputEq' channels
  rw [apply_commBindingsAt_resolved bodyTyped' payloadTyped'] at step'
  rw [resortLex_bag]
  refine ⟨_, step', ?_⟩
  have contractum : canonicalize (semanticCommSubst (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.resolveQuotes rhoReflectivePresentation (resortLex body)) (resortLex payload)) =
      canonicalize (semanticCommSubst (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.resolveQuotes rhoReflectivePresentation body) payload) := by
    rw [canonicalize_semanticCommSubst_resolveQuotes bodyTyped'
        (resortLex_hashSetFree payload (proc_hashSetFree payloadTyped)),
      canonicalize_semanticCommSubst_resolveQuotes bodyTyped (proc_hashSetFree payloadTyped),
      ← canonicalize_semanticCommSubst_canonicalize bodyTyped'
        (resortLex_hashSetFree payload (proc_hashSetFree payloadTyped)),
      canonicalize_resortLex, canonicalize_resortLex,
      canonicalize_semanticCommSubst_canonicalize bodyTyped (proc_hashSetFree payloadTyped)]
  rw [originalTarget, canonicalize_bag, canonicalize_bag, normalizeBagElements_eq_sort_bagContents,
    normalizeBagElements_eq_sort_bagContents]
  congr 1
  apply sortPatterns_eq_of_perm
  apply bagContents_perm
  simp only [List.map_cons]
  rw [contractum]
  apply List.Perm.cons
  have tailEq : (((elements.eraseIdx inputIndex).eraseIdx outputIndex).map resortLex).map canonicalize =
      ((elements.eraseIdx inputIndex).eraseIdx outputIndex).map canonicalize := by
    rw [List.map_map, canonicalize_resortLex_map]
  rw [← tailEq]
  exact residuePerm.map canonicalize

/-! ## The lexicographic stepper -/

/-- The lexicographic form of a closed, quotation-sealed process is closed and sealed. -/
theorem closed_lexCanon {free : FreeSortContext} {process : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] process)
    (safe : binderSafeAt "NQuote" 0 process = true) :
    ProcWellSorted rhoReflectivePresentation free [] (lexCanon process) ∧
      binderSafeAt "NQuote" 0 (lexCanon process) = true := by
  obtain ⟨canonicalTyped, canonicalSafe⟩ := closed_canonicalize typed safe
  rw [lexCanon_eq]
  exact ⟨resortLex_proc canonicalTyped, resortLex_binderSafe "NQuote" 0 _ canonicalSafe⟩

/-- **The lexicographic stepper is complete.** Every step from a well-sorted process,
at any depth, is matched up to canonical form by a depth-one COMM on its lexicographic form. -/
theorem lexStep_complete {free : FreeSortContext} {source target : Pattern}
    (typed : ProcWellSorted rhoReflectivePresentation free [] source)
    (step : RhoStep source target) :
    ∃ target', RhoStepAt 1 (lexCanon source) target' ∧ canonicalize target' = canonicalize target := by
  obtain ⟨middle, depthOne, same⟩ := canonicalStep_complete_of_rhoStep typed step
  obtain ⟨target', resorted, same'⟩ :=
    stepAt_one_resortLex (CanonicalTyping.canonicalize_procWellSorted [] typed) depthOne
  rw [lexCanon_eq]
  exact ⟨target', resorted, same'.trans same⟩

/-! ## Channels of lexicographic forms are decided by equality -/

/-- On this source, canonically equivalent channels of a top-level input and output are equal,
so a literal matcher accepts every pair that the canonical comparator accepts. -/
def ChannelsDecided (source : Pattern) : Prop :=
  ∀ elements, source = .collection .hashBag elements none →
    ∀ input ∈ elements, ∀ output ∈ elements, ∀ inputChannel outputChannel body payload : Pattern,
      ∀ binder : Option String,
      input = .apply "PInput" [inputChannel, .lambda binder body] →
      output = .apply "POutput" [outputChannel, payload] →
      rhoCanonicalEquivalent inputChannel outputChannel = true → inputChannel = outputChannel

theorem resortLex_eq_bag_inv {pattern : Pattern} {elements : List Pattern}
    (same : resortLex pattern = .collection .hashBag elements none) :
    ∃ original, pattern = .collection .hashBag original none ∧ elements = sortLex (original.map resortLex) := by
  match pattern with
  | .bvar _ | .fvar _ | .apply _ _ | .lambda _ _ | .multiLambda _ _ _ | .subst _ _ => simp [resortLex] at same
  | .collection kind inner rest =>
    by_cases bare : kind = .hashBag ∧ rest = none
    · obtain ⟨rfl, rfl⟩ := bare
      rw [resortLex_bag] at same
      simp only [Pattern.collection.injEq, true_and, and_true] at same
      exact ⟨inner, rfl, same.symm⟩
    · rw [resortLex_collection_general kind inner rest bare] at same
      simp only [Pattern.collection.injEq] at same
      exact absurd ⟨same.1, same.2.2⟩ bare

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (IsCanonical IsCanonicalList isCanonicalList_mem
  canonicalize_isCanonical canonicalize_eq_of_isCanonical) in
/-- Every component of a lexicographic bag is its own lexicographic form. -/
theorem lexCanon_member {process member : Pattern} {elements : List Pattern}
    (form : lexCanon process = .collection .hashBag elements none) (membership : member ∈ elements) :
    lexCanon member = member := by
  rw [lexCanon_eq] at form
  obtain ⟨original, canonicalShape, rfl⟩ := resortLex_eq_bag_inv form
  have canonical := canonicalize_isCanonical process
  rw [canonicalShape] at canonical
  unfold IsCanonical at canonical
  obtain ⟨member0, member0In, rfl⟩ := List.mem_map.mp ((sortLex_perm _).mem_iff.mp membership)
  have member0Canonical := canonicalize_eq_of_isCanonical (isCanonicalList_mem canonical.2.2.2 member0In)
  rw [lexCanon_eq, canonicalize_resortLex, member0Canonical]

theorem lexCanon_input_channel {channel body : Pattern} {binder : Option String}
    (fixed : lexCanon (.apply "PInput" [channel, .lambda binder body]) = .apply "PInput" [channel, .lambda binder body]) :
    lexCanon channel = channel := by
  rw [lexCanon_apply_general "PInput" _ (by simp)] at fixed
  simp only [lexCanonList, lexCanon, Pattern.apply.injEq, List.cons.injEq, true_and] at fixed
  exact fixed.1

theorem lexCanon_output_channel {channel payload : Pattern}
    (fixed : lexCanon (.apply "POutput" [channel, payload]) = .apply "POutput" [channel, payload]) :
    lexCanon channel = channel := by
  rw [lexCanon_apply_general "POutput" _ (by simp)] at fixed
  simp only [lexCanonList, Pattern.apply.injEq, List.cons.injEq, true_and] at fixed
  exact fixed.1

/-- **Lexicographic forms decide their channels by equality.** -/
theorem lexCanon_channelsDecided (process : Pattern) : ChannelsDecided (lexCanon process) := by
  intro elements form input inputIn output outputIn inputChannel outputChannel body payload binder
    inputShape outputShape equivalent
  have inputFixed := lexCanon_member form inputIn
  have outputFixed := lexCanon_member form outputIn
  rw [inputShape] at inputFixed
  rw [outputShape] at outputFixed
  have left := lexCanon_input_channel inputFixed
  have right := lexCanon_output_channel outputFixed
  have canonicalSame := (rhoCanonicalEquivalent_iff inputChannel outputChannel).mp equivalent
  rw [← left, ← right]
  exact (lexCanon_eq_iff _ _).mpr canonicalSame

/-! ## The shapes of closed processes -/

/-- The constructor names of closed rho processes. -/
def rhoNames : List String := ["NQuote", "PDrop", "PInput", "POutput", "PZero"]

mutual
  /-- The patterns closed rho processes are built from: bound variables, the five rho
  constructors, anonymous binders and bare parallel bags. -/
  inductive RhoShaped : Pattern → Prop
    | bvar (index : Nat) : RhoShaped (.bvar index)
    | apply {constructor : String} {arguments : List Pattern} :
        constructor ∈ rhoNames → RhoShapedList arguments → RhoShaped (.apply constructor arguments)
    | lambda {body : Pattern} : RhoShaped body → RhoShaped (.lambda none body)
    | bag {elements : List Pattern} : RhoShapedList elements → RhoShaped (.collection .hashBag elements none)

  inductive RhoShapedList : List Pattern → Prop
    | nil : RhoShapedList []
    | cons {pattern : Pattern} {patterns : List Pattern} :
        RhoShaped pattern → RhoShapedList patterns → RhoShapedList (pattern :: patterns)
end

theorem rhoShapedList_iff : ∀ patterns : List Pattern,
    RhoShapedList patterns ↔ ∀ pattern ∈ patterns, RhoShaped pattern
  | [] => ⟨fun _ _ member => absurd member List.not_mem_nil, fun _ => .nil⟩
  | pattern :: patterns => by
    rw [List.forall_mem_cons, ← rhoShapedList_iff patterns]
    constructor
    · intro shaped
      cases shaped with
      | cons head tail => exact ⟨head, tail⟩
    · intro shaped
      exact .cons shaped.1 shaped.2

/-- A free variable is not a rho shape. -/
theorem not_rhoShaped_fvar (name : String) : ¬ RhoShaped (.fvar name) := fun shaped => by cases shaped

mutual
  theorem name_rhoShaped {bound : List String} {name : Pattern} :
      NameWellSorted rhoReflectivePresentation (fun _ => none) bound name → RhoShaped name
    | .bvar _ => .bvar _
    | .fvar lookup => by cases lookup
    | .quote processTyped _ => .apply (by decide) (.cons (proc_rhoShaped processTyped) .nil)

  /-- Closed processes are rho shaped. -/
  theorem proc_rhoShaped {bound : List String} {process : Pattern} :
      ProcWellSorted rhoReflectivePresentation (fun _ => none) bound process → RhoShaped process
    | .bvar _ => .bvar _
    | .fvar lookup => by cases lookup
    | .unit => .apply (by decide) .nil
    | .drop nameTyped => .apply (by decide) (.cons (name_rhoShaped nameTyped) .nil)
    | .output channelTyped payloadTyped =>
        .apply (by decide) (.cons (name_rhoShaped channelTyped) (.cons (proc_rhoShaped payloadTyped) .nil))
    | .input channelTyped bodyTyped =>
        .apply (by decide) (.cons (name_rhoShaped channelTyped) (.cons (.lambda (proc_rhoShaped bodyTyped)) .nil))
    | .parallel processesTyped => .bag (procList_rhoShaped processesTyped)

  theorem procList_rhoShaped {bound : List String} {processes : List Pattern} :
      ProcListWellSorted rhoReflectivePresentation (fun _ => none) bound processes → RhoShapedList processes
    | .nil => .nil
    | .cons head tail => .cons (proc_rhoShaped head) (procList_rhoShaped tail)
end

theorem bagContents_rhoShaped {patterns : List Pattern} (shaped : ∀ pattern ∈ patterns, RhoShaped pattern) :
    ∀ pattern ∈ bagContents patterns, RhoShaped pattern := by
  intro member membership
  obtain ⟨kept, -⟩ := List.mem_filter.mp membership
  obtain ⟨source, sourceMember, spliced⟩ := List.mem_flatMap.mp kept
  have sourceShaped := shaped source sourceMember
  cases sourceShaped with
  | bvar index =>
    simp only [bagSplice, List.mem_singleton] at spliced
    exact spliced ▸ .bvar index
  | apply known arguments =>
    simp only [bagSplice, List.mem_singleton] at spliced
    exact spliced ▸ .apply known arguments
  | lambda body =>
    simp only [bagSplice, List.mem_singleton] at spliced
    exact spliced ▸ .lambda body
  | bag elements =>
    simp only [bagSplice] at spliced
    exact (rhoShapedList_iff _).mp elements member spliced

theorem collapseBag_rhoShaped : ∀ {patterns : List Pattern}, (∀ pattern ∈ patterns, RhoShaped pattern) →
    RhoShaped (collapseBag patterns)
  | [], _ => .apply (by decide) .nil
  | [pattern], shaped => shaped pattern (List.mem_singleton_self pattern)
  | _ :: _ :: _, shaped => .bag ((rhoShapedList_iff _).mpr shaped)

theorem normalizeQuote_rhoShaped {pattern : Pattern} (shaped : RhoShaped pattern) :
    RhoShaped (normalizeQuote pattern) := by
  by_cases dropped : ∃ name, pattern = .apply "PDrop" [name]
  · obtain ⟨name, rfl⟩ := dropped
    cases shaped with
    | apply _ arguments =>
      cases arguments with
      | cons nameShaped _ => simpa only [normalizeQuote] using nameShaped
  · have kept : normalizeQuote pattern = .apply "NQuote" [pattern] := by
      unfold normalizeQuote
      split
      · rename_i name
        exact absurd ⟨name, rfl⟩ dropped
      · rfl
    rw [kept]
    exact .apply (by decide) (.cons shaped .nil)

mutual
  /-- Lexicographic forms of rho shapes are rho shapes. -/
  theorem lexCanon_rhoShaped : ∀ {pattern : Pattern}, RhoShaped pattern → RhoShaped (lexCanon pattern)
    | _, .bvar index => .bvar index
    | _, .apply (constructor := constructor) (arguments := arguments) known argumentsShaped => by
        have canonicalShaped := lexCanonList_rhoShaped argumentsShaped
        by_cases quote : constructor = "NQuote" ∧ ∃ argument, arguments = [argument]
        · obtain ⟨rfl, argument, rfl⟩ := quote
          simp only [lexCanonList] at canonicalShaped
          cases canonicalShaped with
          | cons argumentShaped _ =>
            simp only [lexCanon]
            exact normalizeQuote_rhoShaped argumentShaped
        · rw [lexCanon_apply_general constructor arguments quote]
          exact .apply known canonicalShaped
    | _, .lambda bodyShaped => by
        simp only [lexCanon]
        exact .lambda (lexCanon_rhoShaped bodyShaped)
    | _, .bag elementsShaped => by
        simp only [lexCanon]
        exact collapseBag_rhoShaped fun member membership =>
          bagContents_rhoShaped ((rhoShapedList_iff _).mp (lexCanonList_rhoShaped elementsShaped)) member
            ((sortLex_perm _).mem_iff.mp membership)

  theorem lexCanonList_rhoShaped : ∀ {patterns : List Pattern}, RhoShapedList patterns →
      RhoShapedList (lexCanonList patterns)
    | _, .nil => .nil
    | _, .cons head tail => .cons (lexCanon_rhoShaped head) (lexCanonList_rhoShaped tail)
end

mutual
  /-- Rho shapes have no free variables. -/
  theorem rhoShaped_freeFvarNames : ∀ {pattern : Pattern}, RhoShaped pattern → pattern.freeFvarNames = []
    | _, .bvar _ => by simp [Pattern.freeFvarNames]
    | _, .apply _ argumentsShaped => by
        simp only [Pattern.freeFvarNames]
        exact rhoShapedList_freeFvarNames argumentsShaped
    | _, .lambda bodyShaped => by
        simp only [Pattern.freeFvarNames]
        exact rhoShaped_freeFvarNames bodyShaped
    | _, .bag elementsShaped => by
        simp only [Pattern.freeFvarNames, Option.toList_none, List.append_nil]
        exact rhoShapedList_freeFvarNames elementsShaped

  theorem rhoShapedList_freeFvarNames : ∀ {patterns : List Pattern}, RhoShapedList patterns →
      patterns.flatMap Pattern.freeFvarNames = []
    | _, .nil => rfl
    | _, .cons head tail => by
        simp only [List.flatMap_cons, rhoShaped_freeFvarNames head, List.nil_append]
        exact rhoShapedList_freeFvarNames tail
end

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.LexCanonical

/-! ## Retained alpha-sensitive text keys

`RetainedKey` interprets the existing scoped `Pattern` carrier and emits the
text grammar through a retained frame cursor. Its recursive byte reference is
independent of that cursor. This text grammar is not `ser`; equality of opaque
data encodings does not identify source objects or their occurrences.

A fixed `Decoder` supplies free-name and data bytes. Native VarId-to-pattern,
scope admission, decoding, integer limits, allocation and cancellation are
instance obligations. `PInput` here is pure COMM; persistent receive is a
separate native language extension. Cursor charges count the declared provider
actions on the same initial representation. They are not physical bounds or
an invariance claim for pointer-hash probes after graph reallocation.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.LexCanonical.RetainedKey

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Machines

abbrev Bytes := List UInt8

def literal (text : String) : Bytes := text.toUTF8.toList

def numeral (index : Nat) : Bytes := literal ("$#" ++ toString index)

structure Context where
  bound : List Nat
  next : Nat
  deriving DecidableEq, Repr

/-- The key product is completed text and its alpha displacement. It carries
no occurrence identity and is not the prefix-free serialization `ser`. -/
structure Product where
  bytes : Bytes
  displacement : Nat
  next : Nat
  deriving DecidableEq, Repr

/-- Free-name and opaque-data byte decoding is supplied by the fixed native
instance. It is separate from byte emission and has its own service price. -/
structure Decoder where
  freeName : String → Bytes
  data : Pattern → Bytes

mutual
def procBytes (decode : Decoder) (bound : List Nat) (next : Nat) :
    Pattern → Option (Bytes × Nat)
  | .apply "PZero" [] => some (literal "0", next)
  | .collection .hashBag children none => do
      let result ← partsBytes decode bound next true children
      pure (literal "par(" ++ result.1 ++ literal ")", result.2)
  | .apply "POutput" [channel, body] => do
      let name ← nameBytes decode bound next channel
      let body ← procBytes decode bound next body
      pure (literal "send(" ++ name ++ literal "," ++ body.1 ++ literal ")", body.2)
  | .apply "PInput" [channel, .lambda _ body] => do
      let name ← nameBytes decode bound next channel
      let body ← procBytes decode (next :: bound) (next + 1) body
      pure (literal "recv(" ++ name ++ literal "," ++ body.1 ++ literal ")", body.2)
  | .apply "PDrop" [name] => do
      let name ← nameBytes decode bound next name
      pure (literal "drop(" ++ name ++ literal ")", next)
  | .apply "PVal" [payload] =>
      some (literal "val(" ++ decode.data payload ++ literal ")", next)
  | .apply "PEvalPayload" [payload] =>
      some (literal "defer(" ++ decode.data payload ++ literal ")", next)
  | _ => none

def nameBytes (decode : Decoder) (bound : List Nat) (next : Nat) : Pattern → Option Bytes
  | .bvar index => bound[index]?.map numeral
  | .fvar name => some (decode.freeName name)
  | .apply "NQuote" [.apply "PDrop" [name]] => nameBytes decode bound next name
  | .apply "NQuote" [body] => do
      let body ← procBytes decode [] 0 body
      pure (literal "@(" ++ body.1 ++ literal ")")
  | _ => none

def partsBytes (decode : Decoder) (bound : List Nat) (next : Nat) (first : Bool) :
    List Pattern → Option (Bytes × Nat)
  | [] => some ([], next)
  | child :: rest => do
      let child ← procBytes decode bound next child
      let rest ← partsBytes decode bound child.2 false rest
      pure ((if first then [] else literal "|") ++ child.1 ++ rest.1, rest.2)
end

mutual
def binderCount : Pattern → Nat
  | .collection .hashBag children none => binderCountAll children
  | .apply "POutput" [_, body] => binderCount body
  | .apply "PInput" [_, .lambda _ body] => 1 + binderCount body
  | _ => 0

def binderCountAll : List Pattern → Nat
  | [] => 0
  | child :: rest => binderCount child + binderCountAll rest
end

inductive Frame where
  | proc (pattern : Pattern)
  | name (pattern : Pattern)
  | parts (patterns : List Pattern) (first : Bool)
  | text (bytes : Bytes)
  | receiver (body : Pattern)
  | lookup (position : Nat) (remaining : List Nat)
  | pop (bound : List Nat)
  | restore (context : Context)
  deriving DecidableEq, Repr

structure Work where
  frames : List Frame
  context : Context
  refused : Bool := false
  deriving DecidableEq, Repr

def frameMeaning (decode : Decoder) (context : Context) : Frame → Option (Bytes × Context)
  | .proc pattern => (procBytes decode context.bound context.next pattern).map fun result =>
      (result.1, { context with next := result.2 })
  | .name pattern => (nameBytes decode context.bound context.next pattern).map fun bytes => (bytes, context)
  | .parts patterns first => (partsBytes decode context.bound context.next first patterns).map fun result =>
      (result.1, { context with next := result.2 })
  | .text bytes => some (bytes, context)
  | .receiver body => (procBytes decode (context.next :: context.bound) (context.next + 1) body).map
      fun result => (result.1, { context with next := result.2 })
  | .lookup position remaining => remaining[position]?.map fun index => (numeral index, context)
  | .pop bound => some ([], { context with bound := bound })
  | .restore previous => some ([], previous)

def framesMeaning (decode : Decoder) (context : Context) : List Frame → Option (Bytes × Context)
  | [] => some ([], context)
  | frame :: rest => do
      let first ← frameMeaning decode context frame
      let rest ← framesMeaning decode first.2 rest
      pure (first.1 ++ rest.1, rest.2)

def meaning (decode : Decoder) (work : Work) : Option (Bytes × Context) :=
  if work.refused then none else framesMeaning decode work.context work.frames

/-- One frame, environment position or literal byte is processed. Wide child
lists retain their tail in `parts`; no complete key is constructed first. -/
def step (decode : Decoder) (work : Work) : Option (Option UInt8) × Work :=
  if work.refused then (none, work) else
  match work.frames with
  | [] => (none, work)
  | .text [] :: rest => (some none, { work with frames := rest })
  | .text (byte :: bytes) :: rest =>
      (some (some byte), { work with frames := .text bytes :: rest })
  | .pop bound :: rest =>
      (some none, { work with frames := rest, context.bound := bound })
  | .restore context :: rest =>
      (some none, { work with frames := rest, context := context })
  | .receiver body :: rest =>
      (some none, { work with
        frames := .proc body :: .pop work.context.bound :: rest
        context := ⟨work.context.next :: work.context.bound, work.context.next + 1⟩ })
  | .lookup _ [] :: _ => (some none, { work with frames := [], refused := true })
  | .lookup 0 (index :: _) :: rest =>
      (some none, { work with frames := .text (numeral index) :: rest })
  | .lookup (position + 1) (_ :: remaining) :: rest =>
      (some none, { work with frames := .lookup position remaining :: rest })
  | .parts [] _ :: rest => (some none, { work with frames := rest })
  | .parts (child :: children) first :: rest =>
      (some none, { work with
        frames := .text (if first then [] else literal "|") :: .proc child ::
          .parts children false :: rest })
  | .name pattern :: rest =>
      match pattern with
      | .bvar index =>
          (some none, { work with frames := .lookup index work.context.bound :: rest })
      | .fvar name =>
          (some none, { work with frames := .text (decode.freeName name) :: rest })
      | .apply "NQuote" [.apply "PDrop" [name]] =>
          (some none, { work with frames := .name name :: rest })
      | .apply "NQuote" [body] =>
          (some none, { work with
            frames := .text (literal "@(") :: .proc body :: .text (literal ")") ::
              .restore work.context :: rest
            context := ⟨[], 0⟩ })
      | _ => (some none, { work with frames := [], refused := true })
  | .proc pattern :: rest =>
      match pattern with
      | .apply "PZero" [] =>
          (some none, { work with frames := .text (literal "0") :: rest })
      | .collection .hashBag children none =>
          (some none, { work with
            frames := .text (literal "par(") :: .parts children true :: .text (literal ")") :: rest })
      | .apply "POutput" [channel, body] =>
          (some none, { work with
            frames := .text (literal "send(") :: .name channel :: .text (literal ",") ::
              .proc body :: .text (literal ")") :: rest })
      | .apply "PInput" [channel, .lambda _ body] =>
          (some none, { work with
            frames := .text (literal "recv(") :: .name channel :: .text (literal ",") ::
              .receiver body :: .text (literal ")") :: rest })
      | .apply "PDrop" [name] =>
          (some none, { work with
            frames := .text (literal "drop(") :: .name name :: .text (literal ")") :: rest })
      | .apply "PVal" [payload] =>
          (some none, { work with
            frames := .text (literal "val(") :: .text (decode.data payload) :: .text (literal ")") :: rest })
      | .apply "PEvalPayload" [payload] =>
          (some none, { work with
            frames := .text (literal "defer(") :: .text (decode.data payload) :: .text (literal ")") :: rest })
      | _ => (some none, { work with frames := [], refused := true })

def emitted : Option (Option UInt8) → Bytes
  | some (some byte) => [byte]
  | _ => []

/-- A physical step either retains the complete residual meaning or emits
exactly its next byte. The independently recursive reference interprets the
whole residual, including future scope restoration. -/
theorem step_meaning (decode : Decoder) (work : Work) :
    meaning decode work = (meaning decode (step decode work).2).map fun result =>
      (emitted (step decode work).1 ++ result.1, result.2) := by
  rcases work with ⟨frames, context, refused⟩
  cases refused with
  | true => simp [step, meaning]
  | false =>
      cases frames with
      | nil => simp [step, meaning, framesMeaning, emitted]
      | cons frame rest =>
          cases frame with
          | text bytes =>
              cases bytes <;> simp [step, meaning, framesMeaning, frameMeaning, emitted]
          | pop bound => simp [step, meaning, framesMeaning, frameMeaning, emitted]
          | restore previous => simp [step, meaning, framesMeaning, frameMeaning, emitted]
          | receiver body =>
              cases result : procBytes decode (context.next :: context.bound) (context.next + 1) body <;>
                simp [step, meaning, framesMeaning, frameMeaning, emitted, result]
          | lookup position remaining =>
              cases remaining with
              | nil => simp [step, meaning, framesMeaning, frameMeaning]
              | cons index remaining =>
                  cases position <;> simp [step, meaning, framesMeaning, frameMeaning, emitted]
          | parts patterns first =>
              cases patterns with
              | nil => simp [step, meaning, framesMeaning, frameMeaning, partsBytes, emitted]
              | cons child children =>
                  simp [step, meaning, framesMeaning, frameMeaning, partsBytes, emitted,
                    List.append_assoc, Option.bind_map, Option.bind_assoc]
          | proc pattern =>
              simp only [step, Bool.false_eq_true, if_false]
              split <;> simp_all [meaning, framesMeaning, frameMeaning, procBytes,
                emitted, List.append_assoc, Option.bind_assoc, Option.bind_map]
          | name pattern =>
              simp only [step, Bool.false_eq_true, if_false]
              split <;> simp_all [meaning, framesMeaning, frameMeaning, nameBytes,
                emitted, List.append_assoc, Option.bind_assoc, Option.bind_map, Function.comp_def]

private theorem pair_next {bytes other : Bytes} {next final : Nat}
    (same : some (bytes, next) = some (other, final)) : final = next :=
  (Prod.mk.inj (Option.some.inj same)).2.symm

mutual
theorem proc_next (decode : Decoder) (bound : List Nat) (next : Nat)
    (pattern : Pattern) (bytes : Bytes) (final : Nat)
    (complete : procBytes decode bound next pattern = some (bytes, final)) :
    final = next + binderCount pattern := by
  unfold procBytes at complete
  split at complete
  · simpa [binderCount] using pair_next complete
  · rename_i children
    obtain ⟨result, computed, output⟩ := Option.bind_eq_some_iff.mp complete
    simpa [binderCount] using
      (pair_next output).trans (parts_next decode bound next true children result.1 result.2 computed)
  · rename_i channel body
    obtain ⟨_, _, remainder⟩ := Option.bind_eq_some_iff.mp complete
    obtain ⟨result, computed, output⟩ := Option.bind_eq_some_iff.mp remainder
    simpa [binderCount] using
      (pair_next output).trans (proc_next decode bound next body result.1 result.2 computed)
  · rename_i channel binder body
    obtain ⟨_, _, remainder⟩ := Option.bind_eq_some_iff.mp complete
    obtain ⟨result, computed, output⟩ := Option.bind_eq_some_iff.mp remainder
    have actual := (pair_next output).trans
      (proc_next decode (next :: bound) (next + 1) body result.1 result.2 computed)
    simpa [binderCount, Nat.add_assoc] using actual
  · obtain ⟨_, _, output⟩ := Option.bind_eq_some_iff.mp complete
    simpa [binderCount] using pair_next output
  · simpa [binderCount] using pair_next complete
  · simpa [binderCount] using pair_next complete
  · cases complete
termination_by sizeOf pattern
decreasing_by all_goals (subst_vars; simp_wf <;> omega)

theorem parts_next (decode : Decoder) (bound : List Nat) (next : Nat) (first : Bool)
    (patterns : List Pattern) (bytes : Bytes) (final : Nat)
    (complete : partsBytes decode bound next first patterns = some (bytes, final)) :
    final = next + binderCountAll patterns := by
  cases patterns with
  | nil => simpa [binderCountAll] using pair_next complete
  | cons child children =>
      obtain ⟨childResult, childComplete, remainder⟩ := Option.bind_eq_some_iff.mp complete
      obtain ⟨restResult, restComplete, output⟩ := Option.bind_eq_some_iff.mp remainder
      have actual := (pair_next output).trans
        (parts_next decode bound childResult.2 false children restResult.1 restResult.2 restComplete)
      rw [proc_next decode bound next child childResult.1 childResult.2 childComplete] at actual
      simpa only [binderCountAll, Nat.add_assoc] using actual
termination_by sizeOf patterns
decreasing_by all_goals (subst_vars; simp_wf <;> omega)
end

def provider (decode : Decoder) : Cursor.Provider (Cursor.Sequence.protocol (Option UInt8)) where
  State _ _ := Work
  step work _ := ⟨(step decode work).1, (step decode work).2⟩

def consume (reversed : Bytes) : Option UInt8 → Bytes
  | none => reversed
  | some byte => byte :: reversed

def client := Cursor.Fold.client consume

abbrev Saved (decode : Decoder) := Nat × Cursor.Outcome (provider decode) client ()

def start (decode : Decoder) (context : Context) (pattern : Pattern) : Saved decode :=
  (0, .paused ⟨(), .pulling [], ⟨[.proc pattern], context, false⟩⟩)

def startName (decode : Decoder) (context : Context) (pattern : Pattern) : Saved decode :=
  (0, .paused ⟨(), .pulling [], ⟨[.name pattern], context, false⟩⟩)

def resume (decode : Decoder) (allowance : Nat) (saved : Saved decode) : Saved decode :=
  Cursor.resume (provider decode) client (fun _ _ => 1) allowance saved

def completed (decode : Decoder) (initial : Nat) (saved : Saved decode) : Option (Except Unit Product) :=
  match saved.2 with
  | .paused _ => none
  | .done ⟨_, reversed, work⟩ =>
      if work.refused then some (.error ()) else
        some (.ok ⟨reversed.reverse, work.context.next - initial, work.context.next⟩)

def withPrefix (reversed : Bytes) (remaining : Option (Bytes × Context)) : Option (Bytes × Context) :=
  remaining.map fun result => (reversed.reverse ++ result.1, result.2)

def controlMeaning (decode : Decoder) (control : Cursor.Fold.State Bytes) (work : Work) :
    Option (Bytes × Context) :=
  match control with
  | .pulling reversed => withPrefix reversed (meaning decode work)
  | .finished reversed => if work.refused then none else some (reversed.reverse, work.context)

def savedMeaning (decode : Decoder) (saved : Saved decode) : Option (Bytes × Context) :=
  match saved.2 with
  | .paused ⟨_, control, work⟩ => controlMeaning decode control work
  | .done ⟨_, reversed, work⟩ => controlMeaning decode (.finished reversed) work

theorem resume_zero (decode : Decoder) (saved : Saved decode) : resume decode 0 saved = saved := by
  exact Cursor.resume_zero _ _ _ saved

theorem pause_composition (decode : Decoder) (first second : Nat) (saved : Saved decode) :
    resume decode (first + second) saved = resume decode second (resume decode first saved) := by
  exact Cursor.resume_add _ _ _ first second saved

private theorem end_meaning (decode : Decoder) (work : Work) (ended : (step decode work).1 = none) :
    meaning decode work = if work.refused then none else some ([], work.context) := by
  rcases work with ⟨frames, context, refused⟩
  cases refused with
  | true => simp [meaning]
  | false =>
      cases frames with
      | nil => rfl
      | cons frame rest =>
          cases frame <;> simp only [step, Bool.false_eq_true, if_false] at ended
          all_goals first | contradiction | (split at ended <;> simp_all)

private theorem end_unchanged (decode : Decoder) (work : Work) (ended : (step decode work).1 = none) :
    (step decode work).2 = work := by
  rcases work with ⟨frames, context, refused⟩
  cases refused with
  | true => rfl
  | false =>
      cases frames with
      | nil => rfl
      | cons frame rest =>
          cases frame <;> simp only [step, Bool.false_eq_true, if_false] at ended
          all_goals first | contradiction | (split at ended <;> simp_all)

private theorem withPrefix_consume (reversed : Bytes) (byte : Option UInt8)
    (remaining : Option (Bytes × Context)) :
    withPrefix (consume reversed byte) remaining =
      withPrefix reversed (remaining.map fun result => (byte.toList ++ result.1, result.2)) := by
  cases byte <;> simp [withPrefix, consume, List.reverse_cons, List.append_assoc, Function.comp_def]

private theorem control_step_meaning (decode : Decoder) (reversed : Bytes) (work : Work) :
    controlMeaning decode
      (match (step decode work).1 with
        | none => .finished reversed
        | some byte => .pulling (consume reversed byte)) (step decode work).2 =
      controlMeaning decode (.pulling reversed) work := by
  cases reply : (step decode work).1 with
  | none =>
      rw [end_unchanged decode work reply]
      by_cases refused : work.refused = true <;>
        simp [controlMeaning, withPrefix, end_meaning decode work reply, refused]
  | some byte =>
      simp only [controlMeaning]
      rw [withPrefix_consume, step_meaning decode work]
      cases byte <;> simp [reply, emitted]

theorem advance_meaning (decode : Decoder) (allowance : Nat)
    (control : Cursor.Fold.State Bytes) (work : Work) :
    savedMeaning decode (Cursor.advance (provider decode) client (fun _ _ => 1)
      allowance ⟨(), control, work⟩) = controlMeaning decode control work := by
  induction allowance generalizing control work with
  | zero => rfl
  | succ allowance ih =>
      cases control with
      | finished reversed => rfl
      | pulling reversed =>
          dsimp only [Cursor.advance, provider, client, Cursor.Fold.client]
          simp only [TypeCat.ofHom_apply]
          cases observed : (step decode work).1 with
          | none =>
              have localLaw : controlMeaning decode (.finished reversed) (step decode work).2 =
                  controlMeaning decode (.pulling reversed) work := by
                simpa only [observed] using control_step_meaning decode reversed work
              simpa only [savedMeaning, observed, provider, client, Cursor.Fold.client,
                Cursor.Sequence.protocol, Mettapedia.TypeTheory.IndexedPolynomial.withHoles] using
                  (ih (.finished reversed) (step decode work).2).trans localLaw
          | some byte =>
              have localLaw : controlMeaning decode (.pulling (consume reversed byte)) (step decode work).2 =
                  controlMeaning decode (.pulling reversed) work := by
                simpa only [observed] using control_step_meaning decode reversed work
              simpa only [savedMeaning, observed, provider, client, Cursor.Fold.client,
                Cursor.Sequence.protocol, Mettapedia.TypeTheory.IndexedPolynomial.withHoles] using
                  (ih (.pulling (consume reversed byte)) (step decode work).2).trans localLaw

theorem resume_meaning (decode : Decoder) (allowance : Nat) (saved : Saved decode) :
    savedMeaning decode (resume decode allowance saved) = savedMeaning decode saved := by
  rcases saved with ⟨paid, outcome⟩
  cases outcome with
  | done result => rfl
  | paused packet =>
      rcases packet with ⟨index, control, work⟩
      cases index
      simpa [resume, Cursor.resume, savedMeaning] using advance_meaning decode allowance control work

theorem start_meaning (decode : Decoder) (context : Context) (pattern : Pattern) :
    savedMeaning decode (start decode context pattern) =
      (procBytes decode context.bound context.next pattern).map fun result =>
        (result.1, { context with next := result.2 }) := by
  simp [start, savedMeaning, controlMeaning, withPrefix, meaning, framesMeaning, frameMeaning, Function.comp_def]

theorem startName_meaning (decode : Decoder) (context : Context) (pattern : Pattern) :
    savedMeaning decode (startName decode context pattern) =
      (nameBytes decode context.bound context.next pattern).map fun bytes => (bytes, context) := by
  simp [startName, savedMeaning, controlMeaning, withPrefix, meaning, framesMeaning, frameMeaning,
    Function.comp_def]

/-- Any completed product is the independently interpreted key, with exactly
the receiver displacement outside quotation. Partial cursors publish none. -/
theorem completed_proc_spec (decode : Decoder) (context : Context) (pattern : Pattern)
    (allowance : Nat) (product : Product)
    (returned : completed decode context.next (resume decode allowance (start decode context pattern)) =
      some (.ok product)) :
    procBytes decode context.bound context.next pattern = some (product.bytes, product.next) ∧
      product.next = context.next + binderCount pattern ∧ product.displacement = binderCount pattern := by
  have law := resume_meaning decode allowance (start decode context pattern)
  rw [start_meaning] at law
  generalize savedEq : resume decode allowance (start decode context pattern) = saved at returned law
  rcases saved with ⟨paid, outcome⟩
  cases outcome with
  | paused packet => simp [completed] at returned
  | done result =>
      rcases result with ⟨index, reversed, work⟩
      cases index
      by_cases refused : work.refused = true
      · simp [completed, refused] at returned
      · have productEq : (⟨reversed.reverse, work.context.next - context.next,
            work.context.next⟩ : Product) = product := by simpa [completed, refused] using returned
        subst product
        simp only [savedMeaning, controlMeaning, refused] at law
        cases reference : procBytes decode context.bound context.next pattern with
        | none => simp [reference] at law
        | some answer =>
            have equal : (reversed.reverse, work.context) =
                (answer.1, { context with next := answer.2 }) := by simpa [reference] using law
            have bytes := congrArg (fun pair : Bytes × Context => pair.1) equal
            have next := congrArg (fun pair : Bytes × Context => pair.2.next) equal
            have actual : procBytes decode context.bound context.next pattern =
                some (reversed.reverse, work.context.next) := by
              rw [reference]
              exact congrArg some (Prod.ext bytes.symm next.symm)
            have counted := proc_next decode context.bound context.next pattern _ _ actual
            exact ⟨by simpa only [reference] using actual, counted, by simp [counted]⟩

/-- Quotation may use its own receivers, but a completed name key does not
advance the enclosing counter or replace its bound environment. -/
theorem completed_name_spec (decode : Decoder) (context : Context) (pattern : Pattern)
    (allowance : Nat) (product : Product)
    (returned : completed decode context.next (resume decode allowance (startName decode context pattern)) =
      some (.ok product)) :
    nameBytes decode context.bound context.next pattern = some product.bytes ∧
      product.next = context.next ∧ product.displacement = 0 := by
  have law := resume_meaning decode allowance (startName decode context pattern)
  rw [startName_meaning] at law
  generalize savedEq : resume decode allowance (startName decode context pattern) = saved at returned law
  rcases saved with ⟨paid, outcome⟩
  cases outcome with
  | paused packet => simp [completed] at returned
  | done result =>
      rcases result with ⟨index, reversed, work⟩
      cases index
      by_cases refused : work.refused = true
      · simp [completed, refused] at returned
      · have productEq : (⟨reversed.reverse, work.context.next - context.next,
            work.context.next⟩ : Product) = product := by simpa [completed, refused] using returned
        subst product
        simp only [savedMeaning, controlMeaning, refused] at law
        cases reference : nameBytes decode context.bound context.next pattern with
        | none => simp [reference] at law
        | some bytes =>
            have equal : (reversed.reverse, work.context) = (bytes, context) := by
              simpa [reference] using law
            have sameBytes := congrArg (fun pair : Bytes × Context => pair.1) equal
            have next : work.context.next = context.next :=
              congrArg (fun pair : Bytes × Context => pair.2.next) equal
            exact ⟨by simpa [reference] using sameBytes.symm, next, by simp [next]⟩

theorem unfinished_not_published (decode : Decoder) (initial paid : Nat)
    (packet : Cursor.Packet (provider decode) client ()) :
    completed decode initial (paid, .paused packet) = none := rfl

theorem receiver_preserves_next_on_pop (decode : Decoder) (context : Context)
    (bound : List Nat) (rest : List Frame) :
    step decode ⟨.pop bound :: rest, context, false⟩ =
      (some none, ⟨rest, ⟨bound, context.next⟩, false⟩) := rfl

theorem quotation_restores_context (decode : Decoder) (inner outer : Context) (rest : List Frame) :
    step decode ⟨.restore outer :: rest, inner, false⟩ =
      (some none, ⟨rest, outer, false⟩) := rfl

theorem quotation_drop_uses_ambient (decode : Decoder) (context : Context) (name : Pattern) :
    nameBytes decode context.bound context.next (.apply "NQuote" [.apply "PDrop" [name]]) =
      nameBytes decode context.bound context.next name := rfl

theorem quotation_resets (decode : Decoder) (bound : List Nat) (next : Nat) (body : Pattern)
    (notDrop : ∀ name, body ≠ .apply "PDrop" [name]) :
    nameBytes decode bound next (.apply "NQuote" [body]) =
      (procBytes decode [] 0 body).map fun result => literal "@(" ++ result.1 ++ literal ")" := by
  unfold nameBytes
  split <;> simp_all
  cases computed : procBytes decode [] 0 body <;> simp_all

theorem parts_append (decode : Decoder) (bound : List Nat) (next : Nat) (first : Bool)
    (leading trailing : List Pattern) :
    partsBytes decode bound next first (leading ++ trailing) = (do
      let before ← partsBytes decode bound next first leading
      let after ← partsBytes decode bound before.2 (first && leading.isEmpty) trailing
      pure (before.1 ++ after.1, after.2)) := by
  induction leading generalizing next first with
  | nil => simp [partsBytes]
  | cons child children ih =>
      simp [partsBytes, ih, Option.bind_assoc, List.append_assoc]

inductive Event where
  | pending
  | byte (value : UInt8)
  | end
  | refused
  deriving DecidableEq, Repr

def nextEvent (decode : Decoder) (work : Work) : Event × Work :=
  let result := step decode work
  (match result.1 with
    | some (some byte) => .byte byte
    | some none => .pending
    | none => if result.2.refused then .refused else .end, result.2)

/-- Successful reference keys have exact next-byte, pending and end replies.
A pending step cannot consume a byte or certify exhaustion. -/
theorem event_spec (decode : Decoder) (work : Work) (bytes : Bytes) (context : Context)
    (valid : meaning decode work = some (bytes, context)) :
    match (nextEvent decode work).1 with
    | .pending => meaning decode (nextEvent decode work).2 = some (bytes, context)
    | .byte byte => ∃ rest, bytes = byte :: rest ∧
        meaning decode (nextEvent decode work).2 = some (rest, context)
    | .end => bytes = [] ∧ meaning decode (nextEvent decode work).2 = some ([], context)
    | .refused => False := by
  have residual := step_meaning decode work
  cases reply : (step decode work).1 with
  | none =>
      have unchanged := end_unchanged decode work reply
      have ended := end_meaning decode work reply
      by_cases refused : work.refused = true
      · simp [refused] at ended
        simp [ended] at valid
      · have empty : bytes = [] ∧ context = work.context := by simpa [refused, valid] using ended
        simp [nextEvent, reply, unchanged, refused, valid, empty.1]
  | some item =>
      rw [valid, reply] at residual
      cases item with
      | none => simpa [nextEvent, reply, emitted] using residual.symm
      | some byte =>
          obtain ⟨result, remaining, same⟩ := Option.map_eq_some_iff.mp residual.symm
          have equal : byte :: result.1 = bytes ∧ result.2 = context := by simpa [emitted] using same
          simp only [nextEvent, reply]
          refine ⟨result.1, equal.1.symm, ?_⟩
          exact remaining.trans (congrArg some (Prod.ext rfl equal.2))

namespace Compare

open _root_.CategoryTheory

def reference (left right : Bytes) : Ordering := List.compareLex compare left right

theorem common_prefix (common left right : Bytes) :
    reference (common ++ left) (common ++ right) = reference left right := by
  induction common with
  | nil => rfl
  | cons byte rest ih => simpa [reference, List.compareLex_cons_cons] using ih

theorem first_mismatch (common left right : Bytes) (a b : UInt8) (different : compare a b ≠ .eq) :
    reference (common ++ a :: left) (common ++ b :: right) = compare a b := by
  rw [common_prefix]
  simp only [reference, List.compareLex_cons_cons]
  cases order : compare a b <;> simp_all

theorem proper_prefix (common tail : Bytes) (byte : UInt8) :
    reference common (common ++ byte :: tail) = .lt ∧
      reference (common ++ byte :: tail) common = .gt := by
  have first := common_prefix common [] (byte :: tail)
  have second := common_prefix common (byte :: tail) []
  simpa [reference, List.compareLex] using And.intro first second

inductive Control where
  | left
  | firstRight
  | right (held : Option UInt8)
  | leftHeld (held : Option UInt8)
  | finished (answer : Except Unit Ordering)
  deriving DecidableEq, Repr

def afterLeft : Event → Control
  | .pending => .firstRight
  | .byte byte => .right (some byte)
  | .end => .right none
  | .refused => .finished (.error ())

def afterRight (held : Option UInt8) : Event → Control
  | .pending => .right held
  | .refused => .finished (.error ())
  | .end => .finished (.ok (if held.isSome then .gt else .eq))
  | .byte byte => match held with
    | none => .finished (.ok .lt)
    | some left => match compare left byte with
      | .eq => .left
      | order => .finished (.ok order)

def afterFirstRight : Event → Control
  | .pending => .left
  | .byte byte => .leftHeld (some byte)
  | .end => .leftHeld none
  | .refused => .finished (.error ())

def afterLeftHeld (held : Option UInt8) : Event → Control
  | .pending => .leftHeld held
  | .refused => .finished (.error ())
  | .end => .finished (.ok (if held.isSome then .lt else .eq))
  | .byte byte => match held with
    | none => .finished (.ok .gt)
    | some right => match compare byte right with
      | .eq => .left
      | order => .finished (.ok order)

def protocol : Mettapedia.TypeTheory.IndexedPolynomial Unit (fun _ => Unit) where
  Shape _ _ := Bool
  Position _ := Event
  next _ _ := ()

structure Sources where
  left : Work
  right : Work
  deriving DecidableEq, Repr

def provider (decode : Decoder) : Cursor.Provider protocol where
  State _ _ := Sources
  step sources right :=
    if (show Bool from right) then
      let result := nextEvent decode sources.right
      ⟨result.1, { sources with right := result.2 }⟩
    else
      let result := nextEvent decode sources.left
      ⟨result.1, { sources with left := result.2 }⟩

def client : Cursor.Client (P := protocol) (Return := fun _ _ => Except Unit Ordering) where
  V _ _ := Control
  str := fun _ _ => TypeCat.ofHom (fun control => match control with
    | .finished answer => ⟨.inl answer, fun impossible => nomatch impossible⟩
    | .left => ⟨.inr false, afterLeft⟩
    | .firstRight => ⟨.inr true, afterFirstRight⟩
    | .right held => ⟨.inr true, afterRight held⟩
    | .leftHeld held => ⟨.inr false, afterLeftHeld held⟩)

abbrev Saved (decode : Decoder) := Nat × Cursor.Outcome (provider decode) client ()

def start (decode : Decoder) (left right : Work) : Saved decode :=
  (0, .paused ⟨(), .left, ⟨left, right⟩⟩)

def resume (decode : Decoder) (allowance : Nat) (saved : Saved decode) : Saved decode :=
  Cursor.resume (provider decode) client (fun _ _ => 1) allowance saved

def completed (decode : Decoder) (saved : Saved decode) : Option (Except Unit Ordering) :=
  match saved.2 with
  | .paused _ => none
  | .done ⟨_, answer, _⟩ => some answer

def controlMeaning (decode : Decoder) (control : Control) (sources : Sources) : Option Ordering :=
  match control with
  | .finished (.ok order) => some order
  | .finished (.error _) => none
  | .left => do
      let left ← meaning decode sources.left
      let right ← meaning decode sources.right
      pure (reference left.1 right.1)
  | .firstRight => do
      let left ← meaning decode sources.left
      let right ← meaning decode sources.right
      pure (reference left.1 right.1)
  | .right none => do
      let right ← meaning decode sources.right
      pure (reference [] right.1)
  | .right (some held) => do
      let left ← meaning decode sources.left
      let right ← meaning decode sources.right
      pure (reference (held :: left.1) right.1)
  | .leftHeld none => do
      let left ← meaning decode sources.left
      pure (reference left.1 [])
  | .leftHeld (some held) => do
      let left ← meaning decode sources.left
      let right ← meaning decode sources.right
      pure (reference left.1 (held :: right.1))

def savedMeaning (decode : Decoder) (saved : Saved decode) : Option Ordering :=
  match saved.2 with
  | .paused ⟨_, control, sources⟩ => controlMeaning decode control sources
  | .done ⟨_, answer, sources⟩ => controlMeaning decode (.finished answer) sources

theorem resume_zero (decode : Decoder) (saved : Saved decode) : resume decode 0 saved = saved := by
  exact Cursor.resume_zero _ _ _ saved

theorem pause_composition (decode : Decoder) (first second : Nat) (saved : Saved decode) :
    resume decode (first + second) saved = resume decode second (resume decode first saved) := by
  exact Cursor.resume_add _ _ _ first second saved

theorem take_left_reply (decode : Decoder) (sources : Sources) :
    Cursor.advance (provider decode) client (fun _ _ => 1) (base := ()) 1
      ⟨(), .left, sources⟩ =
      (1, .paused ⟨(), afterLeft (nextEvent decode sources.left).1,
        { sources with left := (nextEvent decode sources.left).2 }⟩) := by
  dsimp only [Cursor.advance, provider, client]
  simp only [protocol, Mettapedia.TypeTheory.IndexedPolynomial.withHoles]
  rfl

theorem take_right_reply (decode : Decoder) (sources : Sources) :
    Cursor.advance (provider decode) client (fun _ _ => 1) (base := ()) 1
      ⟨(), .firstRight, sources⟩ =
      (1, .paused ⟨(), afterFirstRight (nextEvent decode sources.right).1,
        { sources with right := (nextEvent decode sources.right).2 }⟩) := by
  dsimp only [Cursor.advance, provider, client]
  simp only [protocol, Mettapedia.TypeTheory.IndexedPolynomial.withHoles]
  rfl

theorem right_reply_keeps_left (decode : Decoder) (held : Option UInt8) (sources : Sources) :
    Cursor.advance (provider decode) client (fun _ _ => 1) (base := ()) 1
      ⟨(), .right held, sources⟩ =
      (1, .paused ⟨(), afterRight held (nextEvent decode sources.right).1,
        { sources with right := (nextEvent decode sources.right).2 }⟩) := by
  dsimp only [Cursor.advance, provider, client]
  simp only [protocol, Mettapedia.TypeTheory.IndexedPolynomial.withHoles]
  rfl

theorem left_reply_keeps_right (decode : Decoder) (held : Option UInt8) (sources : Sources) :
    Cursor.advance (provider decode) client (fun _ _ => 1) (base := ()) 1
      ⟨(), .leftHeld held, sources⟩ =
      (1, .paused ⟨(), afterLeftHeld held (nextEvent decode sources.left).1,
        { sources with left := (nextEvent decode sources.left).2 }⟩) := by
  dsimp only [Cursor.advance, provider, client]
  simp only [protocol, Mettapedia.TypeTheory.IndexedPolynomial.withHoles]
  rfl

theorem pending_right_holds_left (decode : Decoder) (held : Option UInt8) (sources : Sources)
    (pending : (nextEvent decode sources.right).1 = .pending) :
    Cursor.advance (provider decode) client (fun _ _ => 1) (base := ()) 1
      ⟨(), .right held, sources⟩ =
      (1, .paused ⟨(), .right held, { sources with right := (nextEvent decode sources.right).2 }⟩) := by
  dsimp only [Cursor.advance, provider, client]
  simp only [pending, protocol,
    Mettapedia.TypeTheory.IndexedPolynomial.withHoles]
  rfl

/-- The symmetric wait retains the right byte and leaves its producer untouched. -/
theorem pending_left_holds_right (decode : Decoder) (held : Option UInt8) (sources : Sources)
    (pending : (nextEvent decode sources.left).1 = .pending) :
    Cursor.advance (provider decode) client (fun _ _ => 1) (base := ()) 1
      ⟨(), .leftHeld held, sources⟩ =
      (1, .paused ⟨(), .leftHeld held, { sources with left := (nextEvent decode sources.left).2 }⟩) := by
  dsimp only [Cursor.advance, provider, client]
  simp only [pending, protocol,
    Mettapedia.TypeTheory.IndexedPolynomial.withHoles]
  rfl

private theorem left_step_meaning (decode : Decoder) (sources : Sources) (order : Ordering)
    (valid : controlMeaning decode .left sources = some order) :
    controlMeaning decode (afterLeft (nextEvent decode sources.left).1)
      { sources with left := (nextEvent decode sources.left).2 } = some order := by
  obtain ⟨left, leftValid, remainder⟩ := Option.bind_eq_some_iff.mp valid
  obtain ⟨right, rightValid, compared⟩ := Option.bind_eq_some_iff.mp remainder
  have spec := event_spec decode sources.left left.1 left.2 leftValid
  cases observed : (nextEvent decode sources.left).1 with
  | pending =>
      simp only [observed] at spec
      simpa [afterLeft, controlMeaning, observed, spec, rightValid] using compared
  | byte byte =>
      simp only [observed] at spec
      obtain ⟨rest, split, next⟩ := spec
      simpa [afterLeft, controlMeaning, observed, next, rightValid, split] using compared
  | «end» =>
      simp only [observed] at spec
      simpa [afterLeft, controlMeaning, observed, rightValid, spec.1] using compared
  | refused => simp [observed] at spec

private theorem right_step_meaning (decode : Decoder) (held : Option UInt8) (sources : Sources)
    (order : Ordering) (valid : controlMeaning decode (.right held) sources = some order) :
    controlMeaning decode (afterRight held (nextEvent decode sources.right).1)
      { sources with right := (nextEvent decode sources.right).2 } = some order := by
  cases held with
  | none =>
      obtain ⟨right, rightValid, compared⟩ := Option.bind_eq_some_iff.mp valid
      have spec := event_spec decode sources.right right.1 right.2 rightValid
      cases observed : (nextEvent decode sources.right).1 with
      | pending =>
          simp only [observed] at spec
          simpa [afterRight, controlMeaning, observed, spec] using compared
      | byte byte =>
          simp only [observed] at spec
          obtain ⟨rest, split, _⟩ := spec
          simpa [afterRight, controlMeaning, observed, split, reference, List.compareLex] using compared
      | «end» =>
          simp only [observed] at spec
          simpa [afterRight, controlMeaning, observed, spec.1, reference, List.compareLex] using compared
      | refused => simp [observed] at spec

  | some held =>
      obtain ⟨left, leftValid, remainder⟩ := Option.bind_eq_some_iff.mp valid
      obtain ⟨right, rightValid, compared⟩ := Option.bind_eq_some_iff.mp remainder
      have spec := event_spec decode sources.right right.1 right.2 rightValid
      cases observed : (nextEvent decode sources.right).1 with
      | pending =>
          simp only [observed] at spec
          simpa [afterRight, controlMeaning, observed, leftValid, spec] using compared
      | byte byte =>
          simp only [observed] at spec
          obtain ⟨rest, split, next⟩ := spec
          have exactOrder : (compare held byte).then (reference left.1 rest) = order := by
            simpa [split, reference, List.compareLex_cons_cons] using compared
          cases byteOrder : compare held byte <;>
            simpa [afterRight, controlMeaning, observed, byteOrder, leftValid, next] using exactOrder
      | «end» =>
          simp only [observed] at spec
          simpa [afterRight, controlMeaning, observed, spec.1, reference, List.compareLex] using compared
      | refused => simp [observed] at spec

private theorem firstRight_step_meaning (decode : Decoder) (sources : Sources) (order : Ordering)
    (valid : controlMeaning decode .firstRight sources = some order) :
    controlMeaning decode (afterFirstRight (nextEvent decode sources.right).1)
      { sources with right := (nextEvent decode sources.right).2 } = some order := by
  obtain ⟨left, leftValid, remainder⟩ := Option.bind_eq_some_iff.mp valid
  obtain ⟨right, rightValid, compared⟩ := Option.bind_eq_some_iff.mp remainder
  have spec := event_spec decode sources.right right.1 right.2 rightValid
  cases observed : (nextEvent decode sources.right).1 with
  | pending =>
      simp only [observed] at spec
      simpa [afterFirstRight, controlMeaning, observed, leftValid, spec] using compared
  | byte byte =>
      simp only [observed] at spec
      obtain ⟨rest, split, next⟩ := spec
      simpa [afterFirstRight, controlMeaning, observed, leftValid, next, split] using compared
  | «end» =>
      simp only [observed] at spec
      simpa [afterFirstRight, controlMeaning, observed, leftValid, spec.1] using compared
  | refused => simp [observed] at spec

private theorem leftHeld_step_meaning (decode : Decoder) (held : Option UInt8) (sources : Sources)
    (order : Ordering) (valid : controlMeaning decode (.leftHeld held) sources = some order) :
    controlMeaning decode (afterLeftHeld held (nextEvent decode sources.left).1)
      { sources with left := (nextEvent decode sources.left).2 } = some order := by
  cases held with
  | none =>
      obtain ⟨left, leftValid, compared⟩ := Option.bind_eq_some_iff.mp valid
      have spec := event_spec decode sources.left left.1 left.2 leftValid
      cases observed : (nextEvent decode sources.left).1 with
      | pending =>
          simp only [observed] at spec
          simpa [afterLeftHeld, controlMeaning, observed, spec] using compared
      | byte byte =>
          simp only [observed] at spec
          obtain ⟨rest, split, _⟩ := spec
          simpa [afterLeftHeld, controlMeaning, observed, split, reference, List.compareLex] using compared
      | «end» =>
          simp only [observed] at spec
          simpa [afterLeftHeld, controlMeaning, observed, spec.1, reference, List.compareLex] using compared
      | refused => simp [observed] at spec

  | some held =>
      obtain ⟨left, leftValid, remainder⟩ := Option.bind_eq_some_iff.mp valid
      obtain ⟨right, rightValid, compared⟩ := Option.bind_eq_some_iff.mp remainder
      have spec := event_spec decode sources.left left.1 left.2 leftValid
      cases observed : (nextEvent decode sources.left).1 with
      | pending =>
          simp only [observed] at spec
          simpa [afterLeftHeld, controlMeaning, observed, spec, rightValid] using compared
      | byte byte =>
          simp only [observed] at spec
          obtain ⟨rest, split, next⟩ := spec
          have exactOrder : (compare byte held).then (reference rest right.1) = order := by
            simpa [split, reference, List.compareLex_cons_cons] using compared
          cases byteOrder : compare byte held <;>
            simpa [afterLeftHeld, controlMeaning, observed, byteOrder, next, rightValid] using exactOrder
      | «end» =>
          simp only [observed] at spec
          simpa [afterLeftHeld, controlMeaning, observed, spec.1, reference, List.compareLex] using compared
      | refused => simp [observed] at spec

/-- The held byte here is an actual reply of the left source; its residual
meaning includes precisely that byte followed by the source's unread suffix. -/
theorem left_byte_cut (decode : Decoder) (sources : Sources) (byte : UInt8)
    (leftBytes rightBytes : Bytes) (leftContext rightContext : Context)
    (leftValid : meaning decode sources.left = some (leftBytes, leftContext))
    (rightValid : meaning decode sources.right = some (rightBytes, rightContext))
    (observed : (nextEvent decode sources.left).1 = .byte byte) :
    controlMeaning decode (.right (some byte))
      { sources with left := (nextEvent decode sources.left).2 } =
      some (reference leftBytes rightBytes) := by
  have valid : controlMeaning decode .left sources = some (reference leftBytes rightBytes) := by
    simp [controlMeaning, leftValid, rightValid]
  simpa only [observed, afterLeft] using left_step_meaning decode sources _ valid

/-- The symmetric cut comes from an actual right-source reply, not a forged
byte paired with an arbitrary provider state. -/
theorem right_byte_cut (decode : Decoder) (sources : Sources) (byte : UInt8)
    (leftBytes rightBytes : Bytes) (leftContext rightContext : Context)
    (leftValid : meaning decode sources.left = some (leftBytes, leftContext))
    (rightValid : meaning decode sources.right = some (rightBytes, rightContext))
    (observed : (nextEvent decode sources.right).1 = .byte byte) :
    controlMeaning decode (.leftHeld (some byte))
      { sources with right := (nextEvent decode sources.right).2 } =
      some (reference leftBytes rightBytes) := by
  have valid : controlMeaning decode .firstRight sources = some (reference leftBytes rightBytes) := by
    simp [controlMeaning, leftValid, rightValid]
  simpa only [observed, afterFirstRight] using firstRight_step_meaning decode sources _ valid

theorem advance_preserves_comparison (decode : Decoder) (allowance : Nat) (control : Control)
    (sources : Sources) (order : Ordering) (valid : controlMeaning decode control sources = some order) :
    savedMeaning decode (Cursor.advance (provider decode) client (fun _ _ => 1)
      allowance ⟨(), control, sources⟩) = some order := by
  induction allowance generalizing control sources with
  | zero => exact valid
  | succ allowance ih =>
      cases control with
      | finished answer => exact valid
      | left =>
          have next := ih (afterLeft (nextEvent decode sources.left).1)
            { sources with left := (nextEvent decode sources.left).2 }
            (left_step_meaning decode sources order valid)
          dsimp only [Cursor.advance, provider, client]
          simp only [TypeCat.ofHom_apply]
          simpa [savedMeaning, protocol, Mettapedia.TypeTheory.IndexedPolynomial.withHoles,
            provider, client] using next
      | right held =>
          have next := ih (afterRight held (nextEvent decode sources.right).1)
            { sources with right := (nextEvent decode sources.right).2 }
            (right_step_meaning decode held sources order valid)
          dsimp only [Cursor.advance, provider, client]
          simp only [TypeCat.ofHom_apply]
          simpa [savedMeaning, protocol, Mettapedia.TypeTheory.IndexedPolynomial.withHoles,
            provider, client] using next
      | firstRight =>
          have next := ih (afterFirstRight (nextEvent decode sources.right).1)
            { sources with right := (nextEvent decode sources.right).2 }
            (firstRight_step_meaning decode sources order valid)
          dsimp only [Cursor.advance, provider, client]
          simp only [TypeCat.ofHom_apply]
          simpa [savedMeaning, protocol, Mettapedia.TypeTheory.IndexedPolynomial.withHoles,
            provider, client] using next
      | leftHeld held =>
          have next := ih (afterLeftHeld held (nextEvent decode sources.left).1)
            { sources with left := (nextEvent decode sources.left).2 }
            (leftHeld_step_meaning decode held sources order valid)
          dsimp only [Cursor.advance, provider, client]
          simp only [TypeCat.ofHom_apply]
          simpa [savedMeaning, protocol, Mettapedia.TypeTheory.IndexedPolynomial.withHoles,
            provider, client] using next

theorem resume_preserves_comparison (decode : Decoder) (allowance : Nat) (saved : Saved decode)
    (order : Ordering) (valid : savedMeaning decode saved = some order) :
    savedMeaning decode (resume decode allowance saved) = some order := by
  rcases saved with ⟨paid, outcome⟩
  cases outcome with
  | done result => exact valid
  | paused packet =>
      rcases packet with ⟨index, control, sources⟩
      cases index
      simpa [resume, Cursor.resume, savedMeaning] using
        advance_preserves_comparison decode allowance control sources order valid

/-- A completed comparison of two successfully represented keys agrees with
the independent flattened byte comparison, for every suspension schedule. -/
theorem completed_exact (decode : Decoder) (left right : Work) (leftBytes rightBytes : Bytes)
    (leftContext rightContext : Context)
    (leftValid : meaning decode left = some (leftBytes, leftContext))
    (rightValid : meaning decode right = some (rightBytes, rightContext))
    (allowance : Nat) (order : Ordering)
    (done : completed decode (resume decode allowance (start decode left right)) = some (.ok order)) :
    order = reference leftBytes rightBytes := by
  have valid : savedMeaning decode (start decode left right) = some (reference leftBytes rightBytes) := by
    simp [start, savedMeaning, controlMeaning, leftValid, rightValid]
  have law := resume_preserves_comparison decode allowance _ _ valid
  generalize savedEq : resume decode allowance (start decode left right) = saved at done law
  rcases saved with ⟨paid, outcome⟩
  cases outcome with
  | paused packet => simp [completed] at done
  | done result =>
      rcases result with ⟨index, answer, sources⟩
      cases index
      have answerEq : answer = .ok order := by simpa [completed] using done
      simpa [savedMeaning, answerEq, controlMeaning] using law

end Compare

namespace Controls

private def decode : Decoder :=
  ⟨fun name => literal ("$" ++ name ++ ":7"), fun _ => literal "D"⟩

private def emptyContext : Context := ⟨[], 0⟩
private def zero : Pattern := .apply "PZero" []
private def drop (name : Pattern) : Pattern := .apply "PDrop" [name]
private def quote (body : Pattern) : Pattern := .apply "NQuote" [body]
private def receive (body : Pattern) : Pattern :=
  .apply "PInput" [.fvar "ch", .lambda "x" body]
private def parallel (children : List Pattern) : Pattern := .collection .hashBag children none

/-- Sibling receives pop scope, but do not reuse the previous alpha index. -/
theorem siblings_keep_monotone_counter :
    completed decode 0 (resume decode 256 (start decode emptyContext
      (parallel [receive (drop (.bvar 0)), receive (drop (.bvar 0))]))) =
      some (.ok ⟨literal "par(recv($ch:7,drop($#0))|recv($ch:7,drop($#1)))", 2, 2⟩) := by
  decide +kernel

/-- De Bruijn position one denotes the outer receiver, not the newest one. -/
theorem nested_lookup_keeps_outer_binding :
    completed decode 7 (resume decode 256 (start decode ⟨[], 7⟩
      (receive (receive (drop (.bvar 1)))))) =
      some (.ok ⟨literal "recv($ch:7,recv($ch:7,drop($#7)))", 2, 9⟩) := by
  decide +kernel

theorem bound_positions_are_distinguished :
    (procBytes decode [] 7 (receive (receive (drop (.bvar 0))))).map Prod.fst ≠
      (procBytes decode [] 7 (receive (receive (drop (.bvar 1))))).map Prod.fst := by
  decide +kernel

/-- A quoted receiver starts at zero; the following outer receiver starts at nine. -/
theorem quotation_reset_and_outer_displacement :
    completed decode 9 (resume decode 256 (start decode ⟨[], 9⟩
      (.apply "POutput" [quote (receive (drop (.bvar 0))), receive (drop (.bvar 0))]))) =
      some (.ok ⟨literal "send(@(recv($ch:7,drop($#0))),recv($ch:7,drop($#9)))", 1, 10⟩) := by
  decide +kernel

theorem quote_drop_uses_original_environment :
    completed decode 99 (resume decode 64
      (startName decode ⟨[41], 99⟩ (quote (drop (.bvar 0))))) =
      some (.ok ⟨literal "$#41", 0, 99⟩) := by
  decide +kernel

theorem quoted_body_cannot_capture_outer_binding :
    completed decode 99 (resume decode 128
      (startName decode ⟨[41], 99⟩ (quote (receive (drop (.bvar 1)))))) =
      some (.error ()) := by
  decide +kernel

/-- A reset product cannot be reused as shifted contextual bytes. -/
theorem source_only_contextual_cache_is_unsound :
    procBytes decode [] 0 (receive (drop (.bvar 0))) ≠
      procBytes decode [] 9 (receive (drop (.bvar 0))) ∧
    binderCount (receive (drop (.bvar 0))) = 1 := by
  decide +kernel

theorem decimal_boundaries_change_contextual_bytes :
    procBytes decode [] 99 (receive (drop (.bvar 0))) =
      some (literal "recv($ch:7,drop($#99))", 100) ∧
    procBytes decode [] 999 (receive (drop (.bvar 0))) =
      some (literal "recv($ch:7,drop($#999))", 1000) := by
  decide +kernel

/-- Emitting the only byte is insufficient: end and client return remain pending. -/
theorem last_byte_is_not_publication :
    completed decode 0 (resume decode 2 (start decode emptyContext zero)) = none ∧
    completed decode 0 (resume decode 8 (start decode emptyContext zero)) =
      some (.ok ⟨literal "0", 0, 0⟩) := by
  decide +kernel

theorem actual_prefix_survives_split :
    resume decode 256 (start decode emptyContext (receive (drop (.bvar 0)))) =
      resume decode 237 (resume decode 19
        (start decode emptyContext (receive (drop (.bvar 0))))) := by
  exact pause_composition decode 19 237 _

private def textWork (delays : Nat) (bytes : Bytes) : Work :=
  ⟨List.replicate delays (.text []) ++ [.text bytes], emptyContext, false⟩

/-- This is the real whole-process cursor after its constructor expansion. -/
private def readyPar : Work :=
  (nextEvent decode ⟨[.proc (parallel [])], emptyContext, false⟩).2

private def leftCut : Compare.Saved decode :=
  Cursor.advance (Compare.provider decode) Compare.client (fun _ _ => 1) 1
    ⟨(), .left, ⟨readyPar, readyPar⟩⟩

private def rightCut : Compare.Saved decode :=
  Cursor.advance (Compare.provider decode) Compare.client (fun _ _ => 1) 1
    ⟨(), .firstRight, ⟨readyPar, readyPar⟩⟩

theorem whole_key_cut_is_genuine :
    (nextEvent decode readyPar).1 = .byte 112 ∧
      meaning decode readyPar = some (literal "par()", emptyContext) := by
  decide +kernel

/-- Both cut states interpret the original pair, including the stored first byte. -/
theorem both_ready_cuts_have_legal_residuals :
    Compare.savedMeaning decode leftCut = some .eq ∧
      Compare.savedMeaning decode rightCut = some .eq := by
  decide +kernel

/-- Matching the peer's first byte does not repoll the ready left source. -/
theorem left_ready_byte_consumed_once :
    Compare.resume decode 1 leftCut =
      (2, .paused ⟨(), .left,
        ⟨(nextEvent decode readyPar).2, (nextEvent decode readyPar).2⟩⟩) ∧
    Compare.completed decode (Compare.resume decode 64 leftCut) = some (.ok .eq) := by
  constructor
  · have event := whole_key_cut_is_genuine.1
    simp only [leftCut, Compare.take_left_reply, event, Compare.afterLeft,
      Compare.resume, Cursor.resume]
    rw [Compare.right_reply_keeps_left]
    simp [event, Compare.afterRight]
  · decide +kernel

/-- The symmetric boundary cut rejects repolling a ready right source. -/
theorem right_ready_byte_consumed_once :
    Compare.resume decode 1 rightCut =
      (2, .paused ⟨(), .left,
        ⟨(nextEvent decode readyPar).2, (nextEvent decode readyPar).2⟩⟩) ∧
    Compare.completed decode (Compare.resume decode 64 rightCut) = some (.ok .eq) := by
  constructor
  · have event := whole_key_cut_is_genuine.1
    simp only [rightCut, Compare.take_right_reply, event, Compare.afterFirstRight,
      Compare.resume, Cursor.resume]
    rw [Compare.left_reply_keeps_right]
    simp [event, Compare.afterLeftHeld]
  · decide +kernel

private def compareText (left right : Work) : Option (Except Unit Ordering) :=
  Compare.completed decode (Compare.resume decode 64 (Compare.start decode left right))

theorem delayed_right_byte_is_neither_end_nor_lost :
    compareText (textWork 0 (literal "b")) (textWork 3 (literal "a")) = some (.ok .gt) ∧
      compareText (textWork 0 (literal "b")) (textWork 3 (literal "c")) = some (.ok .lt) := by
  decide +kernel

theorem delayed_left_byte_is_neither_end_nor_lost :
    compareText (textWork 3 (literal "b")) (textWork 0 (literal "a")) = some (.ok .gt) ∧
      compareText (textWork 3 (literal "b")) (textWork 0 (literal "c")) = some (.ok .lt) := by
  decide +kernel

theorem pending_after_other_end_is_not_equality :
    compareText (textWork 0 []) (textWork 3 (literal "a")) = some (.ok .lt) ∧
      compareText (textWork 3 (literal "a")) (textWork 0 []) = some (.ok .gt) := by
  decide +kernel

theorem equal_byte_prefix_is_not_equality :
    compareText (textWork 0 (literal "a")) (textWork 3 (literal "az")) = some (.ok .lt) := by
  decide +kernel

theorem refusal_is_not_end :
    compareText (textWork 0 []) ⟨[], emptyContext, true⟩ = some (.error ()) := by
  decide +kernel

/-- An opaque-data decoder need not be injective, and a key does not certify
source identity or authorize removal of duplicate occurrences. -/
theorem equal_data_key_does_not_identify_payload :
    (.fvar "left" : Pattern) ≠ .fvar "right" ∧
    procBytes decode [] 0 (.apply "PVal" [.fvar "left"]) =
      procBytes decode [] 0 (.apply "PVal" [.fvar "right"]) := by
  decide +kernel

end Controls

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.LexCanonical.RetainedKey
