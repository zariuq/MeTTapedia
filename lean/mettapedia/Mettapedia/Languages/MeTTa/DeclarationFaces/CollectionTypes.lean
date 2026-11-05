import Mettapedia.Languages.MeTTa.DeclarationFaces.Faces
import Mettapedia.Algebra.Collections.Free
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Finsupp.Pointwise

/-!
# Collection types: the declared sort fixes the kind laws, at every depth

A collection literal is braces around elements. What it denotes is fixed by the sort it is
declared at, position by position:

* `(Bag A)` denotes finite multisets of the denotation of `A`: a K-relation with counts in ℕ;
* `(Set A)` denotes finite sets: a K-relation with presence;
* `(List A)` keeps order and multiplicity;
* `(Pair A B)` is a constructor with two declared fields, the shape of a wrapped field.

`den A l` reads a literal at a sort; a literal whose brace kind is not the sort's kind is refused
(`den_kind_mismatch`), and nothing is flattened: a bag inside a bag stays a bag. Kind laws follow
the declared sort inside nested collections and inside wrapped fields, as the declared-type source
laws of the formal-methods lane require.

* **Kind laws** (`bag_perm`, `set_perm`, `set_dedup`, `list_order`): set literals equal up to order
  and repetition, bag literals up to order only, lists up to nothing.
* **The support map** (`support`, `den_set_eq_support`): reading a bag literal as a set is taking
  its support. On annotations it is the semiring homomorphism ℕ → presence (`count_ne_zero_add`,
  `count_ne_zero_mul`); on K-relations with values in ℕ it sends sums to unions and pointwise
  products to intersections (`support_add`, `support_mul`).
* **Folds** (`count_not_set_function`, `fold_set_iff`): a fold consumes a set exactly when its
  generator's values are idempotent (`Mettapedia.Algebra.Collections.foldList_factors_set_iff`);
  counting is a fold on bags and not a function on sets.

Positive controls: `{|a b|} = {|b a a|}` as sets; `{a b} = {b a}` as bags; a bag of sets compares
its inner sets as sets. Negative controls: `{a a} ≠ {a}` as bags; `[a b] ≠ [b a]` as lists;
counting distinguishes two literals with one set.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.DeclarationFaces.Collections

/-- The kind of a collection. -/
inductive Kind where
  | bag
  | set
  | list
  deriving DecidableEq, Repr

/-- Sorts with collections over one base carrier. -/
inductive CSort where
  | base
  | coll (kind : Kind) (elem : CSort)
  | pair (first second : CSort)
  deriving DecidableEq, Repr

variable (B : Type) [DecidableEq B]

/-- **The set a sort denotes.** -/
def Den : CSort → Type
  | .base => B
  | .coll .bag A => Multiset (Den A)
  | .coll .set A => Finset (Den A)
  | .coll .list A => List (Den A)
  | .pair A A' => Den A × Den A'

/-- Denotations have decidable equality. -/
def Den.decEq : (A : CSort) → DecidableEq (Den B A)
  | .base => inferInstanceAs (DecidableEq B)
  | .coll .bag A => @Multiset.decidableEq _ (Den.decEq A)
  | .coll .set A => @Finset.decidableEq _ (Den.decEq A)
  | .coll .list A => @instDecidableEqList _ (Den.decEq A)
  | .pair A A' => @instDecidableEqProd _ _ (Den.decEq A) (Den.decEq A')

instance (A : CSort) : DecidableEq (Den B A) := Den.decEq B A

/-- A literal: a base value, braces of a kind around literals, or a pair. -/
inductive CLit where
  | atom (value : B)
  | coll (kind : Kind) (elems : List CLit)
  | pair (first second : CLit)

variable {B}

/-- **Read a literal at a sort.** A literal of the wrong shape or kind has no reading. -/
def den : (A : CSort) → CLit B → Option (Den B A)
  | .base, l => match l with
    | .atom b => some b
    | _ => none
  | .coll .bag A, l => match l with
    | .coll .bag es => (mapOpt (den A) es).map fun ds =>
        show Den B (.coll .bag A) from Multiset.ofList ds
    | _ => none
  | .coll .set A, l => match l with
    | .coll .set es => (mapOpt (den A) es).map List.toFinset
    | _ => none
  | .coll .list A, l => match l with
    | .coll .list es => mapOpt (den A) es
    | _ => none
  | .pair A A', l => match l with
    | .pair l₁ l₂ => (den A l₁).bind fun d => (den A' l₂).map fun d' => (d, d')
    | _ => none

theorem den_bag (A : CSort) (es : List (CLit B)) :
    den (.coll .bag A) (.coll .bag es) =
      (mapOpt (den A) es).map fun ds => show Den B (.coll .bag A) from Multiset.ofList ds := rfl

theorem den_set (A : CSort) (es : List (CLit B)) :
    den (.coll .set A) (.coll .set es) = (mapOpt (den A) es).map List.toFinset := rfl

/-! ## Kind laws -/

theorem mapOpt_perm {α β : Type*} {f : α → Option β} :
    ∀ {as as' : List α}, as.Perm as' → ∀ {bs : List β}, mapOpt f as = some bs →
      ∃ bs', mapOpt f as' = some bs' ∧ bs.Perm bs' := by
  intro as as' perm
  induction perm with
  | nil => intro bs h; exact ⟨bs, h, .refl _⟩
  | cons a _ ih =>
      intro bs h
      simp only [mapOpt, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rest, hrest, rfl⟩ := h
      obtain ⟨rest', hrest', perm'⟩ := ih hrest
      exact ⟨b :: rest', by simp [mapOpt, hb, hrest'], perm'.cons b⟩
  | swap a a' l =>
      intro bs h
      simp only [mapOpt, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b', hb', rest, hrest, rfl⟩ := h
      try simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hrest
      obtain ⟨b, hb, rest', hrest', rfl⟩ := hrest
      exact ⟨b :: b' :: rest', by simp [mapOpt, hb, hb', hrest'], .swap _ _ _⟩
  | trans _ _ ih₁ ih₂ =>
      intro bs h
      obtain ⟨bs₁, h₁, p₁⟩ := ih₁ h
      obtain ⟨bs₂, h₂, p₂⟩ := ih₂ h₁
      exact ⟨bs₂, h₂, p₁.trans p₂⟩

/-- **Bag literals are equal up to order.** -/
theorem bag_perm (A : CSort) {es es' : List (CLit B)} (perm : es.Perm es') :
    den (.coll .bag A) (.coll .bag es) = den (.coll .bag A) (.coll .bag es') := by
  rw [den_bag, den_bag]
  cases h : mapOpt (den A) es with
  | none =>
      cases h' : mapOpt (den A) es' with
      | none => rfl
      | some bs' =>
          obtain ⟨bs, hb, _⟩ := mapOpt_perm perm.symm h'
          rw [h] at hb; cases hb
  | some bs =>
      obtain ⟨bs', hb', p⟩ := mapOpt_perm perm h
      rw [hb']
      exact congrArg some (Multiset.coe_eq_coe.mpr p)

/-- **Set literals are equal up to order.** -/
theorem set_perm (A : CSort) {es es' : List (CLit B)} (perm : es.Perm es') :
    den (.coll .set A) (.coll .set es) = den (.coll .set A) (.coll .set es') := by
  rw [den_set, den_set]
  cases h : mapOpt (den A) es with
  | none =>
      cases h' : mapOpt (den A) es' with
      | none => rfl
      | some bs' =>
          obtain ⟨bs, hb, _⟩ := mapOpt_perm perm.symm h'
          rw [h] at hb; cases hb
  | some bs =>
      obtain ⟨bs', hb', p⟩ := mapOpt_perm perm h
      rw [hb']
      simp only [Option.map_some]
      exact congrArg some (List.toFinset_eq_of_perm _ _ p)

/-- **Set literals are equal up to repetition.** -/
theorem set_dedup (A : CSort) (e : CLit B) (es : List (CLit B)) :
    den (.coll .set A) (.coll .set (e :: e :: es)) = den (.coll .set A) (.coll .set (e :: es)) := by
  rw [den_set, den_set]
  simp only [mapOpt]
  cases den A e with
  | none => rfl
  | some d =>
      cases mapOpt (den A) es with
      | none => rfl
      | some ds => exact congrArg some (by simp)

/-! ## The support map -/

/-- **The support of a bag**: the set of its elements. -/
def support (A : CSort) (bag : Den B (.coll .bag A)) : Den B (.coll .set A) :=
  Multiset.toFinset bag

/-- **Reading a literal as a set is taking the support of its reading as a bag.** -/
theorem den_set_eq_support (A : CSort) (es : List (CLit B)) :
    den (.coll .set A) (.coll .set es) = (den (.coll .bag A) (.coll .bag es)).map (support A) := by
  rw [den_set, den_bag]
  cases mapOpt (den A) es with
  | none => rfl
  | some ds => exact congrArg some (List.toFinset_coe ds).symm

/-- On annotations, the support is the semiring homomorphism from counts to presence: a sum is
present exactly when one summand is. -/
theorem count_ne_zero_add (m n : ℕ) : (m + n ≠ 0) ↔ (m ≠ 0 ∨ n ≠ 0) := by omega

/-- A product is present exactly when both factors are. -/
theorem count_ne_zero_mul (m n : ℕ) : (m * n ≠ 0) ↔ (m ≠ 0 ∧ n ≠ 0) := by
  simp [not_or]

/-- On K-relations with counts, the support sends sums to unions. -/
theorem support_add {α : Type*} [DecidableEq α] (f g : α →₀ ℕ) :
    (f + g).support = f.support ∪ g.support := by
  ext x
  simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finset.mem_union]
  omega

/-- On K-relations with counts, the support sends pointwise products to intersections. -/
theorem support_mul {α : Type*} [DecidableEq α] (f g : α →₀ ℕ) :
    (f * g).support = f.support ∩ g.support := by
  ext x
  simp only [Finsupp.mem_support_iff, Finsupp.mul_apply, Finset.mem_inter]
  exact count_ne_zero_mul _ _

/-- The support of a bag is the support of its count function. -/
theorem support_toFinsupp {α : Type*} [DecidableEq α] (m : Multiset α) :
    (Multiset.toFinsupp m).support = m.toFinset := by
  ext x
  simp [Multiset.toFinsupp_support]

/-- The support of the sum of two bags is the union of their supports. -/
theorem support_bag_add (A : CSort) (m m' : Multiset (Den B A)) :
    support A (m + m') = (support A m ∪ support A m' : Finset (Den B A)) :=
  Multiset.toFinset_add _ _

/-! ## Folds -/

open Mettapedia.Algebra.Collections in
/-- **A fold consumes sets exactly when its generator's values are idempotent.** -/
theorem fold_set_iff {α M : Type*} [CommMonoid M] [DecidableEq α] (generator : α → M) :
    (∃ consume : Finset α → M, ∀ values : List α, foldList generator values = consume values.toFinset) ↔
      ∀ value, IsIdempotentElem (generator value) :=
  foldList_factors_set_iff generator

open Mettapedia.Algebra.Collections in
/-- **Counting is not a function on sets**: the fold that counts elements, a fold on bags, does not
factor through the set of elements. -/
theorem count_not_set_function {α : Type*} [DecidableEq α] [Nonempty α] :
    ¬ ∃ consume : Finset α → Multiplicative ℕ, ∀ values : List α,
      foldList (fun _ => Multiplicative.ofAdd (1 : ℕ)) values = consume values.toFinset := by
  rw [fold_set_iff]
  intro idempotent
  have := idempotent (Classical.arbitrary α)
  simp only [IsIdempotentElem] at this
  have h := congrArg Multiplicative.toAdd this
  simp at h

open Mettapedia.Algebra.Collections in
/-- **Counting is a function on bags.** -/
theorem count_bag_function {α : Type*} :
    ∃ consume : Multiset α → Multiplicative ℕ, ∀ values : List α,
      foldList (fun _ => Multiplicative.ofAdd (1 : ℕ)) values = consume values :=
  (foldList_factors_bag_iff _).mpr fun _ _ => Commute.all _ _

/-! ## Controls -/

/-- Two atoms. -/
abbrev a : CLit ℕ := .atom 0
abbrev b : CLit ℕ := .atom 1

/-- **Positive**: `{|a b|} = {|b a a|}` as sets. -/
example : den (.coll .set .base) (.coll .set [a, b]) = den (.coll .set .base) (.coll .set [b, a, a]) := by
  decide

/-- **Positive**: `{a b} = {b a}` as bags. -/
example : den (.coll .bag .base) (.coll .bag [a, b]) = den (.coll .bag .base) (.coll .bag [b, a]) := by
  decide

/-- **Negative**: `{a a} ≠ {a}` as bags: counts matter. -/
example : den (.coll .bag .base) (.coll .bag [a, a]) ≠ den (.coll .bag .base) (.coll .bag [a]) := by
  decide

/-- **Negative**: `[a b] ≠ [b a]` as lists: order matters. -/
example : den (.coll .list .base) (.coll .list [a, b]) ≠ den (.coll .list .base) (.coll .list [b, a]) := by
  decide

/-- **Nested**: a bag of sets compares its inner sets as sets, and still counts them. -/
example :
    den (.coll .bag (.coll .set .base)) (.coll .bag [.coll .set [a, b], .coll .set [b, a, a]]) =
      den (.coll .bag (.coll .set .base)) (.coll .bag [.coll .set [a, b], .coll .set [a, b]]) ∧
    den (.coll .bag (.coll .set .base)) (.coll .bag [.coll .set [a, b], .coll .set [a, b]]) ≠
      den (.coll .bag (.coll .set .base)) (.coll .bag [.coll .set [a, b]]) := by
  decide

/-- **Wrapped fields**: a pair whose fields are declared a set and a bag applies each field's laws. -/
example :
    den (.pair (.coll .set .base) (.coll .bag .base)) (.pair (.coll .set [a, a, b]) (.coll .bag [b, a])) =
      den (.pair (.coll .set .base) (.coll .bag .base)) (.pair (.coll .set [b, a]) (.coll .bag [a, b])) ∧
    den (.pair (.coll .set .base) (.coll .bag .base)) (.pair (.coll .set [a]) (.coll .bag [a, a])) ≠
      den (.pair (.coll .set .base) (.coll .bag .base)) (.pair (.coll .set [a]) (.coll .bag [a])) := by
  decide

/-- **Wrong kind is refused**: a bag literal has no reading at a set sort; nothing is flattened. -/
theorem den_kind_mismatch : den (.coll .set .base) (.coll .bag [a]) = none ∧
    den (.coll .bag .base) (.coll .bag [.coll .bag [a]]) = none := by
  decide

end Mettapedia.Languages.MeTTa.DeclarationFaces.Collections
