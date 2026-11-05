import Mettapedia.Algebra.Collections.Sequences
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Dedup
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Multiset.Sort
import Mathlib.Order.Hom.BoundedLattice

/-!
# Tuples, lists, bags and sets: the free collection theories and their maps

* **Tuples** of arity `n` are the `n`-fold power `Fin n → α`. Their universal
  property is the product's: a map into tuples is a tuple of maps
  (`tupleMaps`). No equation identifies two tuples, and a tuple type is not
  the free algebra of an equational theory on `α`; it is the arity that
  carries the structure.
* **Lists** are the disjoint union of the tuple types over all arities
  (`Sequences.Tuple.sigmaEquiv`) and the free monoid on `α`: a
  monoid homomorphism out of the lists is any function on singletons, freely
  (`FreeAddMonoid.lift`). Read as `List`, they are the inductive presentation
  by `nil` and `cons`.
* **Bags** are the free commutative monoid (`bagLift`), **sets** the free
  join-semilattice with a least element, the free idempotent commutative
  monoid (`setLift`). The three lifts are the hom-set bijections of the
  free/forgetful adjunctions; they are natural in the alphabet and in the
  target (`bagLift_comp_map`, `comp_bagLift`, `setLift_comp_image`,
  `comp_setLift`).
* **The forgetful chain.** Reading a tuple's children forgets the arity
  (`Sequences.Tuple.toSeq`); `toBag` forgets order and `toSet`
  multiplicity. Each is the unique homomorphism of its kind that keeps
  singletons (`toBag_eq_lift`, `toSet_unique`), and each step is a
  reflection: a homomorphism from lists into a commutative monoid factors
  uniquely through bags (`existsUnique_factor_toBag`), and one from bags into
  a join-semilattice factors uniquely through sets
  (`existsUnique_factor_toSet`).
* **Universal folds.** For a generator into a monoid, `foldList`, `foldBag`
  and `foldSet` are the unique homomorphisms extending it
  (`foldList_unique`, `foldBag_unique`, `foldSet_unique`); they are the lifts
  above (`foldList_eq_lift`, `foldBag_eq_bagLift`). A list fold consumes bags
  exactly when the generator's values commute, and sets exactly when they are
  also idempotent (`foldList_factors_bag_iff`, `foldList_factors_set_iff`).
* `map` and `filter` commute with forgetting order and multiplicity
  (`map_natural`, `filter_natural`). On bags `map` keeps the size; on sets it
  merges what the function identifies, and keeps the size exactly when the
  function is injective on the set (`setMap_card_eq_iff`, `setMap_eq_support`).
* **Normal forms are sections.** Sorting is a section of `toBag` whose image
  is exactly the sorted lists (`toBag_sort`, `sort_toBag_of_sorted`); sorting
  a set is a section of the whole chain from lists to sets whose image is
  the strictly increasing lists (`toFinset_sort`, `sort_toFinset_of_sorted`);
  the duplicate-free representative is a section of `toSet` whose image is
  the duplicate-free bags (`toSet_val`). Two lists have the same bag normal
  form exactly when they are permutations of each other
  (`bagNormalForm_eq_iff`), and the same set normal form exactly when they
  have the same elements (`setNormalForm_eq_iff`).
* **A section is not a homomorphism.** No homomorphic section of `toBag`
  exists once two values differ (`Controls.no_hom_section`): commutativity is
  lost in lists.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Collections

open Mettapedia.Algebra.Collections.Sequences

universe u v w

variable {α : Type u} {β : Type v}

/-! ## Tuples -/

/-- A map into tuples of arity `n` is a tuple of `n` maps: the universal
property of the `n`-fold product. -/
def tupleMaps (γ : Type w) (n : Nat) : (γ → Tuple n α) ≃ Tuple n (γ → α) :=
  Equiv.piComm fun _ _ => α

@[simp] theorem tupleMaps_apply (γ : Type w) (n : Nat) (f : γ → Tuple n α) (i : Fin n) (c : γ) :
    tupleMaps γ n f i c = f c i := rfl

/-! ## Lists, bags and sets as free algebras -/

section Free

variable {M : Type w}

/-- **Bags are the free commutative monoid.** -/
def bagLift [AddCommMonoid M] : (α → M) ≃ (Multiset α →+ M) where
  toFun g := Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom g)
  invFun h a := h {a}
  left_inv g := by funext a; simp
  right_inv h := Multiset.addHom_ext fun a => by simp

@[simp] theorem bagLift_apply [AddCommMonoid M] (g : α → M) (s : Multiset α) :
    bagLift g s = (s.map g).sum := rfl

@[simp] theorem bagLift_singleton [AddCommMonoid M] (g : α → M) (a : α) :
    bagLift g {a} = g a := by simp

/-- Naturality in the target. -/
theorem comp_bagLift [AddCommMonoid M] {N : Type*} [AddCommMonoid N] (k : M →+ N) (g : α → M) :
    k.comp (bagLift g) = bagLift (k ∘ g) :=
  Multiset.addHom_ext fun a => by simp

/-- Naturality in the alphabet. -/
theorem bagLift_comp_map [AddCommMonoid M] (f : β → α) (g : α → M) :
    (bagLift g).comp (Multiset.mapAddMonoidHom f) = bagLift (g ∘ f) :=
  Multiset.addHom_ext fun a => by simp [Multiset.mapAddMonoidHom]

/-- Two join homomorphisms out of the sets agree once they agree on singletons. -/
theorem set_hom_ext [DecidableEq α] [SemilatticeSup β] [OrderBot β]
    {f g : SupBotHom (Finset α) β} (same : ∀ a, f {a} = g {a}) : f = g := by
  ext s
  induction s using Finset.induction_on with
  | empty =>
      change f ⊥ = g ⊥
      rw [map_bot, map_bot]
  | insert a s _ ih =>
      rw [Finset.insert_eq]
      change f ({a} ⊔ s) = g ({a} ⊔ s)
      rw [map_sup, map_sup, same, ih]

/-- **Sets are the free join-semilattice with a least element**, the free
idempotent commutative monoid. -/
def setLift [DecidableEq α] [SemilatticeSup β] [OrderBot β] :
    (α → β) ≃ SupBotHom (Finset α) β where
  toFun g :=
    { toFun := fun s => s.sup g
      map_sup' := fun s t => Finset.sup_union
      map_bot' := Finset.sup_empty }
  invFun h a := h {a}
  left_inv g := by funext a; simp
  right_inv h := set_hom_ext fun a => by simp

@[simp] theorem setLift_apply [DecidableEq α] [SemilatticeSup β] [OrderBot β] (g : α → β)
    (s : Finset α) : setLift g s = s.sup g := rfl

/-- Naturality in the target. -/
theorem comp_setLift [DecidableEq α] [SemilatticeSup β] [OrderBot β]
    {γ : Type*} [SemilatticeSup γ] [OrderBot γ] (k : SupBotHom β γ) (g : α → β) :
    k.comp (setLift g) = setLift (k ∘ g) :=
  set_hom_ext fun a => by simp

/-- Naturality in the alphabet. -/
theorem setLift_comp_image [DecidableEq α] [DecidableEq β] [SemilatticeSup M] [OrderBot M]
    (f : β → α) (g : α → M) (s : Finset β) :
    setLift g (s.image f) = setLift (g ∘ f) s := by
  simp [Finset.sup_image]

end Free

/-! ## Universal folds and the exact conditions for consuming bags and sets -/

section Folds

variable {M : Type w}

/-- The fold out of the free monoid determined by a generator. -/
def foldList [Monoid M] (generator : α → M) (values : List α) : M :=
  (values.map generator).prod

/-- The fold out of the free commutative monoid determined by a generator. -/
def foldBag [CommMonoid M] (generator : α → M) (values : Multiset α) : M :=
  (values.map generator).prod

/-- The fold out of the free idempotent commutative monoid. -/
def foldSet [CommMonoid M] (generator : α → M) (values : Finset α) : M :=
  values.prod generator

section Laws

variable (generator : α → M)

@[simp] theorem foldList_nil [Monoid M] : foldList generator [] = 1 := rfl

@[simp] theorem foldList_singleton [Monoid M] (value : α) :
    foldList generator [value] = generator value := by
  simp [foldList]

theorem foldList_append [Monoid M] (left right : List α) :
    foldList generator (left ++ right) = foldList generator left * foldList generator right := by
  simp [foldList, List.prod_append]

@[simp] theorem foldBag_zero [CommMonoid M] : foldBag generator 0 = 1 := by
  simp [foldBag]

@[simp] theorem foldBag_singleton [CommMonoid M] (value : α) :
    foldBag generator {value} = generator value := by
  simp [foldBag]

theorem foldBag_add [CommMonoid M] (left right : Multiset α) :
    foldBag generator (left + right) = foldBag generator left * foldBag generator right := by
  simp [foldBag, Multiset.prod_add]

/-- The bag fold restricted along the forgetful map is the list fold. -/
@[simp] theorem foldBag_coe [CommMonoid M] (values : List α) :
    foldBag generator values = foldList generator values := by
  simp [foldBag, foldList]

@[simp] theorem foldSet_empty [CommMonoid M] : foldSet generator ∅ = 1 := by
  simp [foldSet]

@[simp] theorem foldSet_singleton [CommMonoid M] (value : α) :
    foldSet generator {value} = generator value := by
  simp [foldSet]

/-- An idempotent value absorbs a smaller product into a larger one. -/
theorem prod_absorb_subset [CommMonoid M] [DecidableEq α]
    (idempotent : ∀ value, IsIdempotentElem (generator value))
    {small large : Finset α} (contained : small ⊆ large) :
    large.prod generator * small.prod generator = large.prod generator := by
  rw [← Finset.union_sdiff_of_subset contained,
    Finset.prod_union Finset.disjoint_sdiff, mul_comm, ← mul_assoc]
  congr 1
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun value _ => idempotent value)

theorem foldSet_union [CommMonoid M] [DecidableEq α]
    (idempotent : ∀ value, IsIdempotentElem (generator value)) (left right : Finset α) :
    foldSet generator (left ∪ right) = foldSet generator left * foldSet generator right := by
  unfold foldSet
  rw [← Finset.prod_union_inter, prod_absorb_subset generator idempotent
    (Finset.inter_subset_left.trans Finset.subset_union_left)]

/-- With idempotent generator values, the set fold restricted along the
forgetful map is the bag fold. -/
theorem foldSet_toFinset [CommMonoid M] [DecidableEq α]
    (idempotent : ∀ value, IsIdempotentElem (generator value)) (values : Multiset α) :
    foldSet generator values.toFinset = foldBag generator values := by
  unfold foldSet foldBag
  rw [Finset.prod_multiset_map_count]
  refine Finset.prod_congr rfl (fun value member => ?_)
  obtain ⟨count, hcount⟩ : ∃ count, values.count value = count + 1 :=
    Nat.exists_eq_succ_of_ne_zero
      (Multiset.count_ne_zero.mpr (Multiset.mem_toFinset.mp member))
  rw [hcount, (idempotent value).pow_succ_eq]

end Laws

/-! ### Uniqueness: each fold is the homomorphism extending its generator -/

theorem foldList_unique [Monoid M] (generator : α → M) (fold : List α → M)
    (nil : fold [] = 1) (append : ∀ left right, fold (left ++ right) = fold left * fold right)
    (singleton : ∀ value, fold [value] = generator value) :
    fold = foldList generator := by
  funext values
  induction values with
  | nil => exact nil
  | cons head tail ih =>
    rw [← List.singleton_append, append, ih, singleton, foldList_append, foldList_singleton]

theorem foldBag_unique [CommMonoid M] (generator : α → M) (fold : Multiset α → M)
    (zero : fold 0 = 1) (add : ∀ left right, fold (left + right) = fold left * fold right)
    (singleton : ∀ value, fold {value} = generator value) :
    fold = foldBag generator := by
  funext values
  induction values using Multiset.induction_on with
  | empty => simpa using zero
  | cons head tail ih =>
    rw [← Multiset.singleton_add, add, ih, singleton, foldBag_add, foldBag_singleton]

theorem foldSet_unique [CommMonoid M] [DecidableEq α] (generator : α → M)
    (fold : Finset α → M) (empty : fold ∅ = 1)
    (union : ∀ left right, fold (left ∪ right) = fold left * fold right)
    (singleton : ∀ value, fold {value} = generator value) :
    fold = foldSet generator := by
  funext values
  induction values using Finset.induction_on with
  | empty => simpa using empty
  | insert head tail fresh ih =>
    rw [Finset.insert_eq, union, ih, singleton, ← Finset.insert_eq]
    simp [foldSet, Finset.prod_insert fresh]

/-! ### Exact conditions for consuming bags and sets -/

/-- A list fold depends only on the bag exactly when the generator's values
commute pairwise. -/
theorem foldList_factors_bag_iff [Monoid M] (generator : α → M) :
    (∃ consume : Multiset α → M, ∀ values : List α,
        foldList generator values = consume values) ↔
      ∀ first second, Commute (generator first) (generator second) := by
  constructor
  · rintro ⟨consume, factors⟩ first second
    have swapped := factors [first, second]
    rw [show ((([first, second] : List α)) : Multiset α) = ([second, first] : List α) from
      Multiset.coe_eq_coe.mpr (List.Perm.swap _ _ []), ← factors] at swapped
    show generator first * generator second = generator second * generator first
    simpa [foldList] using swapped
  · intro commute
    refine ⟨Quot.lift (foldList generator) ?_, fun _ => rfl⟩
    intro left right permuted
    exact (permuted.map generator).prod_eq'
      (List.pairwise_map.mpr (List.pairwise_of_forall (fun first second => commute first second)))

/-- A commutative list fold depends only on the set of values exactly when
every generator value is idempotent. -/
theorem foldList_factors_set_iff [CommMonoid M] [DecidableEq α] (generator : α → M) :
    (∃ consume : Finset α → M, ∀ values : List α,
        foldList generator values = consume values.toFinset) ↔
      ∀ value, IsIdempotentElem (generator value) := by
  constructor
  · rintro ⟨consume, factors⟩ value
    have repeated := factors [value, value]
    rw [show ([value, value] : List α).toFinset = ([value] : List α).toFinset by simp,
      ← factors] at repeated
    simpa [foldList, IsIdempotentElem] using repeated
  · intro idempotent
    refine ⟨foldSet generator, fun values => ?_⟩
    rw [← foldBag_coe, ← foldSet_toFinset generator idempotent]
    rfl

/-! ## Forgetting order and multiplicity: naturality of map and filter -/

/-- Mapping commutes with forgetting order and with forgetting multiplicity. -/
theorem map_natural [DecidableEq α] [DecidableEq β] (function : α → β) (values : List α) :
    ((values.map function : List β) : Multiset β) = (values : Multiset α).map function ∧
      ((values : Multiset α).map function).toFinset =
        (values : Multiset α).toFinset.image function :=
  ⟨Multiset.map_coe function values |>.symm, Multiset.toFinset_map function _⟩

/-- Filtering commutes with forgetting order and with forgetting multiplicity. -/
theorem filter_natural [DecidableEq α] (keep : α → Prop) [DecidablePred keep]
    (values : List α) :
    ((values.filter (fun value => decide (keep value)) : List α) : Multiset α) =
        (values : Multiset α).filter keep ∧
      ((values : Multiset α).filter keep).toFinset = (values : Multiset α).toFinset.filter keep :=
  ⟨(Multiset.filter_coe keep values).symm, Multiset.toFinset_filter _ keep⟩

/-- Mapping a bag keeps its size: values identified by the function keep
their separate occurrences. -/
theorem bagMap_card (function : α → β) (values : Multiset α) :
    (values.map function).card = values.card :=
  Multiset.card_map function values

/-- Mapping a set merges the values the function identifies, so it keeps the
size exactly when the function is injective on the set. -/
theorem setMap_card_eq_iff [DecidableEq β] (function : α → β) (values : Finset α) :
    (values.image function).card = values.card ↔ Set.InjOn function values :=
  Finset.card_image_iff

/-- Mapping a set as a bag and then forgetting multiplicity is mapping it as
a set; the intermediate bag is duplicate-free exactly for injective maps. -/
theorem setMap_eq_support [DecidableEq β] (function : α → β) (values : Finset α) :
    values.image function = (values.val.map function).toFinset ∧
      ((values.val.map function).Nodup ↔ Set.InjOn function values) :=
  ⟨rfl, Multiset.nodup_map_iff_inj_on values.nodup⟩

end Folds

/-! ## The forgetful chain -/

section Chain

variable {M : Type w}

/-- Forgetting order: a list read as the bag of its elements. -/
def toBag (xs : List α) : Multiset α := xs

/-- Forgetting multiplicity: a bag read as the set of its elements. -/
def toSet [DecidableEq α] (s : Multiset α) : Finset α := s.toFinset

@[simp] theorem toBag_nil : toBag ([] : List α) = 0 := rfl

@[simp] theorem toBag_append (xs ys : List α) : toBag (xs ++ ys) = toBag xs + toBag ys :=
  (Multiset.coe_add xs ys).symm

@[simp] theorem toBag_singleton (a : α) : toBag [a] = {a} := rfl

@[simp] theorem toSet_zero [DecidableEq α] : toSet (0 : Multiset α) = ∅ := rfl

@[simp] theorem toSet_add [DecidableEq α] (s t : Multiset α) :
    toSet (s + t) = toSet s ∪ toSet t :=
  Multiset.toFinset_add s t

@[simp] theorem toSet_singleton [DecidableEq α] (a : α) : toSet ({a} : Multiset α) = {a} := by
  simp [toSet]

theorem toBag_eq_sum (xs : List α) : toBag xs = (xs.map fun a => ({a} : Multiset α)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      rw [List.map_cons, List.sum_cons, ← ih]
      change ((a :: xs : List α) : Multiset α) = {a} + (xs : Multiset α)
      rw [← Multiset.cons_coe, Multiset.singleton_add]

/-- `toBag` is the monoid homomorphism out of the free monoid that keeps
singletons. -/
theorem toBag_eq_lift (xs : FreeAddMonoid α) :
    toBag (FreeAddMonoid.toList xs) = FreeAddMonoid.lift (fun a => ({a} : Multiset α)) xs := by
  rw [FreeAddMonoid.lift_apply, toBag_eq_sum]

/-- `toSet` is the only map from bags to sets that sends the empty bag to the
empty set, sums to unions and singletons to singletons. -/
theorem toSet_unique [DecidableEq α] (h : Multiset α → Finset α) (zero : h 0 = ∅)
    (add : ∀ s t, h (s + t) = h s ∪ h t) (single : ∀ a, h {a} = {a}) : h = toSet := by
  funext s
  induction s using Multiset.induction_on with
  | empty => exact zero
  | cons a s ih =>
      rw [← Multiset.singleton_add, add, single, ih, toSet_add, toSet_singleton]

/-- **Abelianization.** Every homomorphism from lists into a commutative
monoid factors through `toBag`, in exactly one way. -/
theorem existsUnique_factor_toBag [AddCommMonoid M] (h : FreeAddMonoid α →+ M) :
    ∃! k : Multiset α →+ M, ∀ xs : FreeAddMonoid α, k (toBag (FreeAddMonoid.toList xs)) = h xs := by
  refine ⟨bagLift (fun a => h (FreeAddMonoid.of a)), ?_, ?_⟩
  · intro xs
    have homs : (bagLift (fun a => h (FreeAddMonoid.of a))).comp
        (FreeAddMonoid.lift fun a => ({a} : Multiset α)) = h :=
      FreeAddMonoid.hom_eq fun a => by simp
    rw [toBag_eq_lift]
    exact DFunLike.congr_fun homs xs
  · intro k factors
    apply Multiset.addHom_ext
    intro a
    rw [bagLift_singleton, ← factors (FreeAddMonoid.of a)]
    rfl

/-- **The idempotent quotient.** A map from bags into a join-semilattice with
a least element that sends sums to joins factors through `toSet`, in
exactly one way. -/
theorem existsUnique_factor_toSet [DecidableEq α] [SemilatticeSup β] [OrderBot β]
    (h : Multiset α → β) (zero : h 0 = ⊥) (add : ∀ s t, h (s + t) = h s ⊔ h t) :
    ∃! k : SupBotHom (Finset α) β, ∀ s, k (toSet s) = h s := by
  refine ⟨setLift (fun a => h {a}), ?_, ?_⟩
  · intro s
    induction s using Multiset.induction_on with
    | empty => simp [toSet, zero]
    | cons a s ih =>
        rw [← Multiset.singleton_add, add, ← ih, toSet_add, toSet_singleton]
        change ({a} ∪ toSet s).sup _ = _
        rw [Finset.sup_union, Finset.sup_singleton]
        rfl
  · intro k factors
    apply set_hom_ext
    intro a
    rw [← toSet_singleton, factors]
    simp

/-- The list folds are the free monoid's lifts. -/
theorem foldList_eq_lift [Monoid M] (g : α → M) (xs : List α) :
    foldList g xs = FreeMonoid.lift g (FreeMonoid.ofList xs) :=
  (FreeMonoid.lift_ofList g xs).symm

/-- The bag folds are the free commutative monoid's lifts, read
multiplicatively. -/
theorem foldBag_eq_bagLift [CommMonoid M] (g : α → M) (s : Multiset α) :
    foldBag g s = (bagLift (fun a => Additive.ofMul (g a)) s).toMul := by
  induction s using Multiset.induction_on with
  | empty => simp [foldBag]
  | cons a s ih =>
      rw [← Multiset.singleton_add, foldBag_add, ih, map_add, foldBag_singleton, bagLift_singleton]
      rfl

end Chain

/-! ## Normal forms as sections -/

section Sections

variable [LinearOrder α]

/-- Sorting a bag gives a list with that bag of elements. -/
@[simp] theorem toBag_sort (s : Multiset α) : toBag (s.sort) = s := Multiset.sort_eq s _

/-- The image of sorting is exactly the sorted lists. -/
theorem sort_toBag_of_sorted {xs : List α} (sorted : xs.Pairwise (· ≤ ·)) :
    (toBag xs).sort = xs := by
  change Multiset.sort (↑xs) = xs
  rw [Multiset.coe_sort]
  exact List.mergeSort_eq_self (· ≤ ·) sorted

theorem mem_range_sort_iff (xs : List α) :
    xs ∈ Set.range (fun s : Multiset α => s.sort) ↔ xs.Pairwise (· ≤ ·) := by
  constructor
  · rintro ⟨s, rfl⟩
    exact Multiset.pairwise_sort s _
  · intro sorted
    exact ⟨toBag xs, sort_toBag_of_sorted sorted⟩

/-- The bag normal form of a list. -/
def bagNormalForm (xs : List α) : List α := (toBag xs).sort

/-- Two lists have one bag normal form exactly when they are permutations of
each other. -/
theorem bagNormalForm_eq_iff (xs ys : List α) :
    bagNormalForm xs = bagNormalForm ys ↔ xs.Perm ys := by
  constructor
  · intro same
    have bags := congrArg toBag same
    simp only [bagNormalForm, toBag_sort] at bags
    exact Multiset.coe_eq_coe.mp bags
  · intro permuted
    unfold bagNormalForm
    rw [show toBag xs = toBag ys from Multiset.coe_eq_coe.mpr permuted]

theorem bagNormalForm_idempotent (xs : List α) :
    bagNormalForm (bagNormalForm xs) = bagNormalForm xs := by
  unfold bagNormalForm
  rw [toBag_sort]

/-- The duplicate-free representative is a section of `toSet`. -/
@[simp] theorem toSet_val (s : Finset α) : toSet s.val = s := Finset.val_toFinset s

/-- Its image is exactly the duplicate-free bags. -/
theorem val_toSet_of_nodup {s : Multiset α} (nodup : s.Nodup) : (toSet s).val = s :=
  Multiset.toFinset_val s ▸ Multiset.dedup_eq_self.mpr nodup

/-- Sorting a set gives a list with that set of elements. -/
@[simp] theorem toFinset_sort (s : Finset α) : (s.sort).toFinset = s := Finset.sort_toFinset s _

/-- The image of sorting sets is exactly the strictly increasing lists. -/
theorem sort_toFinset_of_sorted {xs : List α} (sorted : xs.Pairwise (· < ·)) :
    xs.toFinset.sort = xs := by
  have nodup : xs.Nodup := sorted.imp (fun less => ne_of_lt less)
  exact (List.toFinset_sort (· ≤ ·) nodup).mpr (sorted.imp le_of_lt)

/-- The set normal form of a list: its distinct elements, in order. -/
def setNormalForm (xs : List α) : List α := xs.toFinset.sort

/-- Two lists have one set normal form exactly when they have the same
elements. -/
theorem setNormalForm_eq_iff (xs ys : List α) :
    setNormalForm xs = setNormalForm ys ↔ ∀ a, a ∈ xs ↔ a ∈ ys := by
  constructor
  · intro same a
    have sets := congrArg List.toFinset same
    simp only [setNormalForm, toFinset_sort] at sets
    simpa using congrArg (a ∈ ·) sets
  · intro members
    unfold setNormalForm
    congr 1
    ext a
    simpa using members a

theorem setNormalForm_pairwise (xs : List α) : (setNormalForm xs).Pairwise (· < ·) :=
  (Finset.sortedLT_sort _).pairwise

end Sections

/-! ## Controls -/

namespace Controls


/-- A noncommutative fold does not consume bags: the free monoid on two
letters separates the two orders. -/
theorem freeMonoid_fold_not_bag :
    ¬ ∃ consume : Multiset Bool → FreeMonoid Bool, ∀ values : List Bool,
        foldList FreeMonoid.of values = consume values := by
  rw [foldList_factors_bag_iff]
  intro commute
  have := (commute true false).eq
  have lists := congrArg FreeMonoid.toList this
  simp at lists

/-- Addition of naturals consumes bags but not sets: repetition counts. -/
theorem nat_sum_bag_not_set :
    (∃ consume : Multiset ℕ → Multiplicative ℕ, ∀ values : List ℕ,
        foldList Multiplicative.ofAdd values = consume values) ∧
      ¬ ∃ consume : Finset ℕ → Multiplicative ℕ, ∀ values : List ℕ,
        foldList Multiplicative.ofAdd values = consume values.toFinset := by
  refine ⟨(foldList_factors_bag_iff _).mpr (fun _ _ => Commute.all _ _), ?_⟩
  rw [foldList_factors_set_iff]
  intro idempotent
  have := idempotent 1
  simp [IsIdempotentElem, ← ofAdd_add] at this

/-- Natural numbers under maximum, with unit zero: a commutative idempotent
monoid. -/
def MaxNat : Type := ℕ

instance : CommMonoid MaxNat where
  mul first second := (max first second : ℕ)
  one := (0 : ℕ)
  mul_assoc first second third := max_assoc (α := ℕ) first second third
  one_mul value := max_eq_right (Nat.zero_le (value : ℕ))
  mul_one value := max_eq_left (Nat.zero_le (value : ℕ))
  mul_comm first second := max_comm (α := ℕ) first second

/-- A natural number read in the maximum monoid. -/
def MaxNat.of (value : ℕ) : MaxNat := value

/-- Maximum consumes sets: it is commutative and idempotent. -/
theorem max_consumes_sets :
    ∃ consume : Finset ℕ → MaxNat, ∀ values : List ℕ,
      foldList MaxNat.of values = consume values.toFinset := by
  rw [foldList_factors_set_iff]
  intro value
  exact max_self (α := ℕ) value

/-- Mapping by a constant: the bag keeps both occurrences, the set merges
them. -/
theorem constant_map_bag_vs_set :
    (({1, 2} : Multiset ℕ).map (fun _ => (0 : ℕ))) = {0, 0} ∧
      (({1, 2} : Finset ℕ).image (fun _ => (0 : ℕ))) = {0} ∧
      ¬ Set.InjOn (fun _ : ℕ => (0 : ℕ)) (({1, 2} : Finset ℕ) : Set ℕ) := by
  refine ⟨by simp, by decide, ?_⟩
  intro injective
  have := injective (by simp : (1 : ℕ) ∈ (({1, 2} : Finset ℕ) : Set ℕ))
    (by simp : (2 : ℕ) ∈ (({1, 2} : Finset ℕ) : Set ℕ)) rfl
  omega

/-- Forgetting order identifies permutations; forgetting multiplicity also
merges repetitions. -/
theorem forgetful_chain :
    toBag [2, 1, 2] = toBag ([1, 2, 2] : List ℕ) ∧
      toBag [2, 1] ≠ toBag ([1] : List ℕ) ∧
      toSet ({1, 1, 2} : Multiset ℕ) = {1, 2} ∧
      ({1, 1, 2} : Multiset ℕ) ≠ {1, 2} := by
  refine ⟨Multiset.coe_eq_coe.mpr (by decide), by decide, by decide, by decide⟩

/-- Normal forms: `[2 1 2]` as a bag is `[1 2 2]`, as a set `[1 2]`. -/
theorem normal_forms :
    bagNormalForm [2, 1, 2] = ([1, 2, 2] : List ℕ) ∧ setNormalForm [2, 1, 2] = ([1, 2] : List ℕ) := by
  constructor
  · unfold bagNormalForm
    rw [show toBag ([2, 1, 2] : List ℕ) = toBag [1, 2, 2] from Multiset.coe_eq_coe.mpr (by decide)]
    exact sort_toBag_of_sorted (by decide)
  · unfold setNormalForm
    rw [show ([2, 1, 2] : List ℕ).toFinset = ([1, 2] : List ℕ).toFinset by decide]
    exact sort_toFinset_of_sorted (by decide)

/-- An unsorted list is the normal form of no bag. -/
theorem unsorted_not_normal : ([2, 1] : List ℕ) ∉ Set.range (fun s : Multiset ℕ => s.sort) := by
  rw [mem_range_sort_iff]
  decide

/-- **Normal forms are sections, never homomorphic ones.** A homomorphic
section of `toBag` would make two singletons commute in the free monoid. -/
theorem no_hom_section (a b : α) (different : a ≠ b) :
    ¬ ∃ k : Multiset α →+ FreeAddMonoid α, ∀ s, toBag (FreeAddMonoid.toList (k s)) = s := by
  rintro ⟨k, section_⟩
  have single : ∀ c : α, FreeAddMonoid.toList (k {c}) = [c] := by
    intro c
    have bag := section_ {c}
    obtain ⟨xs, hxs⟩ : ∃ xs, FreeAddMonoid.toList (k {c}) = xs := ⟨_, rfl⟩
    rw [hxs] at bag
    have length : xs.length = 1 := by
      simpa [toBag] using congrArg Multiset.card bag
    obtain ⟨d, rfl⟩ := List.length_eq_one_iff.mp length
    have : d = c := by simpa [toBag] using bag
    rw [hxs, this]
  have swapped := congrArg (fun s => FreeAddMonoid.toList (k s))
    (add_comm ({a} : Multiset α) {b})
  simp only [map_add, FreeAddMonoid.toList_add, single] at swapped
  simp only [List.singleton_append, List.cons.injEq, and_true] at swapped
  exact different swapped.1

end Controls

end Mettapedia.Algebra.Collections
