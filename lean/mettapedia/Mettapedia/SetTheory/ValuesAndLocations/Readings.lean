import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Card
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

/-!
# Two readings of `{a b}`: a value, or a location that holds a value

## The value reading

`{a b}` is a value. Read as a set it is an element of `Finset A`, the free idempotent commutative
monoid on `A`; read as a bag, an element of `Multiset A`, the free commutative monoid.
`Mettapedia.Algebra.CollectionFold` proves these universal properties and says which folds
descend to which reading. Equality is by elements: two sets are equal when they have the same
members (`Finset.ext`), two bags when every element occurs equally often (`Multiset.ext`).
Adding is a function, `insert c {a b} = {a b c}` (`Controls.set_insert`), and a name bound to
`{a b}` goes on denoting `{a b}`.

* Order is invisible in both readings (`Controls.bag_swap`, `Controls.set_swap`); repetition is
  invisible in sets (`Controls.set_repeat`) and counted in bags (`Controls.bag_counts`).
* Counting does not descend from bags to sets (`Controls.count_not_on_sets`).
* A list compared position by position observes order; sorted forms do not: two lists list one
  bag exactly when their sorted forms are equal (`sorted_eq_iff`, `Controls.listing_vs_canonical`).
  So a canonical form makes positional equality into bag equality.
* **When adding changes nothing.** Adding one element never leaves a bag as it was
  (`bag_cons_ne_self`); it leaves a set as it was exactly when the element is a member
  (`Finset.insert_eq_self`). `Reuse` uses these two facts: an update that changes nothing may be
  done in place even under sharing.

## The location reading

`new-space` makes a location in a store (`Store`). A location has an identity of its own: two
spaces made empty are two locations with equal contents (`two_new_spaces`), and a write to one
leaves the other as it was (`snap_write_of_ne`).

* "Same contents" is an observation at a moment, not an identity: one write separates two
  locations that held equal contents (`two_new_spaces`), so no relation on locations agrees with
  "same contents" at every store (`no_identity_by_contents`). Equality of handles is equality of
  locations, which no write changes.
* **The revision contract.** A store moves a location's revision on every write (`write`). Along
  any run of allocations and writes, a location whose revision did not move holds what it held
  (`Run.snap_eq_of_rev_eq`). So an observation stamped with revisions, such as "these two hold the
  same contents", stays true while both revisions stay put (`Run.sameContents_of_revs`). This is
  the store side of the contract that the `full-of` check relies on
  (`Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.FullOfCheck`, `Tracks`),
  where the right to make such an observation (`observe`) is also checked.
* **Sets and bags as location contents.** A set location may skip an add of a member: then its
  revision moves exactly when its contents change (`addSet_rev_eq_iff`). A bag location's add
  always changes its contents (`addBag_changes`).

## The bridge: snapshots

The snapshot (`snap`, what `collapse (get-atoms …)` returns, read as a set or a bag) sends a store
and a location to a value. A write at a location is the value update at that location
(`snap_write_self`): the snapshot carries the location step to the value step. A snapshot is a
value: a later write at its location does not change it, and the location then holds another
value (`stale_snapshot`); the revision shows that it moved (`write_moves_rev`).
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.ValuesAndLocations

universe u v

/-! ## Values: when adding changes nothing -/

/-- **Adding never leaves a bag as it was.** -/
theorem bag_cons_ne_self {A : Type u} (x : A) (s : Multiset A) : x ::ₘ s ≠ s := fun same => by
  have := congrArg Multiset.card same
  rw [Multiset.card_cons] at this
  omega

/-- **Listings observe order; canonical forms do not.** Two lists list one bag exactly when their
sorted forms are equal. A listing of an unordered space compared position by position can tell
two listings of one bag apart (`Controls.listing_vs_canonical`); its sorted form cannot. -/
theorem sorted_eq_iff {A : Type u} [LinearOrder A] (l₁ l₂ : List A) :
    (l₁ : Multiset A).sort = (l₂ : Multiset A).sort ↔ (l₁ : Multiset A) = l₂ := by
  constructor
  · intro same
    rw [← Multiset.sort_eq (l₁ : Multiset A) (· ≤ ·), ← Multiset.sort_eq (l₂ : Multiset A) (· ≤ ·),
      same]
  · intro same
    rw [same]

/-! ## Locations -/

/-- A store: what each location holds (`none` when it has not been made) and how many writes it
has seen. -/
structure Store (L : Type u) (V : Type v) where
  holds : L → Option V
  rev : L → ℕ

namespace Store

variable {L : Type u} {V : Type v} [DecidableEq L]

/-- `new-space` at the location `ℓ`: it now holds `empty`. -/
def alloc (σ : Store L V) (ℓ : L) (empty : V) : Store L V :=
  ⟨Function.update σ.holds ℓ (some empty), σ.rev⟩

/-- A write at `ℓ` (`add-atom`, `remove-atom`): its contents become `f` of what they were, and its
revision moves. -/
def write (σ : Store L V) (ℓ : L) (f : V → V) : Store L V :=
  ⟨Function.update σ.holds ℓ ((σ.holds ℓ).map f), Function.update σ.rev ℓ (σ.rev ℓ + 1)⟩

/-- **The snapshot**: the value a location holds now. -/
def snap (σ : Store L V) (ℓ : L) : Option V := σ.holds ℓ

/-- "Same contents": an observation at the store `σ`. -/
def SameContents (σ : Store L V) (ℓ₁ ℓ₂ : L) : Prop := σ.snap ℓ₁ = σ.snap ℓ₂

variable {σ : Store L V} {ℓ ℓ' : L}

/-- **The bridge**: a write at a location is the value update at that location. -/
@[simp] theorem snap_write_self (f : V → V) : (σ.write ℓ f).snap ℓ = (σ.snap ℓ).map f := by
  simp [write, snap]

/-- **The frame law**: a write at `ℓ` leaves every other location as it was. -/
theorem snap_write_of_ne (f : V → V) (other : ℓ' ≠ ℓ) : (σ.write ℓ f).snap ℓ' = σ.snap ℓ' := by
  simp [write, snap, Function.update_of_ne other]

@[simp] theorem snap_alloc_self (empty : V) : (σ.alloc ℓ empty).snap ℓ = some empty := by
  simp [alloc, snap]

theorem snap_alloc_of_ne (empty : V) (other : ℓ' ≠ ℓ) : (σ.alloc ℓ empty).snap ℓ' = σ.snap ℓ' := by
  simp [alloc, snap, Function.update_of_ne other]

@[simp] theorem rev_alloc (empty : V) : (σ.alloc ℓ empty).rev = σ.rev := rfl

@[simp] theorem rev_write_self (f : V → V) : (σ.write ℓ f).rev ℓ = σ.rev ℓ + 1 := by
  simp [write]

theorem rev_write_of_ne (f : V → V) (other : ℓ' ≠ ℓ) : (σ.write ℓ f).rev ℓ' = σ.rev ℓ' := by
  simp [write, Function.update_of_ne other]

/-- **A write moves the revision of its location.** -/
theorem write_moves_rev (f : V → V) : (σ.write ℓ f).rev ℓ ≠ σ.rev ℓ := by simp

/-- **A snapshot goes stale.** Take the snapshot `v` of `ℓ`, then write `ℓ` with an update that
changes `v`: the location now holds another value, while `v` is still `v`. -/
theorem stale_snapshot {v : V} (taken : σ.snap ℓ = some v) {f : V → V} (moves : f v ≠ v) :
    (σ.write ℓ f).snap ℓ ≠ some v := by
  rw [snap_write_self, taken, Option.map_some]
  exact fun same => moves (Option.some.inj same)

/-- **Two `new-space`s.** Make `ℓ₁`, then make `ℓ₂` at a place that holds nothing: they are two
locations holding the same value, and an update at the first that changes that value separates
them, while the second still holds it. -/
theorem two_new_spaces {ℓ₁ ℓ₂ : L} (empty : V)
    (fresh₂ : (σ.alloc ℓ₁ empty).holds ℓ₂ = none) {f : V → V} (moves : f empty ≠ empty) :
    ℓ₁ ≠ ℓ₂ ∧ ((σ.alloc ℓ₁ empty).alloc ℓ₂ empty).SameContents ℓ₁ ℓ₂ ∧
      ¬ (((σ.alloc ℓ₁ empty).alloc ℓ₂ empty).write ℓ₁ f).SameContents ℓ₁ ℓ₂ ∧
      (((σ.alloc ℓ₁ empty).alloc ℓ₂ empty).write ℓ₁ f).snap ℓ₂ = some empty := by
  have apart : ℓ₁ ≠ ℓ₂ := by
    rintro rfl
    have : (σ.alloc ℓ₁ empty).holds ℓ₁ = some empty := snap_alloc_self empty
    rw [this] at fresh₂
    cases fresh₂
  have first : ((σ.alloc ℓ₁ empty).alloc ℓ₂ empty).snap ℓ₁ = some empty := by
    rw [snap_alloc_of_ne _ apart, snap_alloc_self]
  have second : ((σ.alloc ℓ₁ empty).alloc ℓ₂ empty).snap ℓ₂ = some empty := snap_alloc_self _
  refine ⟨apart, first.trans second.symm, fun same => ?_, ?_⟩
  · unfold SameContents at same
    rw [snap_write_self, snap_write_of_ne _ (Ne.symm apart), first, second, Option.map_some] at same
    exact moves (Option.some.inj same)
  · rw [snap_write_of_ne _ (Ne.symm apart), second]

/-- **No identity by contents.** If two different locations can hold one value and an update can
change that value, then no relation on locations agrees with "same contents" at every store.
Equality of handles must therefore be equality of locations; same contents is an observation of
one store. -/
theorem no_identity_by_contents {ℓ₁ ℓ₂ : L} (apart : ℓ₁ ≠ ℓ₂) {v : V} {f : V → V}
    (moves : f v ≠ v) :
    ¬ ∃ E : L → L → Prop, ∀ σ : Store L V, ∀ m₁ m₂, E m₁ m₂ ↔ σ.SameContents m₁ m₂ := by
  rintro ⟨E, agrees⟩
  let σ₀ : Store L V := ⟨fun _ => some v, fun _ => 0⟩
  have before : σ₀.SameContents ℓ₁ ℓ₂ := rfl
  have after : ¬ (σ₀.write ℓ₁ f).SameContents ℓ₁ ℓ₂ := fun same => by
    unfold SameContents at same
    rw [snap_write_self, snap_write_of_ne _ (Ne.symm apart)] at same
    exact moves (Option.some.inj same)
  exact after ((agrees _ ℓ₁ ℓ₂).mp ((agrees σ₀ ℓ₁ ℓ₂).mpr before))

/-! ## Revisions -/

/-- A run of a store: allocations at fresh locations and writes. -/
inductive Run : Store L V → Store L V → Prop
  | refl (σ : Store L V) : Run σ σ
  | alloc {σ σ' : Store L V} (ℓ : L) (empty : V) :
      σ.holds ℓ = none → Run (σ.alloc ℓ empty) σ' → Run σ σ'
  | write {σ σ' : Store L V} (ℓ : L) (f : V → V) : Run (σ.write ℓ f) σ' → Run σ σ'

/-- Revisions never go back along a run. -/
theorem Run.rev_le {σ σ' : Store L V} (run : Run σ σ') (ℓ : L) : σ.rev ℓ ≤ σ'.rev ℓ := by
  induction run with
  | refl => exact le_rfl
  | alloc _ _ _ _ ih => exact ih
  | @write σ σ' m f _ ih =>
      refine le_trans ?_ ih
      by_cases same : ℓ = m
      · subst same; simp
      · rw [rev_write_of_ne _ same]

/-- **The revision contract holds along every run.** A location that had been made and whose
revision did not move holds what it held. -/
theorem Run.snap_eq_of_rev_eq {σ σ' : Store L V} (run : Run σ σ') {ℓ : L}
    (made : (σ.holds ℓ).isSome) (still : σ'.rev ℓ = σ.rev ℓ) : σ'.snap ℓ = σ.snap ℓ := by
  induction run with
  | refl => rfl
  | @alloc σ σ' m empty fresh _ ih =>
      have other : ℓ ≠ m := by
        rintro rfl
        rw [fresh] at made
        cases made
      have made' : ((σ.alloc m empty).holds ℓ).isSome := by
        rw [show (σ.alloc m empty).holds ℓ = σ.holds ℓ from snap_alloc_of_ne empty other]
        exact made
      rw [ih made' still, snap_alloc_of_ne empty other]
  | @write σ σ' m f rest ih =>
      by_cases same : ℓ = m
      · subst same
        have := rest.rev_le ℓ
        rw [rev_write_self] at this
        omega
      · have made' : ((σ.write m f).holds ℓ).isSome := by
          rw [show (σ.write m f).holds ℓ = σ.holds ℓ from snap_write_of_ne f same]
          exact made
        rw [ih made' (by rw [still, rev_write_of_ne f same]), snap_write_of_ne f same]

/-- **An observation stamped with revisions stays true while they stay put.** -/
theorem Run.sameContents_of_revs {σ σ' : Store L V} (run : Run σ σ') {ℓ₁ ℓ₂ : L}
    (made₁ : (σ.holds ℓ₁).isSome) (made₂ : (σ.holds ℓ₂).isSome)
    (still₁ : σ'.rev ℓ₁ = σ.rev ℓ₁) (still₂ : σ'.rev ℓ₂ = σ.rev ℓ₂)
    (same : σ.SameContents ℓ₁ ℓ₂) : σ'.SameContents ℓ₁ ℓ₂ := by
  unfold SameContents at same ⊢
  rw [run.snap_eq_of_rev_eq made₁ still₁, run.snap_eq_of_rev_eq made₂ still₂, same]

/-! ## Set and bag locations -/

section Kinds

variable {A : Type v} [DecidableEq A]

/-- `add-atom` at a set location: an atom it holds is not added again, and nothing is written. -/
def addSet (σ : Store L (Finset A)) (ℓ : L) (x : A) : Store L (Finset A) :=
  match σ.holds ℓ with
  | some s => if x ∈ s then σ else σ.write ℓ (insert x)
  | none => σ

/-- `add-atom` at a bag location: one more occurrence. -/
def addBag (σ : Store L (Multiset A)) (ℓ : L) (x : A) : Store L (Multiset A) := σ.write ℓ (x ::ₘ ·)

/-- **A set location's revision moves exactly when its contents change.** -/
theorem addSet_rev_eq_iff (σ : Store L (Finset A)) (ℓ : L) (x : A) :
    (addSet σ ℓ x).rev ℓ = σ.rev ℓ ↔ (addSet σ ℓ x).snap ℓ = σ.snap ℓ := by
  unfold addSet
  cases held : σ.holds ℓ with
  | none => simp
  | some s =>
      by_cases member : x ∈ s
      · simp [member]
      · simp only [member, if_false, rev_write_self, snap_write_self]
        simp only [snap, held, Option.map_some, Option.some.injEq]
        constructor
        · omega
        · intro same
          exact absurd (Finset.insert_eq_self.mp same) member

omit [DecidableEq A] in
/-- **A bag location's add always changes its contents** (once the location is made). -/
theorem addBag_changes (σ : Store L (Multiset A)) (ℓ : L) (x : A) {s : Multiset A}
    (held : σ.holds ℓ = some s) : (addBag σ ℓ x).snap ℓ ≠ σ.snap ℓ := by
  unfold addBag
  rw [snap_write_self]
  simp only [snap, held, Option.map_some, ne_eq, Option.some.injEq]
  exact bag_cons_ne_self x s

end Kinds

end Store

/-! ## Controls -/

namespace Controls

open Store

/-- **Value, positive**: adding `c` to `{a b}` gives `{a b c}`. -/
theorem set_insert : insert 'c' ({'a', 'b'} : Finset Char) = {'a', 'b', 'c'} := by decide

/-- **Value, positive**: order is invisible in a bag. -/
theorem bag_swap : ({'a', 'b'} : Multiset Char) = {'b', 'a'} := Multiset.cons_swap _ _ _

/-- **Value, positive**: order is invisible in a set. -/
theorem set_swap : ({'a', 'b'} : Finset Char) = {'b', 'a'} := by decide

/-- **Value, positive**: repetition is invisible in a set. -/
theorem set_repeat : ({'a', 'a'} : Finset Char) = {'a'} := by decide

/-- **Value, negative**: a bag counts its elements: `{a a}` is not `{a}`. -/
theorem bag_counts : ({'a', 'a'} : Multiset Char) ≠ {'a'} := by decide

/-- **Listing, negative; canonical form, positive**: `(1 2)` and `(2 1)` differ as lists and list one
bag, whose sorted form is one. -/
theorem listing_vs_canonical :
    [1, 2] ≠ [2, 1] ∧ (([1, 2] : List ℕ) : Multiset ℕ).sort = (([2, 1] : List ℕ) : Multiset ℕ).sort :=
  ⟨by decide, (sorted_eq_iff _ _).mpr (Multiset.coe_eq_coe.mpr (List.Perm.swap _ _ _))⟩

/-- **Value, negative**: counting does not descend to sets: two bags with one set of members and
different sizes. -/
theorem count_not_on_sets :
    ({1, 1} : Multiset ℕ).toFinset = ({1} : Multiset ℕ).toFinset ∧
      Multiset.card ({1, 1} : Multiset ℕ) ≠ Multiset.card ({1} : Multiset ℕ) := by decide

/-- The empty store over locations `ℕ`. -/
def empty₀ : Store ℕ (Multiset Char) := ⟨fun _ => none, fun _ => 0⟩

/-- `!(bind! &a (new-space))`, `!(bind! &b (new-space))`, then `x` added to both. -/
def bothX : Store ℕ (Multiset Char) :=
  addBag (addBag ((empty₀.alloc 0 0).alloc 1 0) 0 'x') 1 'x'

/-- **Location, positive**: two spaces holding `x` are two locations with the same contents. -/
theorem bothX_same_contents : bothX.SameContents 0 1 ∧ (0 : ℕ) ≠ 1 := by
  refine ⟨?_, by decide⟩
  unfold SameContents bothX addBag
  rw [snap_write_of_ne _ (by decide : (0 : ℕ) ≠ 1), snap_write_self, snap_write_self,
    snap_write_of_ne _ (by decide : (1 : ℕ) ≠ 0), snap_alloc_of_ne _ (by decide : (0 : ℕ) ≠ 1),
    snap_alloc_self, snap_alloc_self]

/-- **Location, negative**: after `y` is added to the first, the contents differ; the second still
holds `{x}`. -/
theorem bothX_separated :
    ¬ (addBag bothX 0 'y').SameContents 0 1 ∧ (addBag bothX 0 'y').snap 1 = some {'x'} := by
  have first : bothX.snap 0 = some {'x'} := by
    unfold bothX addBag
    rw [snap_write_of_ne _ (by decide : (0 : ℕ) ≠ 1), snap_write_self,
      snap_alloc_of_ne _ (by decide : (0 : ℕ) ≠ 1), snap_alloc_self]
    rfl
  have second : bothX.snap 1 = some {'x'} := by
    unfold bothX addBag
    rw [snap_write_self, snap_write_of_ne _ (by decide : (1 : ℕ) ≠ 0), snap_alloc_self]
    rfl
  refine ⟨fun same => ?_, ?_⟩
  · unfold SameContents addBag at same
    rw [snap_write_self, snap_write_of_ne _ (by decide : (1 : ℕ) ≠ 0), first, second] at same
    revert same
    decide
  · unfold addBag
    rw [snap_write_of_ne _ (by decide : (1 : ℕ) ≠ 0), second]

/-- **Set location, positive**: adding a member writes nothing, so the revision stays. -/
theorem set_member_add_keeps_rev :
    (addSet ((⟨fun _ => none, fun _ => 0⟩ : Store ℕ (Finset Char)).alloc 0 {'x'}) 0 'x').rev 0 = 0 := by
  decide

end Controls

end Mettapedia.SetTheory.ValuesAndLocations
