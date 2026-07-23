import Mettapedia.OSLF.PathMap.PathAlgebra.ZippyLaws

/-!
# The path-space operations and their laws

This module formalises the operation set of Zippy's *current* equational theory -- the one on
branch `b`, where every rule carries a `proofs/laws/*.smt2` reference -- against the
finite-language semantics of `FinLanguage`.

`ZippyLaws` targets the theory on `master`, which differs substantially:

* `master` declares `(Neg Path)` with `(Concat (Neg x) x) → (Eps)`, making paths a **group**,
  and defines `Unwrap` through that inverse.  Branch `b` **removes** `Neg`: `Path` is a plain
  free monoid and `Unwrap` is defined case-wise, yielding `Empty` on a prefix mismatch.  That
  is exactly the partial operation `FreeMonoidBoundary.unwrapPath` -- an independent arrival
  at the same design, from the opposite direction.
* `master`'s two summand-dropping `Restriction` rules (refuted in `ZippyLaws.ZippyRefutation`)
  are gone, replaced by distribution over the *selector* together with
  `Restriction x (Singleton p) = Wrap p (Unwrap x p)`.

## Main definitions

* `dropPrefix`, `unwrap` -- prefix stripping on paths and on spaces.
* `tailsUnion`, `tailsInter` -- the tail folds over `head`.
* `raffination` -- `x \ Restriction x y`.
* `iterC` -- the loop-invariant iteration model.

## Main results

* `mem_unwrap` -- the keystone: `y ∈ unwrap s p ↔ p * y ∈ s`.  Every `Unwrap` law follows.
* `restrict_singleton_eq_wrap_unwrap` -- `Restriction x {p} = Wrap p (Unwrap x p)`.
* `unwrap_unwrap` -- adjacent unwraps merge: `unwrap (unwrap s p) q = unwrap s (p * q)`.
* `tailsUnion_union`, `iterC_union` -- the distribution laws.
* `iterC_one`, `tailsUnion_one` -- the `ε` cases.  A `{ε}` source has **no heads**, so it
  iterates to `Empty`; branch `b` records this as the case its prover caught.

## A note on totality

`tailsInter` folds over a *nonempty* head set and returns `∅` otherwise.  It cannot be an
`Finset.inf` over the head set, because that would need a top element and a finite path space
has none.  Branch `b` resolves this the same way, by seeding the fold with the first head.
-/

namespace Mettapedia.OSLF.PathMap.PathAlgebra

open FinLang

variable {α : Type*} [DecidableEq α]

namespace Zippy

/-! ## Prefix dropping -/

/-- Total prefix drop: remove the first `|p|` items of `x`.  Meaningful when `p` is a prefix
of `x`; `mul_dropPrefix` is the statement that it inverts `p * ·` there. -/
def dropPrefix (p x : FreeMonoid α) : FreeMonoid α :=
  FreeMonoid.ofList ((FreeMonoid.toList x).drop (FreeMonoid.toList p).length)

omit [DecidableEq α] in
@[simp]
theorem dropPrefix_mul (p y : FreeMonoid α) : dropPrefix p (p * y) = y :=
  List.drop_left

omit [DecidableEq α] in
/-- On a genuine prefix, `dropPrefix` is a right inverse to wrapping. -/
theorem mul_dropPrefix {p x : FreeMonoid α} (h : PathPrefix p x) : p * dropPrefix p x = x := by
  obtain ⟨r, hr⟩ := h
  show (FreeMonoid.toList p) ++ ((FreeMonoid.toList x).drop (FreeMonoid.toList p).length)
      = FreeMonoid.toList x
  rw [← hr, List.drop_left]

omit [DecidableEq α] in
@[simp]
theorem pathPrefix_mul (p y : FreeMonoid α) : PathPrefix p (p * y) := ⟨y, rfl⟩

omit [DecidableEq α] in
@[simp]
theorem pathPrefix_one (x : FreeMonoid α) : PathPrefix 1 x := List.nil_prefix

omit [DecidableEq α] in
@[simp]
theorem pathPrefix_refl (x : FreeMonoid α) : PathPrefix x x := List.prefix_rfl

/-! ## `Unwrap`

Branch `b`:
```text
(rewrite (Unwrap (Empty) p) (Empty))
(rewrite (Unwrap s (Eps)) s)
(rewrite (Unwrap (Wrap p s) p) s)
(rewrite (Unwrap (Wrap (Concat p q) s) p) (Wrap q s))
(rewrite (Unwrap (Wrap p s) (Concat p q)) (Unwrap s q))
(rewrite (Unwrap (Union s t) x) (Union (Unwrap s x) (Unwrap t x)))
(rewrite (Unwrap (Unwrap s p) q) (Unwrap s (Concat p q)))
```
-/

/-- `Unwrap s p` -- the paths of `s` lying under `p`, with `p` stripped.  Paths of `s` that do
not lie under `p` contribute nothing: this is the **partial** prefix stripping that branch `b`
adopted when it removed `Neg`. -/
def unwrap (s : FinLanguage α) (p : FreeMonoid α) : FinLanguage α :=
  (s.filter (fun x => PathPrefix p x)).image (dropPrefix p)

/-- The keystone characterisation.  Every `Unwrap` law below is an `ext` away from this. -/
@[simp]
theorem mem_unwrap {s : FinLanguage α} {p y : FreeMonoid α} :
    y ∈ unwrap s p ↔ p * y ∈ s := by
  constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    rw [Finset.mem_filter] at hx
    rw [mul_dropPrefix hx.2]
    exact hx.1
  · intro hy
    exact Finset.mem_image.mpr
      ⟨p * y, Finset.mem_filter.mpr ⟨hy, pathPrefix_mul p y⟩, dropPrefix_mul p y⟩

@[simp]
theorem unwrap_empty (p : FreeMonoid α) : unwrap (∅ : FinLanguage α) p = ∅ := by
  ext y; simp

@[simp]
theorem unwrap_eps (s : FinLanguage α) : unwrap s 1 = s := by
  ext y; simp

theorem unwrap_union (s t : FinLanguage α) (p : FreeMonoid α) :
    unwrap (s ∪ t) p = unwrap s p ∪ unwrap t p := by
  ext y; simp

/-- `Unwrap (Wrap p s) p = s`.  This is where cancellativity of the free monoid is used --
see `FreeMonoidBoundary.mul_left_cancel'`. -/
@[simp]
theorem unwrap_wrap (p : FreeMonoid α) (s : FinLanguage α) : unwrap (wrap p s) p = s := by
  ext y
  simp only [mem_unwrap, wrap, mem_mul, Finset.mem_singleton]
  constructor
  · rintro ⟨a, rfl, b, hb, hab⟩
    exact mul_left_cancel hab ▸ hb
  · intro hy
    exact ⟨p, rfl, y, hy, rfl⟩

/-- Adjacent unwraps merge (`formal.egg` branch `b`, `law_unwrap_merge.smt2`). -/
theorem unwrap_unwrap (s : FinLanguage α) (p q : FreeMonoid α) :
    unwrap (unwrap s p) q = unwrap s (p * q) := by
  ext y; simp [_root_.mul_assoc]

/-- Wrapping by a concatenation is wrapping twice. -/
theorem wrap_wrap (p q : FreeMonoid α) (s : FinLanguage α) :
    wrap (p * q) s = wrap p (wrap q s) := by
  unfold wrap
  rw [← FinLang.mul_assoc]
  congr 1

/-- `Unwrap (Wrap (Concat p q) s) p = Wrap q s`. -/
theorem unwrap_wrap_concat (p q : FreeMonoid α) (s : FinLanguage α) :
    unwrap (wrap (p * q) s) p = wrap q s := by
  rw [wrap_wrap, unwrap_wrap]

/-- `Unwrap (Wrap p s) (Concat p q) = Unwrap s q`. -/
theorem unwrap_wrap_concat' (p q : FreeMonoid α) (s : FinLanguage α) :
    unwrap (wrap p s) (p * q) = unwrap s q := by
  rw [← unwrap_unwrap, unwrap_wrap]

/-- Wrapping by one item and unwrapping by an incomparable item yields nothing. -/
theorem unwrap_wrap_of_ne {a b : α} (h : a ≠ b) (s : FinLanguage α) :
    unwrap (wrap (FreeMonoid.of a) s) (FreeMonoid.of b) = ∅ := by
  ext y
  simp only [mem_unwrap, wrap, mem_mul, Finset.mem_singleton, Finset.notMem_empty, iff_false,
    not_exists, not_and]
  rintro c rfl d _ hcd
  have hp := congrArg pathHead hcd
  rw [pathHead_of_mul, pathHead_of_mul] at hp
  exact h (FreeMonoid.of_injective hp)

/-! ## `Restriction`, in branch `b`'s formulation

```text
(rewrite (Restriction (Empty) p) (Empty))
(rewrite (Restriction x (Empty)) (Empty))
(rewrite (Restriction x (Singleton (Eps))) x)
(rewrite (Restriction x (Union p q)) (Union (Restriction x p) (Restriction x q)))
(rewrite (Restriction x (Singleton p)) (Wrap p (Unwrap x p)))
(rewrite (Restriction x x) x)
```
-/

@[simp]
theorem restrict_empty_space (sel : FinLanguage α) : restrict (∅ : FinLanguage α) sel = ∅ := by
  ext z; simp [mem_restrict]

@[simp]
theorem restrict_empty_selector (x : FinLanguage α) : restrict x (∅ : FinLanguage α) = ∅ := by
  ext z; simp [mem_restrict, Allows]

/-- Restricting by `{ε}` keeps everything: the empty path is a prefix of every path. -/
@[simp]
theorem restrict_eps (x : FinLanguage α) :
    restrict x ({1} : Finset (FreeMonoid α)) = x := by
  ext z; simp [mem_restrict]

/-- Restriction distributes over the **selector** (branch `b`).  Complements `restrict_union`
in `ZippyLaws`, which distributes over the space. -/
theorem restrict_union_selector (x p q : FinLanguage α) :
    restrict x (p ∪ q) = restrict x p ∪ restrict x q := by
  ext z
  simp only [mem_restrict, Finset.mem_union, Allows, Finset.mem_union]
  constructor
  · rintro ⟨hz, w, hw | hw, hpre⟩
    · exact Or.inl ⟨hz, w, hw, hpre⟩
    · exact Or.inr ⟨hz, w, hw, hpre⟩
  · rintro (⟨hz, w, hw, hpre⟩ | ⟨hz, w, hw, hpre⟩)
    · exact ⟨hz, w, Or.inl hw, hpre⟩
    · exact ⟨hz, w, Or.inr hw, hpre⟩

/-- **`Restriction x (Singleton p) = Wrap p (Unwrap x p)`** -- branch `b`'s definition of
single-prefix restriction in terms of unwrap.  This is the law that makes the removal of `Neg`
workable: restriction is expressed through the *partial* unwrap. -/
theorem restrict_singleton_eq_wrap_unwrap (x : FinLanguage α) (p : FreeMonoid α) :
    restrict x ({p} : Finset (FreeMonoid α)) = wrap p (unwrap x p) := by
  ext z
  simp only [mem_restrict, allows_singleton, wrap, mem_mul, Finset.mem_singleton, mem_unwrap]
  constructor
  · rintro ⟨hz, hpre⟩
    exact ⟨p, rfl, dropPrefix p z, by rwa [mul_dropPrefix hpre], mul_dropPrefix hpre⟩
  · rintro ⟨a, rfl, b, hb, rfl⟩
    exact ⟨hb, pathPrefix_mul a b⟩

/-- Every path of `x` has itself as a prefix, so `x` restricted by itself is `x`. -/
@[simp]
theorem restrict_self (x : FinLanguage α) : restrict x x = x := by
  ext z
  simp only [mem_restrict, Allows]
  exact ⟨fun h => h.1, fun hz => ⟨hz, z, hz, pathPrefix_refl z⟩⟩

/-! ## `Raffination`

`(rewrite (Raffination x y) (Subtraction x (Restriction x y)))` -- definitional on branch `b`. -/

/-- `Raffination x y` -- the paths of `x` *not* selected by `y`. -/
def raffination (x y : FinLanguage α) : FinLanguage α := x \ restrict x y

/-- `Raffination x x = Empty`, the consequence branch `b` notes alongside the definition. -/
@[simp]
theorem raffination_self (x : FinLanguage α) : raffination x x = ∅ := by
  simp [raffination]

/-! ## `Head` membership -/

theorem mem_head_iff {s : FinLanguage α} {h : FreeMonoid α} :
    h ∈ head s ↔ ∃ x ∈ s, x ≠ 1 ∧ pathHead x = h := by
  simp only [head, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨x, ⟨hx, hne⟩, rfl⟩; exact ⟨x, hx, hne, rfl⟩
  · rintro ⟨x, hx, hne, rfl⟩; exact ⟨x, ⟨hx, hne⟩, rfl⟩

omit [DecidableEq α] in
/-- The head of a path is a prefix of it. -/
theorem pathHead_prefix (x : FreeMonoid α) : PathPrefix (pathHead x) x := by
  show FreeMonoid.toList (pathHead x) <+: FreeMonoid.toList x
  match hx : FreeMonoid.toList x with
  | [] => simp [pathHead, hx]
  | a :: t => simp [pathHead, hx]

omit [DecidableEq α] in
/-- A nonempty path's head is a single item. -/
theorem exists_of_pathHead {x : FreeMonoid α} (h : x ≠ 1) :
    ∃ a : α, pathHead x = FreeMonoid.of a := by
  match hx : FreeMonoid.toList x with
  | [] => exact absurd (by simpa using congrArg FreeMonoid.ofList hx) h
  | a :: t => exact ⟨a, by simp [pathHead, hx]⟩

/-- If no path of `s` begins with the item `a`, unwrapping by it yields nothing. -/
theorem unwrap_of_eq_empty_of_notMem_head {s : FinLanguage α} {a : α}
    (h : FreeMonoid.of a ∉ head s) : unwrap s (FreeMonoid.of a) = ∅ := by
  ext y
  simp only [mem_unwrap, Finset.notMem_empty, iff_false]
  intro hy
  exact h (mem_head_iff.mpr ⟨FreeMonoid.of a * y, hy, of_mul_ne_one a y, pathHead_of_mul a y⟩)

/-! ## `TailsUnion`

```text
(rewrite (TailsUnion (Empty)) (Empty))
(rewrite (TailsUnion (Singleton (Eps))) (Empty))
(rewrite (TailsUnion (Singleton (Item h))) (Singleton (Eps)))
(rewrite (TailsUnion (Singleton (Concat (Item h) t))) (Singleton t))
(rewrite (TailsUnion (Union s t)) (Union (TailsUnion s) (TailsUnion t)))
(rewrite (TailsUnion (Wrap (Item p) s)) s)
```
-/

/-- `TailsUnion s` -- the union of the tails of `s` over its heads. -/
def tailsUnion (s : FinLanguage α) : FinLanguage α :=
  (head s).biUnion (fun h => unwrap s h)

@[simp]
theorem tailsUnion_empty : tailsUnion (∅ : FinLanguage α) = ∅ := by
  simp [tailsUnion]

/-- A `{ε}` space has no heads, so its tail union is empty. -/
@[simp]
theorem tailsUnion_one : tailsUnion ({1} : Finset (FreeMonoid α)) = ∅ := by
  simp [tailsUnion]

theorem mem_tailsUnion {s : FinLanguage α} {y : FreeMonoid α} :
    y ∈ tailsUnion s ↔ ∃ h ∈ head s, h * y ∈ s := by
  simp [tailsUnion]

theorem tailsUnion_singleton_item (a : α) :
    tailsUnion ({FreeMonoid.of a} : Finset (FreeMonoid α)) = ({1} : Finset (FreeMonoid α)) := by
  ext y
  rw [mem_tailsUnion, head_singleton_item]
  simp

theorem tailsUnion_singleton_cons (a : α) (t : FreeMonoid α) :
    tailsUnion ({FreeMonoid.of a * t} : Finset (FreeMonoid α))
      = ({t} : Finset (FreeMonoid α)) := by
  ext y
  rw [mem_tailsUnion, head_singleton_cons]
  simp only [Finset.mem_singleton, exists_eq_left]
  constructor
  · intro hy; exact mul_left_cancel hy
  · rintro rfl; rfl

/-- Every head is a single item. -/
theorem exists_item_of_mem_head {s : FinLanguage α} {h : FreeMonoid α} (hh : h ∈ head s) :
    ∃ a : α, h = FreeMonoid.of a := by
  obtain ⟨x, _, hne, rfl⟩ := mem_head_iff.mp hh
  exact exists_of_pathHead hne

/-- A path beginning with `a` puts `a` in the head set. -/
theorem of_mem_head {t : FinLanguage α} {a : α} {y : FreeMonoid α}
    (hy : FreeMonoid.of a * y ∈ t) : FreeMonoid.of a ∈ head t :=
  mem_head_iff.mpr ⟨FreeMonoid.of a * y, hy, of_mul_ne_one a y, pathHead_of_mul a y⟩

/-- `TailsUnion` distributes over union.  The content is that a head is always a single item,
so a path landing in one summand contributes its head to *that* summand's head set. -/
theorem tailsUnion_union (s t : FinLanguage α) :
    tailsUnion (s ∪ t) = tailsUnion s ∪ tailsUnion t := by
  ext y
  simp only [mem_tailsUnion, Finset.mem_union, head_union]
  constructor
  · rintro ⟨h, hh, hy⟩
    obtain ⟨a, rfl⟩ : ∃ a : α, h = FreeMonoid.of a := by
      rcases hh with hh | hh
      · exact exists_item_of_mem_head hh
      · exact exists_item_of_mem_head hh
    rcases hy with hy | hy
    · exact Or.inl ⟨_, of_mem_head hy, hy⟩
    · exact Or.inr ⟨_, of_mem_head hy, hy⟩
  · rintro (⟨h, hh, hy⟩ | ⟨h, hh, hy⟩)
    · exact ⟨h, Or.inl hh, Or.inl hy⟩
    · exact ⟨h, Or.inr hh, Or.inr hy⟩

/-! ## `TailsIntersection`

Branch `b` folds this over `Head x`, seeded with the first head, precisely so that the empty
case is `Empty` rather than a top element -- which a finite path space does not have. -/

/-- `TailsIntersection s` -- the intersection of the tails of `s` over its heads, and `∅` when
there are no heads. -/
def tailsInter (s : FinLanguage α) : FinLanguage α :=
  if h : (head s).Nonempty then (head s).inf' h (fun k => unwrap s k) else ∅

@[simp]
theorem tailsInter_empty : tailsInter (∅ : FinLanguage α) = ∅ := by
  simp [tailsInter]

/-- The `ε` case: no heads, so the fold returns `Empty`. -/
@[simp]
theorem tailsInter_one : tailsInter ({1} : Finset (FreeMonoid α)) = ∅ := by
  simp [tailsInter]

/-- On a single head the fold is just that tail. -/
theorem tailsInter_of_head_singleton {s : FinLanguage α} {h : FreeMonoid α}
    (hs : head s = {h}) : tailsInter s = unwrap s h := by
  have hne : (head s).Nonempty := hs ▸ Finset.singleton_nonempty h
  rw [tailsInter, dif_pos hne]
  simp [hs]

theorem tailsInter_singleton_item (a : α) :
    tailsInter ({FreeMonoid.of a} : Finset (FreeMonoid α)) = ({1} : Finset (FreeMonoid α)) := by
  rw [tailsInter_of_head_singleton (head_singleton_item a)]
  ext y; simp

/-! ## `IterC`

The loop-invariant iteration model: the union of a body `b` over the heads of the source.  A
source with no heads iterates to `Empty` -- branch `b` records the `{ε}` case as the one its
prover caught, since the unguarded `(IterC (Singleton p) b) → b` is false at `p = ε`. -/

/-- `IterC src b` -- `b` if `src` has at least one head, `∅` otherwise. -/
def iterC (src b : FinLanguage α) : FinLanguage α :=
  if (head src).Nonempty then b else ∅

@[simp]
theorem iterC_empty (b : FinLanguage α) : iterC (∅ : FinLanguage α) b = ∅ := by
  simp [iterC]

/-- **The prover-caught case**: a `{ε}` source has no heads, so it iterates to `Empty`. -/
@[simp]
theorem iterC_one (b : FinLanguage α) : iterC ({1} : Finset (FreeMonoid α)) b = ∅ := by
  simp [iterC]

theorem iterC_singleton_item (a : α) (b : FinLanguage α) :
    iterC ({FreeMonoid.of a} : Finset (FreeMonoid α)) b = b := by
  rw [iterC, if_pos]
  rw [head_singleton_item a]
  exact Finset.singleton_nonempty _

theorem iterC_singleton_cons (a : α) (t : FreeMonoid α) (b : FinLanguage α) :
    iterC ({FreeMonoid.of a * t} : Finset (FreeMonoid α)) b = b := by
  rw [iterC, if_pos]
  rw [head_singleton_cons a t]
  exact Finset.singleton_nonempty _

/-- Source-union distributes, because the body is idempotent under union. -/
theorem iterC_union (s t b : FinLanguage α) :
    iterC (s ∪ t) b = iterC s b ∪ iterC t b := by
  simp only [iterC, head_union, Finset.union_nonempty]
  by_cases hs : (head s).Nonempty <;> by_cases ht : (head t).Nonempty <;>
    simp [hs, ht, Finset.union_idempotent]

/-! ## Singleton unwrap: the `drop-prefix` relation

Branch `b` implements `Unwrap` on a singleton by letterwise descent, with nine rules covering
the descend step and the miss cases.  The single characterisation below discharges all of
them: unwrapping a one-path space either yields the stripped path or nothing. -/

@[simp]
theorem mem_wrap {p : FreeMonoid α} {s : FinLanguage α} {z : FreeMonoid α} :
    z ∈ wrap p s ↔ ∃ y ∈ s, p * y = z := by
  simp [wrap, mem_mul]

/-- **The `drop-prefix` characterisation.**  Every one of branch `b`'s nine singleton-unwrap
rules is an instance of this. -/
theorem unwrap_singleton (w p : FreeMonoid α) :
    unwrap ({w} : FinLanguage α) p
      = if PathPrefix p w then ({dropPrefix p w} : Finset (FreeMonoid α)) else ∅ := by
  ext y
  by_cases h : PathPrefix p w
  · rw [if_pos h]
    simp only [mem_unwrap, Finset.mem_singleton]
    constructor
    · intro hy; rw [← hy, dropPrefix_mul]
    · rintro rfl; exact mul_dropPrefix h
  · rw [if_neg h]
    simp only [mem_unwrap, Finset.mem_singleton, Finset.notMem_empty, iff_false]
    intro hy
    exact h (hy ▸ pathPrefix_mul p y)

/-- Exact hit: unwrapping a path by itself leaves the empty path. -/
@[simp]
theorem unwrap_singleton_self (w : FreeMonoid α) :
    unwrap ({w} : FinLanguage α) w = ({1} : Finset (FreeMonoid α)) := by
  rw [unwrap_singleton, if_pos (pathPrefix_refl w)]
  congr 1
  exact mul_left_cancel (by rw [mul_dropPrefix (pathPrefix_refl w), _root_.mul_one])

/-- Descend step: a shared leading item cancels from both sides. -/
theorem unwrap_singleton_cons (a : α) (w p : FreeMonoid α) :
    unwrap ({FreeMonoid.of a * w} : FinLanguage α) (FreeMonoid.of a * p)
      = unwrap ({w} : FinLanguage α) p := by
  rw [← wrap_singleton (FreeMonoid.of a) w, unwrap_wrap_concat']

/-- Miss case: a one-item path cannot be unwrapped past the empty path. -/
@[simp]
theorem unwrap_one_of (a : α) :
    unwrap ({1} : FinLanguage α) (FreeMonoid.of a) = ∅ := by
  rw [unwrap_singleton, if_neg]
  intro h
  simp [PathPrefix] at h

/-- Miss case: disagreeing leading items. -/
theorem unwrap_singleton_cons_of_ne {a b : α} (h : a ≠ b) (w : FreeMonoid α) :
    unwrap ({FreeMonoid.of a * w} : FinLanguage α) (FreeMonoid.of b) = ∅ := by
  rw [← wrap_singleton (FreeMonoid.of a) w]
  exact unwrap_wrap_of_ne h _

/-! ## Singleton disequality

The semantic content behind branch `b`'s two `neg`-ruleset space rules.  The hypothesis
`p ≠ q` is stated explicitly, mirroring the `(!= p q)` guard.  The egg side additionally owes
the bridge from e-class disequality to word disequality, which `(saturate paths)` supplies --
a scheduling obligation, not a semantic one, and therefore not discharged here. -/

theorem inter_singleton_ne {p q : FreeMonoid α} (h : p ≠ q) :
    ({p} : FinLanguage α) ∩ {q} = ∅ := by
  ext z
  simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
  rintro rfl; exact h

theorem sdiff_singleton_ne {p q : FreeMonoid α} (h : p ≠ q) :
    ({p} : FinLanguage α) \ {q} = {p} := by
  ext z
  simp only [Finset.mem_sdiff, Finset.mem_singleton]
  exact ⟨fun hz => hz.1, fun hz => ⟨hz, by rw [hz]; exact h⟩⟩

/-! ## The right-comb decomposition

`Head`, `TailsUnion` and `IterC` all case-split a path as `Eps | Item h | Concat (Item h) t`.
On the Lean side `pathHead` is total, so no normal-form assumption is needed; this theorem is
the citable justification that the split is exhaustive. -/

omit [DecidableEq α] in
/-- Every path is either empty or uniquely `of a * t`. -/
theorem path_cases (x : FreeMonoid α) :
    x = 1 ∨ ∃ (a : α) (t : FreeMonoid α), x = FreeMonoid.of a * t := by
  match hx : FreeMonoid.toList x with
  | [] => exact Or.inl (by simpa using congrArg FreeMonoid.ofList hx)
  | a :: t => exact Or.inr ⟨a, FreeMonoid.ofList t, by simpa using congrArg FreeMonoid.ofList hx⟩

/-! ## `TailsUnion` and `Wrap` -/

/-- `TailsUnion (Wrap (Item p) s) = s`. -/
theorem tailsUnion_wrap (a : α) (s : FinLanguage α) :
    tailsUnion (wrap (FreeMonoid.of a) s) = s := by
  ext y
  rw [mem_tailsUnion]
  constructor
  · rintro ⟨h, hh, hy⟩
    obtain ⟨x, hx, hne, rfl⟩ := mem_head_iff.mp hh
    obtain ⟨z, hz, rfl⟩ := mem_wrap.mp hx
    rw [pathHead_of_mul] at hy
    exact (unwrap_wrap (FreeMonoid.of a) s ▸ mem_unwrap.mpr hy)
  · intro hy
    refine ⟨FreeMonoid.of a, ?_, ?_⟩
    · exact of_mem_head (mem_wrap.mpr ⟨y, hy, rfl⟩)
    · exact mem_wrap.mpr ⟨y, hy, rfl⟩

/-- The mixed form: `TailsUnion (Union (Wrap (Item p) s) t) = Union s (TailsUnion t)`. -/
theorem tailsUnion_wrap_union (a : α) (s t : FinLanguage α) :
    tailsUnion (wrap (FreeMonoid.of a) s ∪ t) = s ∪ tailsUnion t := by
  rw [tailsUnion_union, tailsUnion_wrap]

/-! ## `TailsIntersection`, characterised

Branch `b` computes this with a seeded accumulator fold over `Head x`.  Here it is a
`Finset.inf'`, so **order independence is automatic** rather than a proof obligation: the
fold's result is determined by the head *set*, and duplicate heads cannot arise.  The
membership characterisation below is the fold-correctness statement. -/

theorem mem_tailsInter {s : FinLanguage α} (hne : (head s).Nonempty) {y : FreeMonoid α} :
    y ∈ tailsInter s ↔ ∀ h ∈ head s, h * y ∈ s := by
  rw [tailsInter, dif_pos hne]
  constructor
  · intro hy h hh
    exact mem_unwrap.mp (Finset.le_iff_subset.mp (Finset.inf'_le _ hh) hy)
  · intro hy
    have hsub : ({y} : Finset (FreeMonoid α))
        ≤ Finset.inf' (head s) hne (fun k => unwrap s k) :=
      Finset.le_inf' hne _ (fun b hb => Finset.singleton_subset_iff.mpr (mem_unwrap.mpr (hy b hb)))
    exact Finset.singleton_subset_iff.mp hsub

/-- On a wrapped nonempty space the tail intersection is the whole space. -/
theorem tailsInter_wrap (a : α) {s : FinLanguage α} (hs : s.Nonempty) :
    tailsInter (wrap (FreeMonoid.of a) s) = s := by
  obtain ⟨w, hw⟩ := hs
  have hhead : (head (wrap (FreeMonoid.of a) s)).Nonempty :=
    ⟨FreeMonoid.of a, of_mem_head (mem_wrap.mpr ⟨w, hw, rfl⟩)⟩
  ext y
  rw [mem_tailsInter hhead]
  constructor
  · intro hy
    have := hy (FreeMonoid.of a) (of_mem_head (mem_wrap.mpr ⟨w, hw, rfl⟩))
    exact unwrap_wrap (FreeMonoid.of a) s ▸ mem_unwrap.mpr this
  · intro hy h hh
    obtain ⟨x, hx, hne, rfl⟩ := mem_head_iff.mp hh
    obtain ⟨z, _, rfl⟩ := mem_wrap.mp hx
    rw [pathHead_of_mul]
    exact mem_wrap.mpr ⟨y, hy, rfl⟩

/-! ## The membership judgment (`ElemP` / `EB`)

Branch `b` adds a two-valued membership flag algebra.  The structural rules are the
`Bool`-valued reading of `Finset` membership; the `EOr`/`EAnd`/`EAndNot` truth tables are then
the ordinary `Bool` identities.  `EAndNot x y` is pinned to `x && !y` by the `Subtraction`
rule, which is what fixes its intended reading. -/

/-- `ElemP p s` -- the decidable membership flag. -/
def elem (p : FreeMonoid α) (s : FinLanguage α) : Bool := decide (p ∈ s)

@[simp] theorem elem_empty (p : FreeMonoid α) : elem p (∅ : FinLanguage α) = false := by
  simp [elem]

@[simp] theorem elem_singleton (p q : FreeMonoid α) :
    elem p ({q} : FinLanguage α) = decide (p = q) := by simp [elem]

@[simp] theorem elem_union (p : FreeMonoid α) (s t : FinLanguage α) :
    elem p (s ∪ t) = (elem p s || elem p t) := by simp [elem]

@[simp] theorem elem_inter (p : FreeMonoid α) (s t : FinLanguage α) :
    elem p (s ∩ t) = (elem p s && elem p t) := by simp [elem]

/-- This is the rule that pins `EAndNot` to `x && !y`. -/
@[simp] theorem elem_sdiff (p : FreeMonoid α) (s t : FinLanguage α) :
    elem p (s \ t) = (elem p s && !elem p t) := by simp [elem]


end Zippy

end Mettapedia.OSLF.PathMap.PathAlgebra
