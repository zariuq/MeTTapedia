import Mettapedia.OSLF.PathMap.PathAlgebra.FinLanguage
import Mettapedia.OSLF.PathMap.PathPrefixRestrictRefinement

/-!
# Zippy's path-algebra laws, checked against the finite-language semantics

Adam Vandervorst's Zippy presents a path/space algebra together with an equational theory
(`formal.egg`, 29 rewrites) used for equality saturation.  This module states those laws as
theorems about the finite-language model of `FinLanguage`, so the optimizer's rewrites are
backed by a semantics rather than by test cases alone.

## The `Neg` boundary -- a divergence `master` had and branch `b` removed

Zippy's README describes paths as words in a **free monoid**.  The `formal.egg` on `master`
nevertheless declares a formal inverse

```text
(datatype Path (Eps) (Item String) (Concat Path Path) (Neg Path))
(rewrite (Concat (Neg x) x) (Eps))
(rewrite (Unwrap (Singleton p) x) (Singleton (Concat (Neg x) p)))
```

which makes paths a **group**, and defines `Unwrap` through that inverse.  Those three rules
are not theorems of the free-monoid model and are deliberately absent below:
`FreeMonoidBoundary.no_right_inverse` shows the free monoid on an inhabited alphabet is not a
group, and `FreeMonoidBoundary.unwrapPath_partial` exhibits the partiality a formal inverse
exists to hide.

**Branch `b` removes `Neg`**: `Path` is a plain free monoid there and `Unwrap` is defined
case-wise, yielding `Empty` on a prefix mismatch -- exactly the partial operation proved in
`FreeMonoidBoundary`.  The removal is what makes branch `b`'s
`Restriction x (Singleton p) = Wrap p (Unwrap x p)` correct; under `master`'s totalisation it
is false.  See `PathSpaceOps.lean`, which formalises the current theory.

## Scope

The laws below cover the semiring-expressible core of the theory: the lattice rules,
concatenation, `Wrap`, `Product`, `Head`, and prefix `Restriction`.

`Restriction` is defined here **once**, over an arbitrary alphabet, and
`restrict_eq_restrictPaths` proves that the byte-level `restrictPaths` of
`Mettapedia/OSLF/PathMap/PathPrefixRestrictRefinement.lean` is exactly its `α = UInt8`
instance, so the generic form is a strict generalisation rather than a parallel definition.
(That file proves `restrictPaths_mem_iff`, monotonicity and the root/empty-selector cases; it
does NOT prove a uniqueness theorem.)

## Two refuted rewrites

Zippy's `formal.egg:99` and `:101` drop a union summand outright:

```text
(rewrite (Restriction (Union (Wrap p s) t) (Singleton p))            (Wrap p s))
(rewrite (Restriction (Union (Wrap p s) t) (Union (Singleton p) r))  (Wrap p s))
```

Both are **unsound as written** -- any path of `t` that also lies under `p` survives the
restriction, so the left side can be strictly larger.  `ZippyRefutation` proves each false
by an explicit `decide`-checked counterexample; neither is inferred from the other.

`restrict_union_singleton_iff` and `restrict_union_union_selector_iff` give the corrected
rules as **exact characterisations** (the side condition is necessary as well as sufficient),
and `restrict_union_singleton_of_prefixFree` specialises to the trie invariant -- distinct
children -- under which the original rewrites hold verbatim.  The underlying law they were
reaching for is `restrict_union`: restriction distributes over union.

## References

* `repos/Zippy/formal.egg` -- the 29-rewrite equational theory checked here.
* `repos/Zippy/README.md` -- the free-monoid/idempotent-semiring prose.
-/

namespace Mettapedia.OSLF.PathMap.PathAlgebra

open FinLang

variable {α : Type*} [DecidableEq α]

namespace Zippy

/-! ## Space operations, in Zippy's vocabulary -/

/-- `Wrap p s` -- tag every path in `s` with the prefix `p`. -/
def wrap (p : FreeMonoid α) (s : FinLanguage α) : FinLanguage α := mul {p} s

/-- `Product s t` -- the path product; this *is* the semiring multiplication. -/
def product (s t : FinLanguage α) : FinLanguage α := mul s t

/-- The first item of a path (the empty path is its own head). -/
def pathHead (p : FreeMonoid α) : FreeMonoid α :=
  match FreeMonoid.toList p with
  | [] => 1
  | a :: _ => FreeMonoid.of a

/-- `Head s` -- the space of first items.  The **empty path has no head**, so it is filtered
out rather than mapped to itself: branch `b` of Zippy states this as
`(rewrite (Head (Singleton (Eps))) (Empty))`, and `TailsUnion`/`IterC` depend on it (a `{ε}`
source has no heads, hence iterates to `Empty`). -/
def head (s : FinLanguage α) : FinLanguage α :=
  (s.filter (fun p => p ≠ 1)).image pathHead

/-! ## Lattice rules

`(rewrite (Union x x) x)`, `(rewrite (Intersection x x) x)`,
`(rewrite (Subtraction x x) (Empty))`, the two commutativity rules, and the two
`birewrite` associativity rules. -/

theorem union_idem (s : FinLanguage α) : s ∪ s = s := Finset.union_idempotent s

theorem inter_idem (s : FinLanguage α) : s ∩ s = s := Finset.inter_self s

theorem sdiff_self (s : FinLanguage α) : s \ s = (∅ : Finset (FreeMonoid α)) :=
  Finset.sdiff_self s

theorem union_comm (s t : FinLanguage α) : s ∪ t = t ∪ s := Finset.union_comm s t

theorem inter_comm (s t : FinLanguage α) : s ∩ t = t ∩ s := Finset.inter_comm s t

theorem union_assoc (s t u : FinLanguage α) : (s ∪ t) ∪ u = s ∪ (t ∪ u) :=
  Finset.union_assoc s t u

theorem inter_assoc (s t u : FinLanguage α) : (s ∩ t) ∩ u = s ∩ (t ∩ u) :=
  Finset.inter_assoc s t u

/-! ## Concatenation rules

`(rewrite (Concat x (Eps)) x)`, `(rewrite (Concat (Eps) x) x)`, and the `birewrite`
associativity of `Concat`, lifted to spaces. -/

theorem eps_mul (s : FinLanguage α) : mul one s = s := FinLang.one_mul s

theorem mul_eps (s : FinLanguage α) : mul s one = s := FinLang.mul_one s

theorem mul_assoc' (s t u : FinLanguage α) : mul (mul s t) u = mul s (mul t u) :=
  FinLang.mul_assoc s t u

/-! ## `Wrap` rules

`(birewrite (Wrap x (Singleton p)) (Singleton (Concat x p)))` and
`(birewrite (Wrap x (Union s t)) (Union (Wrap x s) (Wrap x t)))`. -/

theorem wrap_singleton (p q : FreeMonoid α) :
    wrap p ({q} : Finset (FreeMonoid α)) = ({p * q} : Finset (FreeMonoid α)) := by
  simp [wrap, mul]

theorem wrap_union (p : FreeMonoid α) (s t : FinLanguage α) :
    wrap p (s ∪ t) = wrap p s ∪ wrap p t := FinLang.left_distrib _ _ _

/-- Wrapping by the empty path is the identity. -/
theorem wrap_one (s : FinLanguage α) : wrap (1 : FreeMonoid α) s = s := FinLang.one_mul s

/-! ## `Product` rules

`(rewrite (Product (Singleton p) t) (Wrap p t))` and
`(rewrite (Product (Union (Singleton p) s) t) (Union (Wrap p t) (Product s t)))`. -/

theorem product_singleton (p : FreeMonoid α) (t : FinLanguage α) :
    product ({p} : Finset (FreeMonoid α)) t = wrap p t := rfl

theorem product_union_singleton (p : FreeMonoid α) (s t : FinLanguage α) :
    product (({p} : Finset (FreeMonoid α)) ∪ s) t = wrap p t ∪ product s t :=
  FinLang.right_distrib _ _ _

theorem product_union_right (s t u : FinLanguage α) :
    product s (t ∪ u) = product s t ∪ product s u := FinLang.left_distrib _ _ _

/-! ## `Head` rules

`(rewrite (Head (Union x y)) (Union (Head x) (Head y)))`,
`(rewrite (Head (Singleton (Concat (Item h) t))) (Singleton (Item h)))`, and
`(rewrite (Head (Singleton (Item h))) (Singleton (Item h)))`. -/

theorem head_union (s t : FinLanguage α) : head (s ∪ t) = head s ∪ head t := by
  simp [head, Finset.filter_union, Finset.image_union]

@[simp]
theorem head_empty : head (∅ : FinLanguage α) = ∅ := by simp [head]

/-- The empty path contributes no head. -/
@[simp]
theorem head_one : head ({1} : Finset (FreeMonoid α)) = ∅ := by simp [head]

theorem head_singleton_of_ne_one {p : FreeMonoid α} (h : p ≠ 1) :
    head ({p} : Finset (FreeMonoid α)) = ({pathHead p} : Finset (FreeMonoid α)) := by
  rw [head, Finset.filter_singleton, if_pos h, Finset.image_singleton]

omit [DecidableEq α] in
/-- A path beginning with an item is not the empty path. -/
theorem of_mul_ne_one (a : α) (t : FreeMonoid α) : FreeMonoid.of a * t ≠ 1 := by
  intro h
  have hlen : (FreeMonoid.of a * t).length = 0 := by
    rw [h]; exact FreeMonoid.length_one
  rw [FreeMonoid.length_mul, FreeMonoid.length_of] at hlen
  omega

omit [DecidableEq α] in
@[simp]
theorem pathHead_of (a : α) : pathHead (FreeMonoid.of a) = FreeMonoid.of a := rfl

omit [DecidableEq α] in
@[simp]
theorem pathHead_of_mul (a : α) (t : FreeMonoid α) :
    pathHead (FreeMonoid.of a * t) = FreeMonoid.of a := rfl

/-- `Head` of a one-item space is that space. -/
theorem head_singleton_item (a : α) :
    head ({FreeMonoid.of a} : Finset (FreeMonoid α))
      = ({FreeMonoid.of a} : Finset (FreeMonoid α)) := by
  rw [head_singleton_of_ne_one (by simp), pathHead_of]

/-- `Head` of a space of one prefixed path is the prefix item. -/
theorem head_singleton_cons (a : α) (t : FreeMonoid α) :
    head ({FreeMonoid.of a * t} : Finset (FreeMonoid α))
      = ({FreeMonoid.of a} : Finset (FreeMonoid α)) := by
  rw [head_singleton_of_ne_one (of_mul_ne_one a t), pathHead_of_mul]

/-! ## `Restriction`

Prefix restriction, generalised.  This tree already formalises restriction extensionally at
the byte level (`PathPrefixRestrictRefinement.lean`); the
definitions below are the same operation over an arbitrary alphabet, so that byte paths are
recovered as the `α = UInt8` instance.  `pathPrefix_iff_isPrefix` is the bridge: prefixhood
in the free monoid is exactly `List.IsPrefix`, because both unfold to `∃ r, q ++ r = p`. -/

/-- `q` is a prefix of `p`, stated in the free monoid. -/
def PathPrefix (q p : FreeMonoid α) : Prop :=
  FreeMonoid.toList q <+: FreeMonoid.toList p

instance decidablePathPrefix (q p : FreeMonoid α) : Decidable (PathPrefix q p) :=
  inferInstanceAs (Decidable (FreeMonoid.toList q <+: FreeMonoid.toList p))

omit [DecidableEq α] in
/-- Prefixhood in the free monoid is exactly divisibility on the left: this is the bridge to
`List.IsPrefix`, and hence to the byte-level `Mettapedia.PathMap.PathPrefix`. -/
theorem pathPrefix_iff_isPrefix (q p : FreeMonoid α) :
    PathPrefix q p ↔ ∃ r : FreeMonoid α, q * r = p := Iff.rfl

/-- A selector admits a path iff one of its paths is a prefix of it. -/
def Allows (sel : FinLanguage α) (p : FreeMonoid α) : Prop :=
  ∃ q ∈ sel, PathPrefix q p

instance decidableAllows (sel : FinLanguage α) (p : FreeMonoid α) :
    Decidable (Allows sel p) :=
  inferInstanceAs (Decidable (∃ q ∈ sel, PathPrefix q p))

/-- `Restriction s sel` -- keep exactly the paths of `s` admitted by the selector. -/
def restrict (s sel : FinLanguage α) : FinLanguage α := s.filter (fun p => Allows sel p)

@[simp]
theorem mem_restrict {s sel : FinLanguage α} {p : FreeMonoid α} :
    p ∈ restrict s sel ↔ p ∈ s ∧ Allows sel p := by
  simp [restrict]

omit [DecidableEq α] in
/-- Every wrapped path is admitted by its own prefix. -/
theorem allows_self_wrap (p : FreeMonoid α) (x : FreeMonoid α) :
    Allows ({p} : Finset (FreeMonoid α)) (p * x) :=
  ⟨p, Finset.mem_singleton_self p, ⟨x, rfl⟩⟩

/-- **Sound.** `(rewrite (Restriction (Wrap p s) (Singleton p)) (Wrap p s))`: restricting a
wrapped space by its own tag keeps everything. -/
theorem restrict_wrap_singleton (p : FreeMonoid α) (s : FinLanguage α) :
    restrict (wrap p s) ({p} : Finset (FreeMonoid α)) = wrap p s := by
  apply Finset.filter_true_of_mem
  intro x hx
  rw [wrap, mul] at hx
  rcases Finset.mem_image₂.mp hx with ⟨a, ha, b, hb, rfl⟩
  rw [Finset.mem_singleton.mp ha]
  exact allows_self_wrap p b

/-- **Sound.** `(rewrite (Restriction (Wrap p s) (Union (Singleton p) r)) (Wrap p s))`:
enlarging the selector cannot drop admitted paths. -/
theorem restrict_wrap_union_selector (p : FreeMonoid α) (s r : FinLanguage α) :
    restrict (wrap p s) (({p} : Finset (FreeMonoid α)) ∪ r) = wrap p s := by
  apply Finset.filter_true_of_mem
  intro x hx
  rw [wrap, mul] at hx
  rcases Finset.mem_image₂.mp hx with ⟨a, ha, b, hb, rfl⟩
  rw [Finset.mem_singleton.mp ha]
  rcases allows_self_wrap p b with ⟨q, hq, hpre⟩
  exact ⟨q, Finset.mem_union_left _ hq, hpre⟩

/-! ### Restriction is additive, and the corrected drop rules

`restrict · sel` keeps each path independently, so it distributes over union.  That is the
law the two unsound Zippy rules are reaching for, and it makes the exact side condition
visible: dropping a summand `t` is legitimate precisely when `t` contributes nothing beyond
what is already kept. -/

omit [DecidableEq α] in
@[simp]
theorem allows_singleton (p x : FreeMonoid α) :
    Allows ({p} : Finset (FreeMonoid α)) x ↔ PathPrefix p x := by
  simp [Allows]

/-- Restriction distributes over union: `restrict · sel` is additive. -/
theorem restrict_union (s t sel : FinLanguage α) :
    restrict (s ∪ t) sel = restrict s sel ∪ restrict t sel :=
  Finset.filter_union _ _ _

/-- A space all of whose paths are admitted is kept entire. -/
theorem restrict_eq_self {s sel : FinLanguage α} (h : ∀ x ∈ s, Allows sel x) :
    restrict s sel = s :=
  Finset.filter_true_of_mem h

/-- A space none of whose paths are admitted is erased. -/
theorem restrict_eq_empty {s sel : FinLanguage α} (h : ∀ x ∈ s, ¬ Allows sel x) :
    restrict s sel = ∅ :=
  Finset.filter_false_of_mem h

/-- **Corrected form of the unsound rule at `formal.egg:99`**, as an exact characterisation:
the summand `t` may be dropped **iff** every path of `t` lying under `p` was already in
`Wrap p s`.  Necessity is the content the original rewrite is missing. -/
theorem restrict_union_singleton_iff (p : FreeMonoid α) (s t : FinLanguage α) :
    restrict (wrap p s ∪ t) ({p} : Finset (FreeMonoid α)) = wrap p s
      ↔ ∀ x ∈ t, PathPrefix p x → x ∈ wrap p s := by
  rw [restrict_union, restrict_wrap_singleton, Finset.union_eq_left]
  constructor
  · intro h x hx hpre
    exact h (mem_restrict.mpr ⟨hx, (allows_singleton p x).mpr hpre⟩)
  · intro h x hx
    rw [mem_restrict, allows_singleton] at hx
    exact h x hx.1 hx.2

/-- **Corrected form of the unsound rule at `formal.egg:101`**, likewise exact: with the
larger selector the side condition is stated against admission by the whole selector. -/
theorem restrict_union_union_selector_iff (p : FreeMonoid α) (s t r : FinLanguage α) :
    restrict (wrap p s ∪ t) (({p} : Finset (FreeMonoid α)) ∪ r) = wrap p s
      ↔ ∀ x ∈ t, Allows (({p} : Finset (FreeMonoid α)) ∪ r) x → x ∈ wrap p s := by
  rw [restrict_union, restrict_wrap_union_selector, Finset.union_eq_left]
  constructor
  · intro h x hx hal
    exact h (mem_restrict.mpr ⟨hx, hal⟩)
  · intro h x hx
    rw [mem_restrict] at hx
    exact h x hx.1 hx.2

/-- `t` lies entirely outside the cone under `p`.  This is the trie invariant -- distinct
children -- under which the original rewrite is sound. -/
def PrefixFreeOf (p : FreeMonoid α) (t : FinLanguage α) : Prop :=
  ∀ x ∈ t, ¬ PathPrefix p x

/-- The trie-invariant corollary: under `PrefixFreeOf`, Zippy's rule at `formal.egg:99` is
sound exactly as written. -/
theorem restrict_union_singleton_of_prefixFree (p : FreeMonoid α) (s t : FinLanguage α)
    (h : PrefixFreeOf p t) :
    restrict (wrap p s ∪ t) ({p} : Finset (FreeMonoid α)) = wrap p s :=
  (restrict_union_singleton_iff p s t).mpr (fun x hx hpre => absurd hpre (h x hx))

/-! ### Bridge to the byte-level restriction

`PathPrefixRestrictRefinement.lean` fixes the intended meaning of PathMap's `restrict` on
byte paths.  The theorems below show that the
generic `restrict` above **is** that operation at `α = UInt8`, rather than a parallel
definition of the same idea: byte paths are the free monoid on `UInt8`, and the two admission
predicates coincide.  Everything proven of `restrictPaths` therefore transfers to the generic
form, and the Zippy laws above apply to byte paths. -/

/-- Admission agrees with the byte-level `Allows`. -/
theorem allows_iff_bytes (sel : Finset (FreeMonoid UInt8)) (p : FreeMonoid UInt8) :
    Allows sel p ↔ Mettapedia.PathMap.Allows sel p := Iff.rfl

/-- The generic prefix restriction **is** the byte-level `restrictPaths`.  The two differ only
by which `Decidable` instance computes the filter. -/
theorem restrict_eq_restrictPaths (s sel : Finset (FreeMonoid UInt8)) :
    restrict s sel = Mettapedia.PathMap.restrictPaths s sel := by
  ext p
  exact mem_restrict.trans Mettapedia.PathMap.restrictPaths_mem_iff.symm

/-! ## Completing the Boolean-algebra rules

Branch `b` cites a certificate for each of these; they are `Finset` one-liners here. -/

@[simp] theorem inter_empty (s : FinLanguage α) : s ∩ (∅ : FinLanguage α) = ∅ :=
  Finset.inter_empty s

@[simp] theorem empty_inter (s : FinLanguage α) : (∅ : FinLanguage α) ∩ s = ∅ :=
  Finset.empty_inter s

@[simp] theorem sdiff_empty (s : FinLanguage α) : s \ (∅ : FinLanguage α) = s :=
  Finset.sdiff_empty

@[simp] theorem empty_sdiff (s : FinLanguage α) : (∅ : FinLanguage α) \ s = ∅ :=
  Finset.empty_sdiff s

theorem inter_union_distrib_left (s t u : FinLanguage α) :
    s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := Finset.inter_union_distrib_left s t u

theorem inter_union_distrib_right (s t u : FinLanguage α) :
    (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) := Finset.union_inter_distrib_right s t u

theorem union_sdiff_distrib (s t u : FinLanguage α) :
    (s ∪ t) \ u = (s \ u) ∪ (t \ u) := Finset.union_sdiff_distrib s t u

/-- The De Morgan form: subtracting a union is subtracting in sequence. -/
theorem sdiff_union_eq_sdiff_sdiff (s t u : FinLanguage α) :
    s \ (t ∪ u) = (s \ t) \ u := by
  ext z
  simp only [Finset.mem_sdiff, Finset.mem_union, not_or, and_assoc]

end Zippy

/-! ## A second refuted rewrite

`sdiff_union_eq_sdiff_sdiff` has a tempting sibling that is **false**:
`x \ (y ∪ z) = (x \ y) ∪ (x \ z)`.  Subtracting a union removes *more*, so the union form is
strictly larger whenever `y` and `z` remove different elements.  Recorded here in the same
style as the `Restriction` refutations, so the correct orientation is not guessed at. -/

namespace SdiffRefutation

open Zippy

/-- Alphabet for the counterexample. -/
abbrev A : Type := Bool

def pa : FreeMonoid A := FreeMonoid.of true
def pb : FreeMonoid A := FreeMonoid.of false

/-- `{a,b} \ ({a} ∪ {b}) = ∅`, but `({a,b} \ {a}) ∪ ({a,b} \ {b}) = {a,b}`. -/
theorem sdiff_union_distrib_unsound :
    ({pa, pb} : Finset (FreeMonoid A)) \ ({pa} ∪ {pb})
      ≠ (({pa, pb} : Finset (FreeMonoid A)) \ {pa}) ∪ (({pa, pb} : Finset (FreeMonoid A)) \ {pb}) := by
  decide

end SdiffRefutation


/-! ## A refuted rewrite

Two of Zippy's four `Restriction` rules discard the second summand outright:

```text
(rewrite (Restriction (Union (Wrap p s) t) (Singleton p))        (Wrap p s))
(rewrite (Restriction (Union (Wrap p s) t) (Union (Singleton p) r)) (Wrap p s))
```

They are **unsound without a side condition**: any path of `t` that also carries `p` as a
prefix survives the restriction, so the left side can be strictly larger than the right.
The counterexample below is minimal -- one letter, `s = 1`, and `t` a single path extending
`p` -- and is checked by `decide`.

The rules become sound with the side condition *"no path of `t` has `p` as a prefix"*, which
is exactly the situation in a trie whose children are distinct; the egglog rules read as if
that structural invariant were globally available. -/

namespace ZippyRefutation

open Zippy

/-- Alphabet for the counterexample. -/
abbrev A : Type := Bool

/-- The tag `p`. -/
def p : FreeMonoid A := FreeMonoid.of true

/-- `Wrap p 1 = {p}`. -/
def lhsWrapped : FinLanguage A := ({p} : Finset (FreeMonoid A))

/-- A path in the *other* summand that also begins with `p`. -/
def extra : FreeMonoid A := FreeMonoid.of true * FreeMonoid.of true

/-- The refutation: restricting `{p} ∪ {p·p}` by the selector `{p}` retains `p·p`, so it is
**not** equal to `Wrap p 1`. -/
theorem restrict_union_drop_unsound :
    restrict (lhsWrapped ∪ ({extra} : Finset (FreeMonoid A)))
        ({p} : Finset (FreeMonoid A))
      ≠ lhsWrapped := by
  decide

/-- The same refutation for the larger-selector variant (`formal.egg:101`), taking `r = ∅`.
Proven, not inferred from the previous theorem by analogy. -/
theorem restrict_union_drop_unsound_union_selector :
    restrict (lhsWrapped ∪ ({extra} : Finset (FreeMonoid A)))
        (({p} : Finset (FreeMonoid A)) ∪ (∅ : Finset (FreeMonoid A)))
      ≠ lhsWrapped := by
  decide

end ZippyRefutation

end Mettapedia.OSLF.PathMap.PathAlgebra
