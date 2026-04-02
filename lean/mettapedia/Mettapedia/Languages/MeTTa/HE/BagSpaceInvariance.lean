import Mettapedia.Languages.MeTTa.HE.BagSupportBridge
import Mettapedia.Languages.MeTTa.HE.Space

/-!
# Bag-Space Invariance

Proves that key Space operations are permutation-invariant, making the
`List`-based Space a faithful representative of semantic `Multiset`.

## Key Results

- `filterMap_perm` — filterMap preserves permutations
- `getAnnotatedTypes_perm` — type annotation queries are perm-invariant
- `Space.BagEquiv` — equivalence relation for bag-equivalent spaces
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## §1: Structural lemmas -/

/-- `filterMap` preserves permutations. -/
theorem filterMap_perm {α β : Type*}
    (f : α → Option β) {l₁ l₂ : List α} (h : l₁.Perm l₂) :
    (l₁.filterMap f).Perm (l₂.filterMap f) := by
  induction h with
  | nil => exact List.Perm.nil
  | cons x _ ih =>
    simp only [List.filterMap_cons]
    cases f x with
    | none => exact ih
    | some b => exact ih.cons b
  | swap x y l =>
    simp only [List.filterMap_cons]
    cases f x <;> cases f y <;>
      first | exact List.Perm.refl _ | exact List.Perm.swap ..
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## §2: Type queries are permutation-invariant -/

/-- `getAnnotatedTypes` is permutation-invariant: permuting the space's
    atoms permutes the type results. -/
theorem getAnnotatedTypes_perm (a : Atom) {s₁ s₂ : Space}
    (h : s₁.atoms.Perm s₂.atoms) :
    (getAnnotatedTypes s₁ a).Perm (getAnnotatedTypes s₂ a) :=
  filterMap_perm _ h

/-- Permutation-invariance at the support level: bag-equivalent spaces
    produce the same set of type annotations (Finset). -/
theorem getAnnotatedTypes_support (a : Atom) {s₁ s₂ : Space}
    (h : s₁.atoms.Perm s₂.atoms) :
    (getAnnotatedTypes s₁ a).toFinset = (getAnnotatedTypes s₂ a).toFinset := by
  ext x; simp only [List.mem_toFinset]; exact (getAnnotatedTypes_perm a h).mem_iff

/-! ## §3: Space bag equivalence -/

/-- Two spaces are **bag-equivalent** when their atom lists are permutations.
    This is the correct semantic equality for `SPACE_KIND_ATOM` spaces. -/
def Space.BagEquiv (s₁ s₂ : Space) : Prop := s₁.atoms.Perm s₂.atoms

theorem Space.bagEquiv_refl (s : Space) : s.BagEquiv s := List.Perm.refl _

theorem Space.bagEquiv_symm {s₁ s₂ : Space} (h : s₁.BagEquiv s₂) :
    s₂.BagEquiv s₁ := List.Perm.symm h

theorem Space.bagEquiv_trans {s₁ s₂ s₃ : Space}
    (h₁ : s₁.BagEquiv s₂) (h₂ : s₂.BagEquiv s₃) : s₁.BagEquiv s₃ :=
  List.Perm.trans h₁ h₂

/-- Bag-equivalent spaces give permutation-equivalent type annotations. -/
theorem Space.BagEquiv.annotatedTypes_perm {s₁ s₂ : Space}
    (h : s₁.BagEquiv s₂) (a : Atom) :
    (getAnnotatedTypes s₁ a).Perm (getAnnotatedTypes s₂ a) :=
  getAnnotatedTypes_perm a h

/-- Bag-equivalent spaces give the same type annotation support (Finset). -/
theorem Space.BagEquiv.annotatedTypes_support {s₁ s₂ : Space}
    (h : s₁.BagEquiv s₂) (a : Atom) :
    (getAnnotatedTypes s₁ a).toFinset = (getAnnotatedTypes s₂ a).toFinset :=
  getAnnotatedTypes_support a h

/-! ## §4: Interpretation

### What's proved

- **`filterMap_perm`**: the structural workhorse. Any operation built as
  `space.atoms.filterMap f` is permutation-invariant. This covers
  `getAnnotatedTypes`, and will cover future space operations.

- **`getAnnotatedTypes_{perm,support}`**: type annotation queries are
  fully permutation-invariant at both bag and support levels.

- **`Space.BagEquiv`**: an equivalence relation making "space = multiset"
  formal. Reflexive, symmetric, transitive.

### The queryEquations gap (honest)

`queryEquations` uses `zipIdx` for fresh variable naming. Permuting atoms
changes indices → changes fresh names → changes Bindings letter-for-letter.
At the **support level** (Finset of RHS atoms), this doesn't matter.
At the **bag level**, full invariance needs alpha-equivalence on Bindings.

### Connection to Fujita/Smarandache

`filterMap_perm` is the concrete proof that `filterMap` (a hyperoperation
component) is well-defined on the Multiset quotient. The hyperization
principle says: if your operation is permutation-invariant, it descends
to a well-defined operation on `Multiset`. Our theorem makes this machine-checked.
-/

end Mettapedia.Languages.MeTTa.HE
