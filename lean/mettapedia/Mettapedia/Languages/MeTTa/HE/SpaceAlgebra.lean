/-
# SpaceAlgebra: the abstract storage/query surface

The published interpreter specification fixes program-level state sequencing
("each atom sees the effects of preceding evaluations or atomspace
modifications") but does not specify the storage operations themselves.  This
module is the conservative extension: a minimal signature whose laws are
determined by what the engines actually share, with coherence doing the
specifying.

Design, in the shape the surrounding development already uses:

* **Operations are a signature; laws are separate bundles.**  Removal
  semantics differs between engines — HE/LeaTTa/CeTTa decrement one
  occurrence, a set-semantics engine zeroes the class — so that difference is
  a LAW VARIANT over ONE signature (`CountedBagSpace` vs `SetSpace`), not two
  signatures.  A set-semantics engine instantiates the same algebra with a
  different equational theory rather than being excluded or forcing the core
  weaker.
* **Multiplicity is primitive**, because it is the shared observable and
  cannot be recovered from a Boolean membership predicate.
* **Query is relational in the core**, so no backend result ORDER is claimed;
  an ordered readout is a separate `QueryEnumeration` extension supplied by
  deterministic backends and required only where byte-exact conformance is.
* **Coherence binds the layers**: without it the two could float free and a
  lawful instance could make additions invisible to query — the degenerate
  model the algebra exists to exclude.

Nothing here mentions any engine's concrete state type.
-/
import Mathlib.Data.List.Basic

namespace Mettapedia.Languages.MeTTa.HE.SpaceAlgebra

/-! ## Signature -/

/-- Abstract atomspace storage over a carrier `S` with atoms `A`.

`multiplicity` is primitive: it is the observable the target engines share,
and a Boolean membership cannot determine it. -/
structure StorageOps (S : Type _) (A : Type _) where
  empty : S
  add : A → S → S
  remove : A → S → S
  multiplicity : S → A → Nat

namespace StorageOps

variable {S A : Type _} (ops : StorageOps S A)

/-- Membership is DERIVED from multiplicity, never primitive. -/
def Mem (s : S) (a : A) : Prop := 0 < ops.multiplicity s a

/-- Two states are observationally equal when every atom has the same
multiplicity.  All laws below are stated observationally — never on raw
carrier equality — so backends with different internal representations can
satisfy them. -/
def ObsEq (s t : S) : Prop := ∀ a, ops.multiplicity s a = ops.multiplicity t a

theorem obsEq_refl (s : S) : ops.ObsEq s s := fun _ => rfl

theorem obsEq_symm {s t : S} (h : ops.ObsEq s t) : ops.ObsEq t s :=
  fun a => (h a).symm

theorem obsEq_trans {s t u : S} (h : ops.ObsEq s t) (h' : ops.ObsEq t u) :
    ops.ObsEq s u := fun a => (h a).trans (h' a)

end StorageOps

/-! ## Law bundles

The core laws every engine shares, then the removal variants. -/

/-- Laws shared by every atomspace: the empty space is empty, and `add`
increments exactly the added atom's count. -/
structure StorageLaws {S A : Type _} (ops : StorageOps S A) : Prop where
  multiplicity_empty : ∀ a, ops.multiplicity ops.empty a = 0
  multiplicity_add_self : ∀ a s, ops.multiplicity (ops.add a s) a
    = ops.multiplicity s a + 1
  multiplicity_add_other : ∀ a b s, a ≠ b →
    ops.multiplicity (ops.add a s) b = ops.multiplicity s b

/-- Counted-bag removal (HE default, LeaTTa, CeTTa): one occurrence at a
time. -/
structure CountedBagLaws {S A : Type _} (ops : StorageOps S A) : Prop
    extends StorageLaws ops where
  multiplicity_remove_self : ∀ a s,
    ops.multiplicity (ops.remove a s) a = ops.multiplicity s a - 1
  multiplicity_remove_other : ∀ a b s, a ≠ b →
    ops.multiplicity (ops.remove a s) b = ops.multiplicity s b

/-- Set-style removal (e.g. a filter-all implementation): the whole class
goes.  Same signature, different equational theory — which is why this is a
law variant rather than a second algebra. -/
structure SetLaws {S A : Type _} (ops : StorageOps S A) : Prop
    extends StorageLaws ops where
  multiplicity_remove_self : ∀ a s, ops.multiplicity (ops.remove a s) a = 0
  multiplicity_remove_other : ∀ a b s, a ≠ b →
    ops.multiplicity (ops.remove a s) b = ops.multiplicity s b

/-! ### Consequences of the shared core -/

variable {S A : Type _} {ops : StorageOps S A}

theorem not_mem_empty (laws : StorageLaws ops) (a : A) :
    ¬ ops.Mem ops.empty a := by
  simp [StorageOps.Mem, laws.multiplicity_empty a]

theorem mem_add_self (laws : StorageLaws ops) (a : A) (s : S) :
    ops.Mem (ops.add a s) a := by
  simp [StorageOps.Mem, laws.multiplicity_add_self a s]

/-- Adding is observationally monotone: nothing is lost. -/
theorem multiplicity_le_add (laws : StorageLaws ops) (a b : A) (s : S) :
    ops.multiplicity s b ≤ ops.multiplicity (ops.add a s) b := by
  by_cases h : a = b
  · subst h
    rw [laws.multiplicity_add_self]
    omega
  · rw [laws.multiplicity_add_other a b s h]
    exact Nat.le_refl _

/-- Remove-after-add returns to the original multiplicity, observationally —
never as raw-state equality.  This is the load-bearing counted-bag law and it
FAILS for set semantics when the atom was already present, which is exactly
the difference the two bundles record. -/
theorem countedBag_remove_add (laws : CountedBagLaws ops) (a : A) (s : S) :
    ops.ObsEq (ops.remove a (ops.add a s)) s := by
  intro b
  by_cases h : a = b
  · subst h
    rw [laws.multiplicity_remove_self, laws.multiplicity_add_self]
    omega
  · rw [laws.multiplicity_remove_other a b _ h, laws.multiplicity_add_other a b s h]

/-- Under set semantics, remove-after-add is idempotent-to-zero rather than
restoring: the observable that distinguishes the two law bundles. -/
theorem set_remove_add (laws : SetLaws ops) (a : A) (s : S) :
    ops.multiplicity (ops.remove a (ops.add a s)) a = 0 :=
  laws.multiplicity_remove_self a (ops.add a s)

/-! ## Query layer

Relational in the core: no result order is claimed, because backends
genuinely differ.  `QueryRel s pattern result` reads "querying `s` with
`pattern` admits `result`". -/

/-- Abstract relational query over the same carrier. -/
structure QueryOps (S : Type _) (A : Type _) (R : Type _) where
  QueryRel : S → A → R → Prop

/-! ### Coherence

The gap that would otherwise let the layers float free: query must SEE what
storage holds.  Without this an instance could satisfy every storage law and
every query law while additions remained invisible to query — the degenerate
model the algebra exists to exclude. -/

/-- Coherence between storage and query: an atom is visible to the query
layer exactly when its multiplicity is positive. -/
structure QueryCoherent {S A R : Type _}
    (ops : StorageOps S A) (q : QueryOps S A R) (observe : A → R) : Prop where
  visible_iff_present : ∀ s a, q.QueryRel s a (observe a) ↔ ops.Mem s a

/-- Coherence forces additions to be observable — the anti-degeneracy
consequence. -/
theorem query_sees_added {S A R : Type _} {ops : StorageOps S A}
    {q : QueryOps S A R} {observe : A → R}
    (laws : StorageLaws ops) (coh : QueryCoherent ops q observe)
    (a : A) (s : S) : q.QueryRel (ops.add a s) a (observe a) :=
  (coh.visible_iff_present (ops.add a s) a).mpr (mem_add_self laws a s)

/-- Coherence forces the empty space to answer nothing — the other half of
anti-degeneracy. -/
theorem query_empty_blind {S A R : Type _} {ops : StorageOps S A}
    {q : QueryOps S A R} {observe : A → R}
    (laws : StorageLaws ops) (coh : QueryCoherent ops q observe) (a : A) :
    ¬ q.QueryRel ops.empty a (observe a) := by
  intro h
  exact not_mem_empty laws a ((coh.visible_iff_present ops.empty a).mp h)

/-! ## Enumeration extension

Byte-exact conformance needs an ORDER that the relational core deliberately
does not fix.  Deterministic backends supply this extension; engines whose
enumeration order is unspecified still satisfy the core.  The law ties the
readout to the relation so an enumeration cannot invent or drop solutions. -/

/-- An ordered readout of the relational query. -/
structure QueryEnumeration {S A R : Type _} (q : QueryOps S A R) where
  enumerate : S → A → List R
  /-- The listing contains exactly the relational solutions. -/
  mem_enumerate_iff : ∀ s pattern r,
    r ∈ enumerate s pattern ↔ q.QueryRel s pattern r

/-- An enumeration determines the relation, so two enumerations of the same
query agree as sets — order remains backend-specific, contents do not. -/
theorem enumerations_agree_as_sets {S A R : Type _} {q : QueryOps S A R}
    (e f : QueryEnumeration q) (s : S) (pattern : A) (r : R) :
    r ∈ e.enumerate s pattern ↔ r ∈ f.enumerate s pattern := by
  rw [e.mem_enumerate_iff, f.mem_enumerate_iff]

end Mettapedia.Languages.MeTTa.HE.SpaceAlgebra
