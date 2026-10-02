import Mettapedia.GSLT.LanguageDef.CanonicalSection
import Mettapedia.GSLT.LanguageDef.Cost.Elaboration.ReplayKey

/-!
# Exact keys and observations of canonical classes

A canonical section gives an exact key for an equation class, computable
when the supplied normalizer is computable.  This
key supports exactly the observations invariant under the selected equations.
An optional digest can accelerate comparison, but the final exact-key check
is what makes acceptance independent of hash collisions.
-/

namespace Mettapedia.GSLT.LanguageDef.ComputableSetoidSection

open Cost.Elaboration

universe u v

variable {Carrier : Type u} {relation : Setoid Carrier}
    (canonical : ComputableSetoidSection Carrier relation)

/-- The selected representatives, retaining their normalization invariant. -/
abbrev Key := { term : Carrier // canonical.normalize term = term }

/-- Compute the exact key of a term's equation class. -/
def key (term : Carrier) : canonical.Key :=
  ⟨canonical.normalize term, canonical.normalize_idempotent term⟩

@[simp] theorem key_val (term : Carrier) :
    (canonical.key term).val = canonical.normalize term := rfl

@[simp] theorem key_representative (key : canonical.Key) :
    canonical.key key.val = key :=
  Subtype.ext key.property

/-- Equality of exact keys is the selected equation relation. -/
theorem key_eq_iff (left right : Carrier) :
    canonical.key left = canonical.key right ↔ relation.r left right := by
  rw [Subtype.ext_iff]
  exact (canonical.equivalent_iff_normalize_eq left right).symm

/-- Exact keys represent the quotient without choosing a new normalizer. -/
def quotientEquiv : Quotient relation ≃ canonical.Key where
  toFun value := ⟨canonical.representative value,
    canonical.representative_normal value⟩
  invFun key := Quotient.mk relation key.val
  left_inv := canonical.representative_spec
  right_inv key := Subtype.ext key.property

@[simp] theorem quotientEquiv_mk (term : Carrier) :
    canonical.quotientEquiv (Quotient.mk relation term) =
      canonical.key term := rfl

/-- Canonical keys support precisely the equation-invariant observations. -/
theorem supports_iff {Value : Type v} (observe : Carrier → Value) :
    ReplayKey.Supports canonical.key observe ↔
      ∀ left right, relation.r left right → observe left = observe right := by
  constructor
  · intro supported left right equivalent
    exact supported ((canonical.key_eq_iff left right).mpr equivalent)
  · intro invariant left right sameKey
    exact invariant left right ((canonical.key_eq_iff left right).mp sameKey)

/-- An invariant observation runs directly on selected representatives. -/
def realize {Value : Type v} (observe : Carrier → Value)
    (invariant : ∀ left right, relation.r left right →
      observe left = observe right) :
    ObservationRealization canonical.key observe :=
  ObservationRealization.ofSplit canonical.key Subtype.val
    canonical.key_representative observe
    ((canonical.supports_iff observe).mpr invariant)

/-- Every digest of canonical keys is constant on each equation class. -/
theorem digest_eq_of_equivalent {Digest : Type v}
    (digest : canonical.Key → Digest) {left right : Carrier}
    (equivalent : relation.r left right) :
    digest (canonical.key left) = digest (canonical.key right) :=
  congrArg digest ((canonical.key_eq_iff left right).mpr equivalent)

/-- The exact key always retains at least the information in its digest. -/
def digestRefinement {Digest : Type v} (digest : canonical.Key → Digest) :
    KeyRefinement canonical.key (digest ∘ canonical.key) where
  forget := digest
  commutes := rfl

/-- A literal observation that separates equivalent representatives cannot
be reconstructed from their canonical-class keys. -/
theorem no_realization_of_distinguished_equivalents {Value : Type v}
    (observe : Carrier → Value) {left right : Carrier}
    (equivalent : relation.r left right)
    (distinguished : observe left ≠ observe right) :
    ¬ ReplayKey.HasRealization canonical.key observe := by
  rintro ⟨realization⟩
  exact distinguished (((canonical.supports_iff observe).mp
    realization.supports) left right equivalent)

/-- Digest comparison followed by exact-key comparison. -/
def checkKey {Digest : Type v} [DecidableEq Digest]
    [DecidableEq Carrier] (digest : canonical.Key → Digest)
    (left right : canonical.Key) : Bool :=
  decide (digest left = digest right) && decide (left = right)

/-- Hash collisions cannot create false positives after exact comparison. -/
@[simp] theorem checkKey_eq_true_iff {Digest : Type v} [DecidableEq Digest]
    [DecidableEq Carrier] (digest : canonical.Key → Digest)
    (left right : canonical.Key) :
    canonical.checkKey digest left right = true ↔ left = right := by
  simp only [checkKey, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨And.right, fun same => ⟨congrArg digest same, same⟩⟩

/-- Exact validation tests equation classes even with a colliding digest. -/
theorem checkKey_keys_iff {Digest : Type v} [DecidableEq Digest]
    [DecidableEq Carrier] (digest : canonical.Key → Digest)
    (left right : Carrier) :
    canonical.checkKey digest (canonical.key left) (canonical.key right) = true ↔
      relation.r left right := by
  rw [checkKey_eq_true_iff, key_eq_iff]

end Mettapedia.GSLT.LanguageDef.ComputableSetoidSection
