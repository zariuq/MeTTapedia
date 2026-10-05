import Mettapedia.TypeTheory.MaterialSets.DependentProduct
import Mettapedia.TypeTheory.MaterialSets.Hypersets.MembershipEvidence

/-!
# Dependent products of hypersets

The material function-graph construction applies to hypersets without imposing
foundation on their members. The product is separated from the powerset of the
dependent-pair set and its members are equivalent to dependent functions on the
member types. The same construction applies within the well-founded part.

An explicit `Presentation` supplies the dependent replacement operation. Supplying
`Presentation.choice` would use classical choice; evaluation of a product member
does not introduce additional choice. The resulting hyperset is independent of
which presentation was supplied. All constructions remain at the graph-size
level `u`; this does not assert a universe containing every hyperset.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u

namespace HSet

/-- Hyperset separation realizes the generic separation interface. -/
def separation : SeparationOperation fun x X : HSet.{u} => x ∈ X where
  sep := HSet.sep
  nonempty_mem_sep_iff := by
    intro x X p
    exact nonempty_iff_of_prop.trans (mem_sep.trans
      ⟨fun h => ⟨⟨h.1⟩, h.2⟩, fun h => ⟨h.1.elim id, h.2⟩⟩)

/-- Hyperset powerset realizes the generic powerset interface. -/
def power : PowersetOperation fun x X : HSet.{u} => x ∈ X where
  powerset := powerset
  nonempty_mem_powerset_iff := by
    intro Y X
    exact nonempty_iff_of_prop.trans (mem_powerset.trans
      ⟨fun h _ hz => ⟨h (hz.elim id)⟩, fun h _ hz => (h _ ⟨hz⟩).elim id⟩)

/-- The hyperset of total single-valued dependent function graphs. -/
def dependentProduct (p : Presentation.{u}) (X : HSet.{u})
    (B : El (· ∈ ·) X → HSet.{u}) : HSet.{u} :=
  piSet (dependentReplacement p) union kuratowski separation power X B

/-- Every member of a dependent product evaluates to an actual dependent function,
and every dependent function has a unique material graph. -/
def piSetEquiv (p : Presentation.{u}) (X : HSet.{u}) (B : El (· ∈ ·) X → HSet.{u}) :
    El (· ∈ ·) (dependentProduct p X B) ≃ (∀ a, El (· ∈ ·) (B a)) :=
  MaterialSets.piSetEquiv (dependentReplacement p) union kuratowski separation power
    propositional recovery extensional X B

theorem mem_dependentProduct_iff {p : Presentation.{u}} {X G : HSet.{u}}
    {B : El (· ∈ ·) X → HSet.{u}} :
    G ∈ dependentProduct p X B ↔
      (∀ z ∈ G, z ∈ sigmaSet (dependentReplacement p) union kuratowski X B) ∧
        IsFunctionGraph kuratowski X B G := by
  exact nonempty_iff_of_prop.symm.trans
    ((nonempty_mem_piSet_iff (dependentReplacement p) union kuratowski separation power).trans
      ⟨fun h => ⟨fun z hz => (h.1 z ⟨hz⟩).elim id, h.2⟩,
        fun h => ⟨fun z hz => ⟨h.1 z (hz.elim id)⟩, h.2⟩⟩)

theorem mem_sigmaSet_iff {p : Presentation.{u}} {X z : HSet.{u}}
    {B : El (· ∈ ·) X → HSet.{u}} :
    z ∈ sigmaSet (dependentReplacement p) union kuratowski X B ↔
      ∃ (a : El (· ∈ ·) X) (b : El (· ∈ ·) (B a)), kpair a.1 b.1 = z :=
  ⟨fun hz => exists_of_mem_sigmaSet (dependentReplacement p) union kuratowski hz,
    fun ⟨a, b, e⟩ => e ▸ (pairMember (dependentReplacement p) union kuratowski ⟨a, b⟩).2⟩

/-- The product's extensional meaning is independent of presentation selection. -/
theorem dependentProduct_eq_of_presentations (p q : Presentation.{u}) (X : HSet.{u})
    (B : El (· ∈ ·) X → HSet.{u}) : dependentProduct p X B = dependentProduct q X B := by
  apply ext
  intro G
  rw [mem_dependentProduct_iff, mem_dependentProduct_iff]
  have same : sigmaSet (dependentReplacement p) union kuratowski X B =
      sigmaSet (dependentReplacement q) union kuratowski X B :=
    ext fun _ => mem_sigmaSet_iff.trans mem_sigmaSet_iff.symm
  rw [same]

/-- The empty dependent product is the singleton consisting of the empty graph. -/
theorem dependentProduct_empty (p : Presentation.{u})
    (B : El (· ∈ ·) (∅ : HSet.{u}) → HSet.{u}) : dependentProduct p ∅ B = {∅} := by
  apply ext
  intro G
  rw [mem_dependentProduct_iff, mem_singleton]
  constructor
  · intro h
    apply eq_empty_iff.mpr
    intro z hz
    obtain ⟨a, _, _⟩ := mem_sigmaSet_iff.mp (h.1 z hz)
    exact notMem_empty a.1 a.2
  · rintro rfl
    exact ⟨fun z hz => (notMem_empty z hz).elim,
      fun a => (notMem_empty a.1 a.2).elim⟩

/-- An empty fibre over an actual domain member leaves no function graph. -/
theorem dependentProduct_eq_empty_of_empty_fibre (p : Presentation.{u})
    {X : HSet.{u}} {B : El (· ∈ ·) X → HSet.{u}} (a : El (· ∈ ·) X)
    (empty : B a = ∅) : dependentProduct p X B = ∅ := by
  apply eq_empty_iff.mpr
  intro G hG
  have b := piSetEquiv p X B ⟨G, hG⟩ a
  exact notMem_empty b.1 (empty ▸ b.2)

/-- Concrete negative control: the nonempty singleton domain with empty fibres
has empty dependent product. -/
theorem dependentProduct_singleton_empty (p : Presentation.{u}) :
    dependentProduct p ({∅} : HSet.{u}) (fun _ => ∅) = ∅ :=
  dependentProduct_eq_empty_of_empty_fibre p ⟨∅, mem_singleton_self ∅⟩ rfl

/-- A singleton domain and singleton fibre have precisely the one singleton
function graph. The arguments may themselves be non-well-founded hypersets. -/
theorem dependentProduct_singleton_singleton (p : Presentation.{u}) (x y : HSet.{u}) :
    dependentProduct p {x} (fun _ => {y}) = {{kpair x y}} := by
  apply ext
  intro G
  rw [mem_dependentProduct_iff, mem_singleton]
  constructor
  · rintro ⟨bound, good⟩
    have only : ∀ z ∈ G, z = kpair x y := by
      intro z hz
      obtain ⟨a, b, e⟩ := mem_sigmaSet_iff.mp (bound z hz)
      have ha : a.1 = x := mem_singleton.mp a.2
      have hb : b.1 = y := mem_singleton.mp b.2
      rw [ha, hb] at e
      exact e.symm
    obtain ⟨b, entry, _⟩ := good ⟨x, mem_singleton_self x⟩
    have hb : b.1 = y := mem_singleton.mp b.2
    have includes : kpair x y ∈ G := hb ▸ entry.elim id
    exact ext fun z => ⟨fun hz => mem_singleton.mpr (only z hz),
      fun hz => mem_singleton.mp hz ▸ includes⟩
  · rintro rfl
    constructor
    · intro z hz
      obtain rfl := mem_singleton.mp hz
      exact mem_sigmaSet_iff.mpr
        ⟨⟨x, mem_singleton_self x⟩, ⟨y, mem_singleton_self y⟩, rfl⟩
    · intro a
      have ha : a.1 = x := mem_singleton.mp a.2
      refine ⟨⟨y, mem_singleton_self y⟩, ?_, ?_⟩
      · change Nonempty (kpair a.1 y ∈ {kpair x y})
        rw [ha]
        exact ⟨mem_singleton_self (kpair x y)⟩
      · rintro z ⟨hz⟩ _
        obtain rfl := mem_singleton.mp hz
        exact snd_kpair x y

/-- Positive non-well-founded control: functions on the singleton containing the
self-membered Quine atom exist and use the same graph construction. -/
theorem dependentProduct_quine_singleton (p : Presentation.{u}) :
    dependentProduct p {quineAtom.{u}} (fun _ => {quineAtom}) =
      {{kpair quineAtom quineAtom}} :=
  dependentProduct_singleton_singleton p quineAtom quineAtom

end HSet

namespace WellFoundedPart

open HSet

/-- Separation restricts to well-founded hypersets. -/
def separation : SeparationOperation Mem.{u} where
  sep p X :=
    ⟨HSet.sep (fun z => ∃ hz : z.WF, p ⟨z, hz⟩) X.1, X.2.sep _⟩
  nonempty_mem_sep_iff := by
    intro x X p
    change Nonempty (x.1 ∈ HSet.sep (fun z => ∃ hz : z.WF, p ⟨z, hz⟩) X.1) ↔
      Nonempty (x.1 ∈ X.1) ∧ p x
    rw [nonempty_iff_of_prop, mem_sep, nonempty_iff_of_prop]
    exact ⟨fun ⟨hx, _, hp⟩ => ⟨hx, hp⟩, fun ⟨hx, hp⟩ => ⟨hx, x.2, hp⟩⟩

/-- Every subset of a well-founded hyperset is well-founded. -/
def power : PowersetOperation Mem.{u} where
  powerset X := ⟨HSet.powerset X.1, X.2.powerset⟩
  nonempty_mem_powerset_iff := by
    intro Y X
    change Nonempty (Y.1 ∈ HSet.powerset X.1) ↔
      ∀ z : WellFoundedPart.{u}, Nonempty (z.1 ∈ Y.1) → Nonempty (z.1 ∈ X.1)
    rw [nonempty_iff_of_prop, mem_powerset]
    exact ⟨fun h z hz => ⟨h (hz.elim id)⟩,
      fun h z hz => (h ⟨z, Y.2.mem hz⟩ ⟨hz⟩).elim id⟩

/-- Material dependent products stay within the well-founded part. -/
def dependentProduct (p : Presentation.{u}) (X : WellFoundedPart.{u})
    (B : El Mem X → WellFoundedPart.{u}) : WellFoundedPart.{u} :=
  piSet (dependentReplacement p) union pairing separation power X B

def piSetEquiv (p : Presentation.{u}) (X : WellFoundedPart.{u})
    (B : El Mem X → WellFoundedPart.{u}) :
    El Mem (dependentProduct p X B) ≃ (∀ a, El Mem (B a)) :=
  MaterialSets.piSetEquiv (dependentReplacement p) union pairing separation power
    propositional recovery extensional X B

end WellFoundedPart

end Mettapedia.TypeTheory.MaterialSets.Hypersets
