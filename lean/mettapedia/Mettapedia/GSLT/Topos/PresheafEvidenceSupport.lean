import Mettapedia.GSLT.Topos.PresheafPredicateHeyting
import Mathlib.CategoryTheory.Elements

/-!
# The interface between proof-relevant families and predicates

Predicate fibres over a presheaf are thin: a predicate says whether a section
satisfies it, and nothing more.  A proof-relevant family says *how* a section
satisfies it, and may offer several witnesses.  This file gives the comparison
between the two layers and states exactly what it loses. Evidence families
are functors on the category of elements, the same construction used by the
displayed-presheaf CwF. Their transport obeys identity and composition.

The comparison runs from the proof-relevant layer to the thin one, because
that is the only canonical direction: a witness can always be forgotten, while
producing one from a bare predicate would be a choice rather than a map.

* `support E` — the predicate holding exactly where `E` has evidence;
* `support_mono` — a fibrewise map of families entails their supports, so the
  comparison is monotone; natural family maps are a special case;
* `trivialFamily φ` — the canonical proof-irrelevant family of a predicate;
* `support_trivialFamily` — every predicate is the support of that family, so
  the comparison is a **split epimorphism** and the thin layer is a retract of
  the proof-relevant one;
* `trivialFamily_subsingleton` — the canonical section lands entirely in
  proof-irrelevant families.

## What is lost, stated rather than implied

`support_forgets_multiplicity` exhibits two families with **equal support**,
one carrying a single witness everywhere and one carrying two distinct
witnesses everywhere.  So the retraction is not an equivalence, and
multiplicity of evidence is precisely what the thin layer cannot see.

This matters for consumers that require proof relevance.  A requirement of the
form "the same term admits two retained evidence values" is satisfiable in the
proof-relevant layer and unsatisfiable in a thin predicate fibre, so such a
requirement must be met before the support map is applied, never after it.
The comparison is the place to record that boundary, not to hide it.

## References

- Jacobs, "Categorical Logic and Type Theory" (1999), Ch. 1 and Ch. 4
  (subobject fibrations are proof irrelevant; comprehension categories are
  not).
- Mac Lane–Moerdijk, "Sheaves in Geometry and Logic" (1994), Ch. I.3.
-/

open CategoryTheory

universe w v u

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos

variable {C : Type u} [Category.{v} C] {P : C ⥤ Type w}

/-- A proof-relevant family with coherent transport. This is the existing
category-of-elements construction, not a separate unchecked transport API. -/
abbrev EvidenceFamily (P : C ⥤ Type w) := P.Elements ⥤ Type w

/-- Support: the predicate holding exactly where evidence exists. -/
def support (E : EvidenceFamily P) : Subfunctor P where
  obj U := {x | Nonempty (E.obj ⟨U, x⟩)}
  map {U V} i := by
    rintro x ⟨evidence⟩
    exact ⟨E.map (CategoryOfElements.homMk _ _ i rfl) evidence⟩

@[simp] theorem mem_support (E : EvidenceFamily P) (U : C) (x : P.obj U) :
    x ∈ (support E).obj U ↔ Nonempty (E.obj ⟨U, x⟩) := Iff.rfl

/-- A fibrewise map of evidence families gives an
entailment of supports. -/
theorem support_mono {E E' : EvidenceFamily P}
    (f : ∀ (U : C) (x : P.obj U), E.obj ⟨U, x⟩ → E'.obj ⟨U, x⟩) :
    support E ≤ support E' := by
  rintro U x ⟨evidence⟩
  exact ⟨f U x evidence⟩

/-- A natural transformation of coherent families entails their supports. -/
theorem support_map {E E' : EvidenceFamily P} (f : E ⟶ E') :
    support E ≤ support E' :=
  support_mono (fun U x => f.app ⟨U, x⟩)

/-- Support is unchanged by a natural isomorphism of evidence families. -/
theorem support_iso {E E' : EvidenceFamily P} (f : E ≅ E') :
    support E = support E' :=
  le_antisymm (support_map f.hom) (support_map f.inv)

/-- Forgetting evidence commutes with presheaf-context substitution.
The family is pulled back by the actual functor on categories of elements. -/
theorem support_reindex {Q : C ⥤ Type w} (f : P ⟶ Q)
    (E : EvidenceFamily Q) :
    support (f.mapElements ⋙ E) = (support E).preimage f := by
  ext U x
  rfl

/-- The canonical proof-irrelevant family of a predicate: its evidence is the
proposition that the section satisfies it. -/
def trivialFamily (φ : Subfunctor P) : EvidenceFamily P where
  obj value := ULift.{w, 0} (PLift (value.2 ∈ φ.obj value.1))
  map {source target} i := TypeCat.ofHom fun e =>
    ULift.up (PLift.up (i.property ▸ φ.map i.val e.down.down))
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- Support is a split epimorphism: every predicate is the support of a
family, namely its own proof-irrelevant one. -/
theorem support_trivialFamily (φ : Subfunctor P) :
    support (trivialFamily φ) = φ := by
  ext U x
  constructor
  · intro held
    exact held.some.down.down
  · intro held
    exact ⟨ULift.up (PLift.up held)⟩

/-- The canonical section lands in proof-irrelevant families. -/
theorem trivialFamily_subsingleton (φ : Subfunctor P) (U : C) (x : P.obj U)
    (e e' : (trivialFamily φ).obj ⟨U, x⟩) : e = e' := by
  obtain ⟨⟨_⟩⟩ := e
  obtain ⟨⟨_⟩⟩ := e'
  rfl

/-- An entailment from support supplies a natural map to the predicate's
proof-irrelevant family. The input evidence is used only for inhabitation. -/
def mapToTrivialFamily (E : EvidenceFamily P) (φ : Subfunctor P)
    (held : support E ≤ φ) : E ⟶ trivialFamily φ where
  app value := TypeCat.ofHom fun evidence =>
    ⟨⟨held value.1 ⟨evidence⟩⟩⟩
  naturality := by intro source target arrow; ext; rfl

/-- Support has the reflection universal property: natural maps into a
predicate family correspond exactly to entailments from support. -/
def supportHomEquiv (E : EvidenceFamily P) (φ : Subfunctor P) :
    (E ⟶ trivialFamily φ) ≃ (support E ≤ φ) where
  toFun f := by
    rintro U x ⟨evidence⟩
    exact (f.app ⟨U, x⟩ evidence).down.down
  invFun := mapToTrivialFamily E φ
  left_inv f := by ext; rfl
  right_inv _ := rfl

/-- Evidence that is always a single point. -/
def pointEvidence (P : C ⥤ Type w) : EvidenceFamily P :=
  (Functor.const P.Elements).obj PUnit

/-- Evidence that is always two points. -/
def pairEvidence (P : C ⥤ Type w) : EvidenceFamily P :=
  (Functor.const P.Elements).obj (ULift Bool)

theorem support_pointEvidence : support (pointEvidence P) = ⊤ := by
  ext U x
  exact ⟨fun _ => trivial, fun _ => ⟨PUnit.unit⟩⟩

theorem support_pairEvidence : support (pairEvidence P) = ⊤ := by
  ext U x
  exact ⟨fun _ => trivial, fun _ => ⟨ULift.up true⟩⟩

/-- Support forgets multiplicity of evidence: two families with the same
support, one with a single witness everywhere and one with two. -/
theorem support_forgets_multiplicity :
    support (pointEvidence P) = support (pairEvidence P) ∧
      (∀ (U : C) (x : P.obj U) (e e' : (pointEvidence P).obj ⟨U, x⟩), e = e') ∧
      (∀ (U : C) (x : P.obj U),
        ∃ e e' : (pairEvidence P).obj ⟨U, x⟩, e ≠ e') := by
  refine ⟨by rw [support_pointEvidence, support_pairEvidence], ?_, ?_⟩
  · intro _ _ e e'
    rfl
  · intro U x
    refine ⟨ULift.up true, ULift.up false, ?_⟩
    intro equal
    exact Bool.noConfusion (congrArg ULift.down equal)
end Mettapedia.GSLT.Topos

#print axioms Mettapedia.GSLT.Topos.support_mono
#print axioms Mettapedia.GSLT.Topos.support_reindex
#print axioms Mettapedia.GSLT.Topos.support_iso
#print axioms Mettapedia.GSLT.Topos.supportHomEquiv
#print axioms Mettapedia.GSLT.Topos.support_trivialFamily
#print axioms Mettapedia.GSLT.Topos.trivialFamily_subsingleton
#print axioms Mettapedia.GSLT.Topos.support_forgets_multiplicity
