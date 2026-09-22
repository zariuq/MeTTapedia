import Mettapedia.GSLT.Topos.PredicateFibration

/-!
# The universal quantifier of a presheaf predicate, pointwise

Reindexing a predicate along a map of type-valued functors has a right
adjoint.  The ambient predicate package already carries such an operation,
but only as a best approximation from below — a supremum over the predicates
whose reindexing is small enough — which supports the adjunction and nothing
computational.  This file supplies the standard pointwise description and
proves it is the right adjoint:

* `forallAlong f Ψ` — a section of the target satisfies it when every
  restriction of that section, and every source section lying over that
  restriction, satisfies `Ψ`;
* `preimage_le_iff_le_forallAlong` — the adjunction, in usable biconditional
  form;
* `forallAlong_eq_universalImage` — agreement with the existing operation,
  since right adjoints of one map are unique.

The pointwise form is what later constructions need: the abstract supremum
cannot be computed against, while this one is an ordinary quantifier over
restrictions, so statements about it reduce to naturality.

Controls at the end of the file record that the quantifier is not the
reindexing it is adjoint to, and is not the direct image.

## References

- Mac Lane–Moerdijk, "Sheaves in Geometry and Logic" (1994), Ch. I.3 and
  III.8 (quantifiers along maps of presheaves).
- Jacobs, "Categorical Logic and Type Theory" (1999), Ch. 1 and Ch. 4
  (reindexing with its two adjoints).
-/

open CategoryTheory

universe w v u

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos

variable {C : Type u} [Category.{v} C] {P Q : C ⥤ Type w}

/-- The universal quantifier of a predicate along a map of type-valued
functors, pointwise. -/
def forallAlong (f : P ⟶ Q) (Ψ : Subfunctor P) : Subfunctor Q where
  obj U := {q | ∀ (V : C) (i : U ⟶ V) (p : P.obj V),
    f.app V p = Q.map i q → p ∈ Ψ.obj V}
  map {U V} i := by
    intro q holds W j p over
    refine holds W (i ≫ j) p ?_
    rw [over, Functor.map_comp_apply]

@[simp] theorem mem_forallAlong (f : P ⟶ Q) (Ψ : Subfunctor P) (U : C)
    (q : Q.obj U) :
    q ∈ (forallAlong f Ψ).obj U ↔
      ∀ (V : C) (i : U ⟶ V) (p : P.obj V),
        f.app V p = Q.map i q → p ∈ Ψ.obj V := Iff.rfl

/-- Reindexing along `f` is left adjoint to the universal quantifier
along `f`. -/
theorem preimage_le_iff_le_forallAlong (f : P ⟶ Q) (Ψ : Subfunctor P)
    (χ : Subfunctor Q) :
    χ.preimage f ≤ Ψ ↔ χ ≤ forallAlong f Ψ := by
  constructor
  · intro below U q member V i p over
    refine below V ?_
    show f.app V p ∈ χ.obj V
    rw [over]
    exact χ.map i member
  · intro above U p member
    have held : f.app U p ∈ (forallAlong f Ψ).obj U := above U member
    exact held U (𝟙 U) p (by rw [Functor.map_id_apply])

/-- The adjunction as a Galois connection. -/
theorem galois_preimage_forallAlong (f : P ⟶ Q) :
    GaloisConnection (fun χ : Subfunctor Q => χ.preimage f)
      (fun Ψ : Subfunctor P => forallAlong f Ψ) :=
  fun χ Ψ => preimage_le_iff_le_forallAlong f Ψ χ

theorem forallAlong_mono (f : P ⟶ Q) : Monotone (forallAlong f) := by
  intro Ψ Ψ' below U q holds V i p over
  exact below V (holds V i p over)

@[simp] theorem forallAlong_top (f : P ⟶ Q) :
    forallAlong f (⊤ : Subfunctor P) = ⊤ := by
  ext U q
  simp [forallAlong]

/-- Right adjoints of one map agree, so the pointwise quantifier is the
operation the ambient predicate package already carried. -/
theorem forallAlong_eq_universalImage (D : Type u) [Category.{u} D]
    {X Y : Dᵒᵖ ⥤ Type u} (f : X ⟶ Y) (Ψ : Subfunctor X) :
    forallAlong f Ψ = (presheafChangeOfBase.{u, u, u} D).universalImage f Ψ := by
  have ours := galois_preimage_forallAlong f
  have theirs := (presheafChangeOfBase.{u, u, u} D).pullback_universal_adj f
  refine le_antisymm ?_ ?_
  · exact (theirs (forallAlong f Ψ) Ψ).mp (ours.l_u_le Ψ)
  · exact (ours ((presheafChangeOfBase.{u, u, u} D).universalImage f Ψ) Ψ).mp
      (theirs.l_u_le Ψ)

/-! ## Controls -/

section Controls

private abbrev ControlBase := Discrete PUnit

/-- A two-valued constant presheaf over a one-object base. -/
private abbrev boolPresheaf : ControlBaseᵒᵖ ⥤ Type :=
  (Functor.const ControlBaseᵒᵖ).obj Bool

/-- A map whose image omits one section. -/
private def alwaysTrue : boolPresheaf ⟶ boolPresheaf where
  app _ := TypeCat.ofHom (fun _ => true)

private abbrev controlSpot : ControlBaseᵒᵖ :=
  Opposite.op (Discrete.mk PUnit.unit)

/-- The omitted section satisfies the universal quantifier of the empty
predicate, because nothing lies over it: vacuous satisfaction is real
content, so the quantifier of the empty predicate is not empty. -/
theorem forallAlong_bot_ne_bot :
    forallAlong alwaysTrue (⊥ : Subfunctor boolPresheaf) ≠
      (⊥ : Subfunctor boolPresheaf) := by
  intro equal
  have held : false ∈
      (forallAlong alwaysTrue (⊥ : Subfunctor boolPresheaf)).obj controlSpot := by
    intro V i p over
    simp [alwaysTrue, boolPresheaf] at over
  rw [equal] at held
  exact held

/-- The direct image of the empty predicate stays empty. -/
theorem image_bot_eq_bot :
    (⊥ : Subfunctor boolPresheaf).image alwaysTrue =
      (⊥ : Subfunctor boolPresheaf) := by
  ext U value
  constructor
  · rintro ⟨p, held, _⟩
    exact held
  · exact fun held => held.elim

/-- Consequently the two adjoints of reindexing are distinct operations: the
universal quantifier is not the direct image. -/
theorem forallAlong_ne_image :
    forallAlong alwaysTrue (⊥ : Subfunctor boolPresheaf) ≠
      (⊥ : Subfunctor boolPresheaf).image alwaysTrue := by
  rw [image_bot_eq_bot]
  exact forallAlong_bot_ne_bot

end Controls

end Mettapedia.GSLT.Topos

#print axioms Mettapedia.GSLT.Topos.preimage_le_iff_le_forallAlong
#print axioms Mettapedia.GSLT.Topos.galois_preimage_forallAlong
#print axioms Mettapedia.GSLT.Topos.forallAlong_mono
#print axioms Mettapedia.GSLT.Topos.forallAlong_top
#print axioms Mettapedia.GSLT.Topos.forallAlong_eq_universalImage
#print axioms Mettapedia.GSLT.Topos.forallAlong_bot_ne_bot
#print axioms Mettapedia.GSLT.Topos.image_bot_eq_bot
#print axioms Mettapedia.GSLT.Topos.forallAlong_ne_image
