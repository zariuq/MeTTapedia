import Mettapedia.GSLT.Core.ContextualFamilyPresheaf

/-!
# The presheaf-level data of a cwf morphism

The first half of a morphism of categories with families is a pair `(F, σ)`:

* a functor `F` between the categories of contexts and substitutions; and
* a natural transformation from the source family presheaf to the target
  family presheaf pulled back along `F`.

This module isolates that representation-independent part.  Naturality is
proved below to be exactly preservation of substitution in both types and
terms.  Preservation of the chosen terminal context and context
comprehension is deliberately kept for the next layer: a natural
transformation alone is not yet a strict cwf morphism.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ContextualLadder

open CategoryTheory

universe u v w w'

/-- Pull a target family presheaf back along a context functor.  This is
definitionally the usual composite `base.op ⋙ D.familyPresheaf`, stated
directly so its object and substitution actions remain transparent. -/
def Cwf.pullbackFamilyPresheaf (C D : Cwf.{u, v, w, w'})
    (base : C.base.Context ⥤ D.base.Context) :
    C.base.Contextᵒᵖ ⥤ IndexedFamily.{w, w'} where
  obj context := D.familyPresheaf.obj (Opposite.op (base.obj context.unop))
  map substitution := D.familyPresheaf.map
    (Quiver.Hom.op (base.map substitution.unop))
  map_id context := by simp
  map_comp left right := by simp

/-- A functor of context categories together with a natural map of their
type-and-term family presheaves.  This is the `(F, σ)` data underlying both
strict and pseudo cwf morphisms. -/
structure CwfFamilyMorphism (C D : Cwf.{u, v, w, w'}) where
  base : C.base.Context ⥤ D.base.Context
  family : NatTrans C.familyPresheaf (C.pullbackFamilyPresheaf D base)

namespace CwfFamilyMorphism

variable {C D E : Cwf.{u, v, w, w'}}

/-- The induced map on types at a context. -/
def mapType (morphism : CwfFamilyMorphism C D) {Γ : C.Ctx}
    (A : C.Ty Γ) : D.Ty (morphism.base.obj ⟨Γ⟩).val :=
  (morphism.family.app (Opposite.op ⟨Γ⟩)).onIndex A

/-- The induced dependent map on terms at a context. -/
def mapTerm (morphism : CwfFamilyMorphism C D) {Γ : C.Ctx}
    {A : C.Ty Γ} (term : C.Tm Γ A) :
    D.Tm (morphism.base.obj ⟨Γ⟩).val (morphism.mapType A) :=
  (morphism.family.app (Opposite.op ⟨Γ⟩)).onFibre A term

/-- Positive type canary: naturality of the family map is precisely
preservation of substitution in types. -/
theorem mapType_substitution (morphism : CwfFamilyMorphism C D)
    {Γ Δ : C.Ctx} (substitution : C.Sub Γ Δ) (A : C.Ty Δ) :
    morphism.mapType (C.tySub A substitution) =
      D.tySub (morphism.mapType A) (morphism.base.map substitution) := by
  have naturality := morphism.family.naturality
    (Quiver.Hom.op
      (show (⟨Γ⟩ : C.base.Context) ⟶ ⟨Δ⟩ from substitution))
  exact congrArg (fun map => map.onIndex A) naturality

/-- Positive term canary: the same naturality square preserves substitution
in terms.  `HEq` records the type equality supplied by
`mapType_substitution` without choosing an additional cast convention. -/
theorem mapTerm_substitution (morphism : CwfFamilyMorphism C D)
    {Γ Δ : C.Ctx} {A : C.Ty Δ} (term : C.Tm Δ A)
    (substitution : C.Sub Γ Δ) :
    HEq (morphism.mapTerm (C.tmSub term substitution))
      (D.tmSub (morphism.mapTerm term) (morphism.base.map substitution)) := by
  have naturality := morphism.family.naturality
    (Quiver.Hom.op
      (show (⟨Γ⟩ : C.base.Context) ⟶ ⟨Δ⟩ from substitution))
  have fibreNaturality :
      HEq
        (((C.familyPresheaf.map (Quiver.Hom.op substitution)) ≫
          morphism.family.app (Opposite.op ⟨Γ⟩)).onFibre A term)
        ((morphism.family.app (Opposite.op ⟨Δ⟩) ≫
          ((C.pullbackFamilyPresheaf D morphism.base).map
            (Quiver.Hom.op substitution))).onFibre A term) := by
    rw [naturality]
  exact fibreNaturality

/-- Identity context and family translation. -/
def identity (C : Cwf.{u, v, w, w'}) : CwfFamilyMorphism C C where
  base := 𝟭 C.base.Context
  family :=
    { app := fun context => 𝟙 (C.familyPresheaf.obj context)
      naturality := by
        intro source target substitution
        rfl }

@[simp]
theorem identity_mapType {Γ : C.Ctx} (A : C.Ty Γ) :
    (identity C).mapType A = A := rfl

@[simp]
theorem identity_mapTerm {Γ : C.Ctx} {A : C.Ty Γ}
    (term : C.Tm Γ A) :
    (identity C).mapTerm term = term := rfl

#print axioms CwfFamilyMorphism.mapType_substitution
#print axioms CwfFamilyMorphism.mapTerm_substitution
#print axioms Cwf.pullbackFamilyPresheaf
#print axioms CwfFamilyMorphism.identity
#print axioms CwfFamilyMorphism.identity_mapType
#print axioms CwfFamilyMorphism.identity_mapTerm

end CwfFamilyMorphism

end Mettapedia.GSLT.Core.ContextualLadder
