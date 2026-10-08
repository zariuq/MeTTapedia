import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableIndexedInterpretation

/-!
# Complete fibre witnesses, comprehension and restriction

The native indexed type decodes to the independently specified original
arrow fibre. Its complete comprehension is isomorphic to the original
representable source, with the actual original arrow as projection.
Restriction transports the supplied witness by precomposition.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableIndexedDeclarations

open _root_.CategoryTheory Opposite
open ContextualModelTelescopes NativeLocalTypeFormers

universe u
variable {C : Type u} [Category.{u} C]

noncomputable section

def decode (arrow : ArrowSymbol C) (world : Cᵒᵖ)
    (argument : (objectScope arrow.target).1.obj world)
    (value : (fibreMeaning arrow).decoded.obj ⟨world, argument⟩) :
    {source : world.unop ⟶ arrow.source |
      source ≫ arrow.arrow = (objectName arrow.target).app world argument} :=
  ⟨value.val, value.property⟩

def encode (arrow : ArrowSymbol C) (world : Cᵒᵖ)
    (argument : (objectScope arrow.target).1.obj world)
    (source : world.unop ⟶ arrow.source)
    (indexed : source ≫ arrow.arrow = (objectName arrow.target).app world argument) :
    (fibreMeaning arrow).decoded.obj ⟨world, argument⟩ :=
  ⟨source, indexed⟩

theorem decode_encode (arrow : ArrowSymbol C) (world : Cᵒᵖ)
    (argument : (objectScope arrow.target).1.obj world) (source : world.unop ⟶ arrow.source)
    (indexed : source ≫ arrow.arrow = (objectName arrow.target).app world argument) :
    decode arrow world argument (encode arrow world argument source indexed) = ⟨source, indexed⟩ := rfl

theorem encode_decode (arrow : ArrowSymbol C) (world : Cᵒᵖ)
    (argument : (objectScope arrow.target).1.obj world)
    (value : (fibreMeaning arrow).decoded.obj ⟨world, argument⟩) :
    encode arrow world argument (decode arrow world argument value).val
      (decode arrow world argument value).property = value := by
  cases value
  rfl

theorem inhabited_iff (arrow : ArrowSymbol C) (world : Cᵒᵖ)
    (argument : (objectScope arrow.target).1.obj world) :
    Nonempty ((fibreMeaning arrow).decoded.obj ⟨world, argument⟩) ↔
      ∃ source : world.unop ⟶ arrow.source,
        source ≫ arrow.arrow = (objectName arrow.target).app world argument := by
  constructor
  · rintro ⟨value⟩
    exact ⟨(decode arrow world argument value).val, (decode arrow world argument value).property⟩
  · rintro ⟨source, indexed⟩
    exact ⟨encode arrow world argument source indexed⟩

theorem restriction_complete (arrow : ArrowSymbol C) {world future : Cᵒᵖ}
    (before : world ⟶ future) (argument : (objectScope arrow.target).1.obj world)
    (value : (fibreMeaning arrow).decoded.obj ⟨world, argument⟩) :
    (decode arrow future ((objectScope arrow.target).1.map before argument)
      ((fibreMeaning arrow).decoded.map ⟨before, rfl⟩ value)).val =
        before.unop ≫ (decode arrow world argument value).val := rfl

def fibreNameInverse (arrow : ArrowSymbol C) :
    yoneda.obj arrow.source ⟶ (fibreScope arrow).1 where
  app _ := TypeCat.ofHom fun source =>
    ⟨(objectNameInverse arrow.target).app _ (source ≫ arrow.arrow), ⟨source, rfl⟩⟩
  naturality := by
    intro world future before
    ext source
    change (⟨⟨PUnit.unit, (before.unop ≫ source) ≫ arrow.arrow⟩,
      ⟨before.unop ≫ source, rfl⟩⟩ : (fibreScope arrow).1.obj future) =
        ⟨⟨PUnit.unit, before.unop ≫ (source ≫ arrow.arrow)⟩,
          ⟨before.unop ≫ source, Category.assoc _ _ _⟩⟩
    apply Sigma.ext
    · exact Sigma.ext rfl (heq_of_eq (Category.assoc _ _ _))
    · apply (Subtype.heq_iff_coe_eq ?_).mpr
      · rfl
      · intro candidate
        change (candidate ≫ arrow.arrow = (before.unop ≫ source) ≫ arrow.arrow) ↔
          candidate ≫ arrow.arrow = before.unop ≫ (source ≫ arrow.arrow)
        exact ⟨fun indexed => indexed.trans (Category.assoc _ _ _),
          fun indexed => indexed.trans (Category.assoc _ _ _).symm⟩

def fibreScopeIso (arrow : ArrowSymbol C) : (fibreScope arrow).1 ≅ yoneda.obj arrow.source where
  hom := fibreName arrow
  inv := fibreNameInverse arrow
  hom_inv_id := by
    ext world value
    change (⟨(objectNameInverse arrow.target).app world (value.2.val ≫ arrow.arrow),
      ⟨value.2.val, rfl⟩⟩ : (fibreScope arrow).1.obj world) = value
    rcases value with ⟨⟨singleton, argument⟩, ⟨source, indexed⟩⟩
    cases singleton
    change world.unop ⟶ arrow.source at source
    change world.unop ⟶ arrow.target at argument
    change source ≫ arrow.arrow = argument at indexed
    subst argument
    rfl
  inv_hom_id := by ext world source; rfl

/-- The projection is the supplied original arrow, after the earned
source and target comprehension comparisons. -/
theorem comprehension_projection (arrow : ArrowSymbol C) :
    (fibreScopeIso arrow).hom ≫ yoneda.map arrow.arrow =
      (NativeModel C).toCwf.wk (fibreMeaning arrow) ≫ objectName arrow.target := by
  ext world value
  exact value.2.property

theorem forget_complete (arrow : ArrowSymbol C) (world : Cᵒᵖ)
    (argument : (objectScope arrow.target).1.obj world)
    (value : (fibreMeaning arrow).decoded.obj ⟨world, argument⟩) :
    (forgetValue arrow).val ⟨world, ⟨argument, value⟩⟩ =
      (decode arrow world argument value).val := rfl

theorem forget_restriction (arrow : ArrowSymbol C) {world future : Cᵒᵖ}
    (before : world ⟶ future) (value : (fibreScope arrow).1.obj world) :
    (forgetValue arrow).val ⟨future, (fibreScope arrow).1.map before value⟩ =
      before.unop ≫ (forgetValue arrow).val ⟨world, value⟩ := rfl

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableIndexedDeclarations
