import Mettapedia.CategoryTheory.RelativeClosedSyntaxSignatureMapClosed
import Mettapedia.CategoryTheory.RelativeClosedSyntaxSignatureMapComposition
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorNormalizationReadout
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorNormalizationClosed
import Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence

/-!
# Native closed shapes through declaration maps

A declaration map retains the actual chosen terminal, products and function
objects of the generated presentation. Its canonical comparisons were earned
from the generated arrow equations. Here those comparisons give complete
normalization transport through postcomposition, including the contravariant
function argument. The source shapes may contain embedded base objects and
fresh objects, arbitrary products and arbitrary function objects.

No assertion about a generated equalizer's selected representative is needed
for this closed-shape comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.SignatureMap

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory GeneratedCategory FunctorNormalization

universe k

variable {C D E : Type k} [Category.{k} C] [Category.{k} D] [Category.{k} E]
variable {sourceNames middleNames targetNames : Symbols.{k}}
variable {source : Signature (C := C) (symbols := sourceNames)}
variable {middle : Signature (C := D) (symbols := middleNames)}
variable {target : Signature (C := E) (symbols := targetNames)}
variable (mapping : SignatureMap middle target)

private theorem typed_code_square {first last nextFirst nextLast : Object target}
    (before : RawHom first last) (after : RawHom nextFirst nextLast)
    (firstSame : first = nextFirst) (lastSame : last = nextLast)
    (codeSame : before.code = after.code) :
    eqToHom firstSame ≫ classOf after = classOf before ≫ eqToHom lastSame := by
  cases firstSame
  cases lastSame
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact congrArg classOf (RawHom.ext codeSame).symm

theorem functor_composition_readout (first : SignatureMap source middle)
    {start finish : Object source} (arrow : start ⟶ finish) :
    eqToHom (SignatureMap.object_compose first mapping start) ≫
        (first.compose mapping).functor.map arrow =
      mapping.functor.map (first.functor.map arrow) ≫
        eqToHom (SignatureMap.object_compose first mapping finish) := by
  refine Quotient.inductionOn arrow ?_
  intro raw
  exact typed_code_square (mapping.rawArrow (first.rawArrow raw))
    ((first.compose mapping).rawArrow raw) (SignatureMap.object_compose first mapping start)
    (SignatureMap.object_compose first mapping finish) (SignatureMap.arrow_code_compose first mapping raw)

theorem functor_curry {context argument result : Object middle}
    (body : argument ⊗ context ⟶ result) :
    mapping.functor.map (MonoidalClosed.curry body) =
      MonoidalClosed.curry (A := mapping.functor.obj argument)
        (Y := mapping.functor.obj context) (X := mapping.functor.obj result)
        (mapping.functor.map body) := by
  rw [FunctorNormalization.source_curry, mapping.functor_abstraction, mapping.functor.map_comp]
  change abstraction ((GeneratedCategory.exchange (mapping.functor.obj context)
    (mapping.functor.obj argument)).hom ≫ mapping.functor.map body) = _
  exact (FunctorNormalization.source_curry
    (argument := mapping.functor.obj argument) (context := mapping.functor.obj context)
    (result := mapping.functor.obj result) (mapping.functor.map body)).symm

theorem functor_lift {context first second : Object middle}
    (before : context ⟶ first) (after : context ⟶ second) :
    mapping.functor.map (lift before after) =
      lift (mapping.functor.map before) (mapping.functor.map after) :=
  mapping.functor_pairing before after

theorem functor_toUnit (context : Object middle) :
    mapping.functor.map (toUnit context) = toUnit (mapping.functor.obj context) :=
  toUnit_unique _ _

theorem functor_rightUnitor_hom (object : Object middle) :
    mapping.functor.map (ρ_ object).hom = (ρ_ (mapping.functor.obj object)).hom := by
  rw [rightUnitor_hom, rightUnitor_hom]
  rfl

/-- Full ordered closed shapes, with embedded and named objects as leaves. -/
inductive ClosedShape : Object source → Prop
  | base (object : C) : ClosedShape (baseObject source object)
  | named (origin : sourceNames.ObjectName) : ClosedShape (namedObject origin)
  | unit : ClosedShape (terminal source)
  | product {first second : Object source} :
      ClosedShape first → ClosedShape second → ClosedShape (product first second)
  | function {argument result : Object source} :
      ClosedShape argument → ClosedShape result → ClosedShape (exponentialObject argument result)

theorem functor_tensorHom {first nextFirst second nextSecond : Object middle}
    (before : first ⟶ nextFirst) (after : second ⟶ nextSecond) :
    mapping.functor.map (before ⊗ₘ after) =
      mapping.functor.map before ⊗ₘ mapping.functor.map after := by
  apply CartesianMonoidalCategory.hom_ext
    (X := mapping.functor.obj nextFirst) (Y := mapping.functor.obj nextSecond)
  · change mapping.functor.map (before ⊗ₘ after) ≫ mapping.functor.map (fst nextFirst nextSecond) = _
    rw [← mapping.functor.map_comp, tensorHom_fst, mapping.functor.map_comp]
    exact (tensorHom_fst (mapping.functor.map before) (mapping.functor.map after)).symm
  · change mapping.functor.map (before ⊗ₘ after) ≫ mapping.functor.map (snd nextFirst nextSecond) = _
    rw [← mapping.functor.map_comp, tensorHom_snd, mapping.functor.map_comp]
    exact (tensorHom_snd (mapping.functor.map before) (mapping.functor.map after)).symm

theorem functor_ihom {before after : Object middle} (argument : Object middle)
    (change : before ⟶ after) :
    mapping.functor.map ((ihom argument).map change) =
      (ihom (mapping.functor.obj argument)).map (mapping.functor.map change) := by
  have natural := ((expComparison mapping.functor argument).natTrans).naturality change
  change mapping.functor.map ((ihom argument).map change) ≫
      (expComparison mapping.functor argument).natTrans.app after =
    (expComparison mapping.functor argument).natTrans.app before ≫
      (ihom (mapping.functor.obj argument)).map (mapping.functor.map change) at natural
  rw [mapping.expComparison_identity, mapping.expComparison_identity] at natural
  change mapping.functor.map ((ihom argument).map change) ≫ 𝟙 _ =
    𝟙 _ ≫ (ihom (mapping.functor.obj argument)).map (mapping.functor.map change) at natural
  simpa only [Category.comp_id, Category.id_comp] using natural

theorem functor_pre {argument nextArgument : Object middle}
    (change : nextArgument ⟶ argument) (result : Object middle) :
    mapping.functor.map ((MonoidalClosed.pre change).app result) =
      (MonoidalClosed.pre (mapping.functor.map change)).app (mapping.functor.obj result) := by
  have natural := congrArg (fun square => square.natTrans.app result)
    (expComparison_whiskerLeft mapping.functor change)
  change (expComparison mapping.functor argument).natTrans.app result ≫
      (MonoidalClosed.pre (mapping.functor.map change)).app (mapping.functor.obj result) =
    mapping.functor.map ((MonoidalClosed.pre change).app result) ≫
      (expComparison mapping.functor nextArgument).natTrans.app result at natural
  rw [mapping.expComparison_identity, mapping.expComparison_identity] at natural
  change 𝟙 _ ≫ (MonoidalClosed.pre (mapping.functor.map change)).app (mapping.functor.obj result) =
    mapping.functor.map ((MonoidalClosed.pre change).app result) ≫ 𝟙 _ at natural
  simpa only [Category.comp_id, Category.id_comp] using natural.symm

variable (before : Object source ⥤ Object middle)
variable [PreservesFiniteLimits before] [MonoidalClosedFunctor before]

private instance composite_finite : PreservesFiniteLimits (before ⋙ mapping.functor) :=
  comp_preservesFiniteLimits _ _

private instance composite_closed : MonoidalClosedFunctor (before ⋙ mapping.functor) :=
  CartesianClosedFunctorCoherence.closed_composition _ _

/-- Map both the complete chosen object and its actual comparison. -/
def mappedObjectImage (object : Object source) : ObjectImage (before ⋙ mapping.functor) object where
  value := mapping.functor.obj (objectImage before object).value
  comparison := mapping.functor.mapIso (objectImage before object).comparison

theorem objectImage_postcomposition {object : Object source} (shape : ClosedShape object) :
    objectImage (before ⋙ mapping.functor) object = mappedObjectImage mapping before object := by
  induction shape with
  | base object =>
      rw [objectImage_base]
      unfold mappedObjectImage
      rw [objectImage_base]
      apply congrArg (fun comparison => (⟨_, comparison⟩ : ObjectImage (before ⋙ mapping.functor) _))
      apply Iso.ext
      exact (mapping.functor.map_id _).symm
  | named origin =>
      rw [objectImage_named]
      unfold mappedObjectImage
      rw [objectImage_named]
      apply congrArg (fun comparison => (⟨_, comparison⟩ : ObjectImage (before ⋙ mapping.functor) _))
      apply Iso.ext
      exact (mapping.functor.map_id _).symm
  | unit =>
      rw [objectImage_terminal]
      unfold mappedObjectImage
      rw [objectImage_terminal]
      apply congrArg (fun comparison => (⟨_, comparison⟩ : ObjectImage (before ⋙ mapping.functor) _))
      apply Iso.ext
      exact Subsingleton.elim _ _
  | @product first second firstShape secondShape firstSame secondSame =>
      rw [objectImage_product, firstSame, secondSame]
      unfold mappedObjectImage
      rw [objectImage_product]
      apply congrArg (fun comparison => (⟨_, comparison⟩ : ObjectImage (before ⋙ mapping.functor) _))
      apply Iso.ext
      change CartesianMonoidalCategory.prodComparison (before ⋙ mapping.functor) first second ≫
          (mapping.functor.map (objectImage before first).comparison.hom ⊗ₘ
            mapping.functor.map (objectImage before second).comparison.hom) =
        mapping.functor.map (CartesianMonoidalCategory.prodComparison before first second ≫
          ((objectImage before first).comparison.hom ⊗ₘ (objectImage before second).comparison.hom))
      rw [CartesianMonoidalCategory.prodComparison_comp, mapping.productComparison_identity]
      erw [Category.comp_id]
      simp only [mapping.functor.map_comp, mapping.functor_tensorHom]
  | @function argument result argumentShape resultShape argumentSame resultSame =>
      rw [objectImage_exponential, argumentSame, resultSame]
      unfold mappedObjectImage
      rw [objectImage_exponential]
      apply congrArg (fun comparison => (⟨_, comparison⟩ : ObjectImage (before ⋙ mapping.functor) _))
      apply Iso.ext
      change (expComparison (before ⋙ mapping.functor) argument).natTrans.app result ≫
          (MonoidalClosed.pre (mapping.functor.map (objectImage before argument).comparison.inv)).app
            (mapping.functor.obj (before.obj result)) ≫
          (ihom (mapping.functor.obj (objectImage before argument).value)).map
            (mapping.functor.map (objectImage before result).comparison.hom) =
        mapping.functor.map ((expComparison before argument).natTrans.app result ≫
          (MonoidalClosed.pre (objectImage before argument).comparison.inv).app (before.obj result) ≫
          (ihom (objectImage before argument).value).map (objectImage before result).comparison.hom)
      rw [CartesianClosedFunctorCoherence.exponential_composition, mapping.expComparison_identity]
      erw [Category.comp_id]
      simp only [mapping.functor.map_comp, mapping.functor_pre, mapping.functor_ihom]

theorem normalized_arrow_postcomposition {first second : Object source}
    (firstShape : ClosedShape first) (secondShape : ClosedShape second)
    (arrow : first ⟶ second) :
    (⟨(normalizedFunctor (before ⋙ mapping.functor)).obj first,
      (normalizedFunctor (before ⋙ mapping.functor)).obj second,
      (normalizedFunctor (before ⋙ mapping.functor)).map arrow⟩ : Interpretation.ArrowValue (Object target)) =
    ⟨mapping.functor.obj ((normalizedFunctor before).obj first),
      mapping.functor.obj ((normalizedFunctor before).obj second),
      mapping.functor.map ((normalizedFunctor before).map arrow)⟩ := by
  change (⟨(objectImage (before ⋙ mapping.functor) first).value,
    (objectImage (before ⋙ mapping.functor) second).value,
    (objectImage (before ⋙ mapping.functor) first).comparison.inv ≫
      mapping.functor.map (before.map arrow) ≫
        (objectImage (before ⋙ mapping.functor) second).comparison.hom⟩ : Interpretation.ArrowValue (Object target)) = _
  rw [objectImage_postcomposition mapping before firstShape,
    objectImage_postcomposition mapping before secondShape]
  simp only [mappedObjectImage, Functor.mapIso_inv, Functor.mapIso_hom,
    normalizedFunctor, Functor.map_comp]

end Mettapedia.CategoryTheory.RelativeClosedSyntax.SignatureMap
