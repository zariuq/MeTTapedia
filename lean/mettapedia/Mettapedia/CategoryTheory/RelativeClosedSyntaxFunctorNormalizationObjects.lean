import Mettapedia.CategoryTheory.RelativeClosedSyntaxInterpretationClosed
import Mettapedia.CategoryTheory.RelativeClosedSyntaxPresentedEqualizers

/-!
# Constructor-built object comparisons for a weak closed functor

An actual finite-limit and closed functor on the generated category determines
native choices for every authored object expression. Base objects and fresh
objects retain their supplied images. The other constructors use the target's
terminal, tensor product, function object and equalizer. Their comparison
isomorphisms come from preserved universal properties.

The recursion is on raw object constructors. Equalizer arrows retain their
authored representatives and their actual quotient images; the source's
independently presented equalizer is compared by its earned limit. No raw
objects are identified, and no parser compatibility is an input.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorNormalization

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open GeneratedCategory

universe k w

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]

theorem product_formation {first second : ObjectCode C symbols}
    (formed : Nonempty (Derivation signature (.object (.product first second)))) :
    Nonempty (Derivation signature (.object first)) ∧
      Nonempty (Derivation signature (.object second)) := by
  obtain ⟨tree⟩ := formed
  cases tree with
  | productObject first second => exact ⟨⟨first⟩, ⟨second⟩⟩

theorem exponential_formation {argument result : ObjectCode C symbols}
    (formed : Nonempty (Derivation signature (.object (.exponential argument result)))) :
    Nonempty (Derivation signature (.object argument)) ∧
      Nonempty (Derivation signature (.object result)) := by
  obtain ⟨tree⟩ := formed
  cases tree with
  | exponentialObject argument result => exact ⟨⟨argument⟩, ⟨result⟩⟩

theorem equalizer_formation {source target : ObjectCode C symbols}
    {first second : ArrowCode C symbols}
    (formed : Nonempty (Derivation signature (.object (.equalizer source target first second)))) :
    Nonempty (Derivation signature (.object source)) ∧
      Nonempty (Derivation signature (.object target)) ∧
      Nonempty (Derivation signature (.arrow source target first)) ∧
      Nonempty (Derivation signature (.arrow source target second)) := by
  obtain ⟨tree⟩ := formed
  cases tree with
  | equalizerObject source target first second => exact ⟨⟨source⟩, ⟨target⟩, ⟨first⟩, ⟨second⟩⟩

def objectDepth : ObjectCode C symbols → Nat
  | .base _ | .name _ | .terminal => 0
  | .product first second => 1 + objectDepth first + objectDepth second
  | .exponential argument result => 1 + objectDepth argument + objectDepth result
  | .equalizer source target _ _ => 1 + objectDepth source + objectDepth target

def functionIso {argument result before after : D}
    (input : argument ≅ before) (output : result ≅ after) :
    (argument ⟶[D] result) ≅ (before ⟶[D] after) :=
  ((MonoidalClosed.internalHom (C := D)).mapIso input.symm.op).app result ≪≫
    (ihom before).mapIso output

def equalizerTransport {source target before after : D}
    (first second : source ⟶ target) (input : source ≅ before) (output : target ≅ after) :
    equalizer first second ≅ equalizer
      (input.inv ≫ first ≫ output.hom) (input.inv ≫ second ≫ output.hom) := by
  let transformed : Fork (input.inv ≫ first ≫ output.hom)
      (input.inv ≫ second ≫ output.hom) :=
    Fork.ofι (equalizer.ι first second ≫ input.hom) (by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      simpa only [Category.assoc] using congrArg (fun arrow => arrow ≫ output.hom)
        (equalizer.condition first second))
  let preserved : IsLimit transformed := Fork.isLimitOfIsos
    (Fork.ofι (equalizer.ι first second) (equalizer.condition first second))
    (equalizerIsEqualizer first second) transformed input output (Iso.refl _)
    (by simp only [Iso.hom_inv_id_assoc])
    (by simp only [Iso.hom_inv_id_assoc])
    (by change 𝟙 _ ≫ (equalizer.ι first second ≫ input.hom) = _
        exact Category.id_comp _)
  exact preserved.conePointUniqueUpToIso
    (t := Fork.ofι (equalizer.ι (input.inv ≫ first ≫ output.hom)
      (input.inv ≫ second ≫ output.hom)) (equalizer.condition _ _))
    (equalizerIsEqualizer (input.inv ≫ first ≫ output.hom)
      (input.inv ≫ second ≫ output.hom))

variable (mapping : Object signature ⥤ D) [PreservesFiniteLimits mapping]
variable [MonoidalClosedFunctor mapping]

def mappedPresentedIsLimit {source target : Object signature}
    (first second : RawHom source target) :
    IsLimit (Fork.ofι (mapping.map (PresentedEqualizer.inclusion first second))
      (by simp only [← mapping.map_comp]; rw [PresentedEqualizer.condition]) :
        Fork (mapping.map (classOf first)) (mapping.map (classOf second))) :=
  (isLimitMapConeForkEquiv mapping (PresentedEqualizer.condition first second)).1
    (isLimitOfPreserves mapping (PresentedEqualizer.isLimit first second))

def mappedPresentedIso {source target : Object signature}
    (first second : RawHom source target) :
    mapping.obj (PresentedEqualizer.object first second) ≅
      equalizer (mapping.map (classOf first)) (mapping.map (classOf second)) :=
  (mappedPresentedIsLimit mapping first second).conePointUniqueUpToIso
    (t := Fork.ofι (equalizer.ι (mapping.map (classOf first)) (mapping.map (classOf second)))
      (equalizer.condition _ _))
    (equalizerIsEqualizer (mapping.map (classOf first)) (mapping.map (classOf second)))

omit [CartesianMonoidalCategory D] [MonoidalClosed D] [MonoidalClosedFunctor mapping] in
@[reassoc] theorem mappedPresentedIso_inclusion {source target : Object signature}
    (first second : RawHom source target) :
    (mappedPresentedIso mapping first second).hom ≫
      equalizer.ι (mapping.map (classOf first)) (mapping.map (classOf second)) =
        mapping.map (PresentedEqualizer.inclusion first second) :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (mappedPresentedIsLimit mapping first second)
    (equalizerIsEqualizer (mapping.map (classOf first)) (mapping.map (classOf second)))
    WalkingParallelPair.zero

structure ObjectImage (source : Object signature) where
  value : D
  comparison : mapping.obj source ≅ value

set_option backward.isDefEq.respectTransparency false in
def objectImage (source : Object signature) : ObjectImage mapping source := by
  classical
  rcases source with ⟨code, formed⟩
  revert formed
  cases constructor : code with
  | base object =>
      intro formed
      exact ⟨mapping.obj (baseObject signature object), Iso.refl _⟩
  | name origin =>
      intro formed
      exact ⟨mapping.obj ⟨.name origin, ⟨.objectName (signature := signature) origin⟩⟩, Iso.refl _⟩
  | terminal =>
      intro formed
      exact ⟨𝟙_ D, asIso (CartesianMonoidalCategory.terminalComparison mapping)⟩
  | product first second =>
      intro formed
      have parts := product_formation formed
      let firstObject : Object signature := ⟨first, parts.1⟩
      let secondObject : Object signature := ⟨second, parts.2⟩
      let firstImage := objectImage firstObject
      let secondImage := objectImage secondObject
      exact ⟨firstImage.value ⊗ secondImage.value,
        asIso (CartesianMonoidalCategory.prodComparison mapping firstObject secondObject) ≪≫
          tensorIso firstImage.comparison secondImage.comparison⟩
  | exponential argument result =>
      intro formed
      have parts := exponential_formation formed
      let argumentObject : Object signature := ⟨argument, parts.1⟩
      let resultObject : Object signature := ⟨result, parts.2⟩
      let argumentImage := objectImage argumentObject
      let resultImage := objectImage resultObject
      exact ⟨argumentImage.value ⟶[D] resultImage.value,
        asIso ((expComparison mapping argumentObject).natTrans.app resultObject) ≪≫
          functionIso argumentImage.comparison resultImage.comparison⟩
  | equalizer source target first second =>
      intro formed
      have parts := equalizer_formation formed
      let sourceObject : Object signature := ⟨source, parts.1⟩
      let targetObject : Object signature := ⟨target, parts.2.1⟩
      let firstArrow : RawHom sourceObject targetObject := ⟨first, parts.2.2.1⟩
      let secondArrow : RawHom sourceObject targetObject := ⟨second, parts.2.2.2⟩
      let sourceImage := objectImage sourceObject
      let targetImage := objectImage targetObject
      let mappedFirst := mapping.map (classOf firstArrow)
      let mappedSecond := mapping.map (classOf secondArrow)
      exact ⟨equalizer
          (sourceImage.comparison.inv ≫ mappedFirst ≫ targetImage.comparison.hom)
          (sourceImage.comparison.inv ≫ mappedSecond ≫ targetImage.comparison.hom),
        mappedPresentedIso mapping firstArrow secondArrow ≪≫
          equalizerTransport mappedFirst mappedSecond sourceImage.comparison targetImage.comparison⟩
termination_by objectDepth source.code
decreasing_by all_goals simp_all only [objectDepth]; all_goals omega

end Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorNormalization
