import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedPresheafEvents
import Mettapedia.OSLF.Syntax.SecondOrderEquationProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# The actual represented pair of generic programs

The two-program equation context represents the pointwise pair of generic
program presheaves. The comparison follows from the existing equation-context
product and preservation by the actual program section and lifted Yoneda.
The generic endpoint map is the existing event projection followed by this
comparison. A semantic extension can therefore compare its transported pair
object through its structured Yoneda restriction.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier

universe w

variable {S : Signature} (R : List (LocalRule S))
variable {M : List (MetaArity S)} (equations : List (EqAxiom S M))
variable (Γ : Ctx S) (s : S.Srt)

def genericProgramPairFan :
    BinaryFan (program.{w} R equations Γ s) (program.{w} R equations Γ s) :=
  BinaryFan.mk
    ((programSection R equations ⋙ embedding R equations).map
      ((authoredEquationPresentation S equations).quotientFunctor.map
        (firstProjection S (single S Γ s) (single S Γ s))))
    ((programSection R equations ⋙ embedding R equations).map
      ((authoredEquationPresentation S equations).quotientFunctor.map
        (secondProjection S (single S Γ s) (single S Γ s))))

/-- The authored two-metavariable context remains a product after equations,
the program section and the actual lifted Yoneda embedding. -/
def genericProgramPairIsLimit : IsLimit (genericProgramPairFan.{w} R equations Γ s) := by
  let := programEmbedding_preservesLimits.{w} R equations
  exact mapIsLimitOfPreservesOfIsLimit (programSection R equations ⋙ embedding R equations) _ _
    (quotientProductIsLimit (authoredEquationPresentation S equations)
      (single S Γ s) (single S Γ s))

def genericProgramPairIso :
    (embedding.{w} R equations).obj
      ((programSection R equations).obj (pairBase equations Γ s)) ≅
        FunctorToTypes.prod (program R equations Γ s) (program R equations Γ s) :=
  (genericProgramPairIsLimit R equations Γ s).conePointUniqueUpToIso
    (FunctorToTypes.binaryProductLimit _ _)

theorem genericProgramPairIso_fst :
    (genericProgramPairIso.{w} R equations Γ s).hom ≫ FunctorToTypes.prod.fst =
      (programSection R equations ⋙ embedding R equations).map
        ((authoredEquationPresentation S equations).quotientFunctor.map
          (firstProjection S (single S Γ s) (single S Γ s))) :=
  (genericProgramPairIsLimit R equations Γ s).conePointUniqueUpToIso_hom_comp
    (FunctorToTypes.binaryProductLimit _ _) ⟨WalkingPair.left⟩

theorem genericProgramPairIso_snd :
    (genericProgramPairIso.{w} R equations Γ s).hom ≫ FunctorToTypes.prod.snd =
      (programSection R equations ⋙ embedding R equations).map
        ((authoredEquationPresentation S equations).quotientFunctor.map
          (secondProjection S (single S Γ s) (single S Γ s))) :=
  (genericProgramPairIsLimit R equations Γ s).conePointUniqueUpToIso_hom_comp
    (FunctorToTypes.binaryProductLimit _ _) ⟨WalkingPair.right⟩

private theorem pointwisePair_ext {C : Type*} [Category* C]
    {F G H : C ⥤ Type w} (f g : F ⟶ FunctorToTypes.prod G H)
    (first : f ≫ FunctorToTypes.prod.fst = g ≫ FunctorToTypes.prod.fst)
    (second : f ≫ FunctorToTypes.prod.snd = g ≫ FunctorToTypes.prod.snd) : f = g := by
  apply NatTrans.ext
  funext X
  apply ConcreteCategory.hom_ext
  intro x
  exact Prod.ext (congrArg (fun k => k.app X x) first)
    (congrArg (fun k => k.app X x) second)

/-- The existing generic event projection with its represented pair codomain. -/
abbrev genericEventProjection (Γ : Ctx S) (s : S.Srt) :
    event.{w} R equations Γ s ⟶
      (embedding R equations).obj ((programSection R equations).obj (pairBase equations Γ s)) :=
  (embedding R equations).map (toProgram R equations (eventObject R equations Γ s))

private theorem genericEventProjection_fst :
    genericEventProjection.{w} R equations Γ s ≫
      ((genericProgramPairIso R equations Γ s).hom ≫ FunctorToTypes.prod.fst) =
        genericEventSource R equations Γ s := by
  exact (congrArg (genericEventProjection R equations Γ s ≫ ·)
    (genericProgramPairIso_fst R equations Γ s)).trans
      ((embedding R equations).map_comp _ _).symm

private theorem genericEventProjection_snd :
    genericEventProjection.{w} R equations Γ s ≫
      ((genericProgramPairIso R equations Γ s).hom ≫ FunctorToTypes.prod.snd) =
        genericEventTarget R equations Γ s := by
  exact (congrArg (genericEventProjection R equations Γ s ≫ ·)
    (genericProgramPairIso_snd R equations Γ s)).trans
      ((embedding R equations).map_comp _ _).symm

/-- The image observation is taken on the actual generic event projection,
with the represented pair comparison stated explicitly. -/
theorem genericEndpointMap_projection :
    genericEndpointMap.{w} R equations Γ s =
      genericEventProjection R equations Γ s ≫
        (genericProgramPairIso R equations Γ s).hom := by
  apply pointwisePair_ext
  · exact (FunctorToTypes.prod.lift_fst _ _).trans
      ((genericEventProjection_fst R equations Γ s).symm.trans
        (Category.assoc _ _ _).symm)
  · exact (FunctorToTypes.prod.lift_snd _ _).trans
      ((genericEventProjection_snd R equations Γ s).symm.trans
        (Category.assoc _ _ _).symm)

/-- Taking images after a semantic extension uses its action on this
explicit projection and pair comparison, without assuming that it preserves
products of arbitrary presheaves. -/
theorem extension_genericEndpointMap {D : Type*} [Category* D]
    (L : Presheaf.{w} R equations ⥤ D) :
    L.map (genericEndpointMap R equations Γ s) =
      L.map ((embedding R equations).map
        (toProgram R equations (eventObject R equations Γ s))) ≫
          L.map (genericProgramPairIso R equations Γ s).hom :=
  (congrArg L.map (genericEndpointMap_projection R equations Γ s)).trans
    (L.map_comp _ _)

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf

end
