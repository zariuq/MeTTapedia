import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorReconstruction

/-!
# Earned declaration realization and complete parser comparison

The images of genuine typed primitive headers and the mapped generated
declaration equations establish the local realization of the normalized
assignment. Deterministic evaluator readouts then identify its actual quotient
interpretation with the independently normalized functor. Composing that
equality with the constructor-built comparison gives a complete natural
isomorphism from the original weak closed functor to the parser interpretation.

Objects retain their raw presentations. No free-extension universal property
or uniqueness of arbitrary declaration-preserving cells is assumed here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorNormalization

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory Interpretation

universe k w

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (mapping : Object signature ⥤ D) [PreservesFiniteLimits mapping]
variable [MonoidalClosedFunctor mapping] (headers : HeaderFormation signature)

theorem reconstruction_realization : Realization signature (assignment mapping headers) where
  source origin := object_reconstruction mapping headers (headerSource headers origin)
  target origin := object_reconstruction mapping headers (headerTarget headers origin)
  equation origin := by
    let source : Object signature := ⟨signature.equationSource origin,
      (Regularity.arrow_endpoints ⟨headers.left origin⟩).1⟩
    let target : Object signature := ⟨signature.equationTarget origin,
      (Regularity.arrow_endpoints ⟨headers.left origin⟩).2⟩
    let first : RawHom source target := ⟨signature.left origin, ⟨headers.left origin⟩⟩
    let second : RawHom source target := ⟨signature.right origin, ⟨headers.right origin⟩⟩
    have equal : (normalizedFunctor mapping).map (classOf first) =
        (normalizedFunctor mapping).map (classOf second) :=
      congrArg (normalizedFunctor mapping).map
        (classOf_equation ⟨.declaredEquation origin (headers.left origin) (headers.right origin)⟩)
    refine ⟨⟨(normalizedFunctor mapping).obj source, (normalizedFunctor mapping).obj target,
      (normalizedFunctor mapping).map (classOf first)⟩,
      object_reconstruction mapping headers source, object_reconstruction mapping headers target,
      raw_arrow_reconstruction mapping headers first, ?_⟩
    exact (raw_arrow_reconstruction mapping headers second).trans
      (congrArg (fun value => some (⟨(normalizedFunctor mapping).obj source,
        (normalizedFunctor mapping).obj target, value⟩ : ArrowValue D)) equal.symm)

def reconstructedFunctor : Object signature ⥤ D :=
  Interpretation.functor (assignment mapping headers) (reconstruction_realization mapping headers)

theorem reconstructed_object (object : Object signature) :
    (reconstructedFunctor mapping headers).obj object = (normalizedFunctor mapping).obj object :=
  objectValue_unique (assignment mapping headers) (reconstruction_realization mapping headers)
    object _ (object_reconstruction mapping headers object)

theorem reconstructed_map_heq {source target : Object signature} (raw : RawHom source target) :
    HEq ((reconstructedFunctor mapping headers).map (classOf raw))
      ((normalizedFunctor mapping).map (classOf raw)) :=
  ArrowValue.arrows_heq (Option.some.inj
    ((functor_complete_readout (assignment mapping headers)
      (reconstruction_realization mapping headers) raw).symm.trans
        (raw_arrow_reconstruction mapping headers raw)))

theorem reconstructed_functor_equal : reconstructedFunctor mapping headers = normalizedFunctor mapping := by
  refine _root_.CategoryTheory.Functor.ext (reconstructed_object mapping headers) ?_
  intro source target arrow
  refine Quotient.inductionOn arrow ?_
  intro raw
  exact (conj_eqToHom_iff_heq _ _ (reconstructed_object mapping headers source)
    (reconstructed_object mapping headers target)).mpr (reconstructed_map_heq mapping headers raw)

def parserComparison : mapping ≅ reconstructedFunctor mapping headers :=
  comparison mapping ≪≫ (eqToIso (reconstructed_functor_equal mapping headers)).symm

theorem parserComparison_natural {source target : Object signature} (arrow : source ⟶ target) :
    mapping.map arrow ≫ (parserComparison mapping headers).hom.app target =
      (parserComparison mapping headers).hom.app source ≫
        (reconstructedFunctor mapping headers).map arrow :=
  (parserComparison mapping headers).hom.naturality arrow

end Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorNormalization
