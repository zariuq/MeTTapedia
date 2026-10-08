import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorCanonicalExtension

/-!
# Transport of independent meanings through a weak closed functor

The base and fresh object meanings are mapped by the supplied functor.
Primitive arrows first retain their complete mapped values. The actual
constructor comparisons then transport each arrow to the newly interpreted
header, and the generated equations earn its local realization.

This constructs a new independently evaluated assignment and a natural
isomorphism from the genuine composite interpretation. No compatibility
with whole expressions is supplied as data. Coherence of this transport and
the free/forgetful universal construction are separate obligations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.AssignmentTransport

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory Interpretation FunctorNormalization

universe k w z

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable {E : Type z} [Category.{k} E]
variable [CartesianMonoidalCategory E] [MonoidalClosed E] [HasFiniteLimits E]
variable (meanings : Assignment C symbols D) (realization : Realization signature meanings)
variable (mapping : D ⥤ E) [PreservesFiniteLimits mapping] [MonoidalClosedFunctor mapping]

/-- Complete mapped declaration values, before transporting their headers. -/
def primitiveData : Assignment C symbols E where
  base := meanings.base ⋙ mapping
  object origin := mapping.obj (meanings.object origin)
  arrow origin := ⟨mapping.obj (meanings.arrow origin).source,
    mapping.obj (meanings.arrow origin).target, mapping.map (meanings.arrow origin).arrow⟩

abbrev composite : Object signature ⥤ E := Interpretation.functor meanings realization ⋙ mapping

private instance composite_lex : PreservesFiniteLimits (composite meanings realization mapping) :=
  comp_preservesFiniteLimits (Interpretation.functor meanings realization) mapping

private instance composite_closed : MonoidalClosedFunctor (composite meanings realization mapping) :=
  CartesianClosedFunctorCoherence.closed_composition (Interpretation.functor meanings realization) mapping

def primitiveImages : AtomicPresentation.PrimitiveImages
    (composite meanings realization mapping) (primitiveData meanings mapping) where
  base := eqToIso ((Functor.assoc (baseFunctor signature)
    (Interpretation.functor meanings realization) mapping).symm.trans
      (congrArg (fun diagram => diagram ⋙ mapping) (functor_base meanings realization)))
  object origin := eqToIso (congrArg mapping.obj
    (CoherentExtension.target_named_object meanings realization origin))

abbrev selected := AtomicPresentation.functor (composite meanings realization mapping)
  (primitiveData meanings mapping) (primitiveImages meanings realization mapping)

private instance selected_lex : PreservesFiniteLimits (selected meanings realization mapping) :=
  AtomicPresentation.functor_preservesFiniteLimits (composite meanings realization mapping)
    (primitiveData meanings mapping) (primitiveImages meanings realization mapping)

private instance selected_closed : MonoidalClosedFunctor (selected meanings realization mapping) :=
  AtomicPresentation.functor_closed (composite meanings realization mapping)
    (primitiveData meanings mapping) (primitiveImages meanings realization mapping)

variable (headers : HeaderFormation signature)

def assignment : Assignment C symbols E :=
  FunctorNormalization.assignment (selected meanings realization mapping) headers

theorem locally_realized : Realization signature (assignment meanings realization mapping headers) :=
  reconstruction_realization (selected meanings realization mapping) headers

def interpretation : Object signature ⥤ E :=
  Interpretation.functor (assignment meanings realization mapping headers)
    (locally_realized meanings realization mapping headers)

def comparison : composite meanings realization mapping ≅
    interpretation meanings realization mapping headers :=
  AtomicPresentation.comparison (composite meanings realization mapping)
    (primitiveData meanings mapping) (primitiveImages meanings realization mapping) ≪≫
      parserComparison (selected meanings realization mapping) headers

theorem assignment_base : (assignment meanings realization mapping headers).base =
    meanings.base ⋙ mapping :=
  AtomicPresentation.functor_base (composite meanings realization mapping)
    (primitiveData meanings mapping) (primitiveImages meanings realization mapping)

theorem assignment_object (origin : symbols.ObjectName) :
    (assignment meanings realization mapping headers).object origin =
      mapping.obj (meanings.object origin) := rfl

theorem assignment_arrow (origin : symbols.ArrowName) :
    (assignment meanings realization mapping headers).arrow origin =
      ⟨(objectImage (selected meanings realization mapping) (headerSource headers origin)).value,
        (objectImage (selected meanings realization mapping) (headerTarget headers origin)).value,
        (objectImage (selected meanings realization mapping) (headerSource headers origin)).comparison.inv ≫
          (selected meanings realization mapping).map (classOf (namedArrow headers origin)) ≫
            (objectImage (selected meanings realization mapping)
              (headerTarget headers origin)).comparison.hom⟩ := rfl

theorem interpretation_base : baseFunctor signature ⋙ interpretation meanings realization mapping headers =
    meanings.base ⋙ mapping :=
  (functor_base (assignment meanings realization mapping headers)
    (locally_realized meanings realization mapping headers)).trans
      (assignment_base meanings realization mapping headers)

theorem interpretation_object (origin : symbols.ObjectName) :
    (interpretation meanings realization mapping headers).obj (namedObject origin) =
      mapping.obj (meanings.object origin) :=
  (CoherentExtension.target_named_object (assignment meanings realization mapping headers)
    (locally_realized meanings realization mapping headers) origin).trans
      (assignment_object meanings realization mapping headers origin)

theorem comparison_natural {source target : Object signature} (arrow : source ⟶ target) :
    mapping.map ((Interpretation.functor meanings realization).map arrow) ≫
        (comparison meanings realization mapping headers).hom.app target =
      (comparison meanings realization mapping headers).hom.app source ≫
        (interpretation meanings realization mapping headers).map arrow :=
  (comparison meanings realization mapping headers).hom.naturality arrow

theorem complete_arrow_readout {source target : Object signature} (arrow : RawHom source target) :
    (assignment meanings realization mapping headers).evaluateArrow arrow.code =
      some ⟨(interpretation meanings realization mapping headers).obj source,
        (interpretation meanings realization mapping headers).obj target,
        (comparison meanings realization mapping headers).inv.app source ≫
          mapping.map ((Interpretation.functor meanings realization).map (classOf arrow)) ≫
            (comparison meanings realization mapping headers).hom.app target⟩ := by
  have natural := comparison_natural meanings realization mapping headers (classOf arrow)
  have conjugated := congrArg
    (fun value => (comparison meanings realization mapping headers).inv.app source ≫ value) natural
  have arrowEquality : (interpretation meanings realization mapping headers).map (classOf arrow) =
      (comparison meanings realization mapping headers).inv.app source ≫
        mapping.map ((Interpretation.functor meanings realization).map (classOf arrow)) ≫
          (comparison meanings realization mapping headers).hom.app target := by
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using conjugated.symm
  exact (functor_complete_readout (assignment meanings realization mapping headers)
    (locally_realized meanings realization mapping headers) arrow).trans
      (congrArg (fun value => some (⟨_, _, value⟩ : ArrowValue E)) arrowEquality)

end Mettapedia.CategoryTheory.RelativeClosedSyntax.AssignmentTransport
