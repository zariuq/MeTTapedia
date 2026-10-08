import Mettapedia.CategoryTheory.RelativeClosedSyntaxSignatureMap
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctor

/-!
# Interpretation under a declaration-local presentation map

Precomposition supplies only the individual old generator meanings and the
composite base functor. The two structural evaluators commute on every raw
expression, including rejected endpoint checks and equalizer candidates.
Local declaration realization is then transported by these earned equations.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.SignatureMap

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Interpretation

universe u v a w z b r h

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {D : Type w} [Category.{z} D] {nextSymbols : Symbols.{b}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {next : Signature (C := D) (symbols := nextSymbols)}
variable {E : Type r} [Category.{h} E]
variable [CartesianMonoidalCategory E] [MonoidalClosed E] [HasFiniteLimits E]

def precompose (mapping : SignatureMap signature next)
    (assignment : Assignment D nextSymbols E) : Assignment C symbols E where
  base := mapping.base ⋙ assignment.base
  object origin := assignment.object (mapping.objects origin)
  arrow origin := assignment.arrow (mapping.arrows origin)

mutual

theorem evaluateObjectLift_precompose (mapping : SignatureMap signature next)
    (assignment : Assignment D nextSymbols E) : (code : ObjectCode C symbols) →
    assignment.evaluateObjectLift (code.map mapping.base mapping.objects mapping.arrows) =
      (mapping.precompose assignment).evaluateObjectLift code
  | .base _ => rfl
  | .name _ => rfl
  | .terminal => rfl
  | .product _ _ => by
      simp only [ObjectCode.map, Assignment.evaluateObjectLift,
        evaluateObjectLift_precompose mapping assignment]
  | .exponential _ _ => by
      simp only [ObjectCode.map, Assignment.evaluateObjectLift,
        evaluateObjectLift_precompose mapping assignment]
  | .equalizer _ _ _ _ => by
      simp only [ObjectCode.map, Assignment.evaluateObjectLift,
        evaluateObjectLift_precompose mapping assignment,
        evaluateArrow_precompose mapping assignment]

theorem evaluateArrow_precompose (mapping : SignatureMap signature next)
    (assignment : Assignment D nextSymbols E) : (code : ArrowCode C symbols) →
    assignment.evaluateArrow (code.map mapping.base mapping.objects mapping.arrows) =
      (mapping.precompose assignment).evaluateArrow code
  | .base _ => rfl
  | .name _ => rfl
  | .identity _ => by
      simp only [ArrowCode.map, Assignment.evaluateArrow,
        evaluateObjectLift_precompose mapping assignment]
  | .compose _ _ => by
      simp only [ArrowCode.map, Assignment.evaluateArrow,
        evaluateArrow_precompose mapping assignment]
  | .terminal _ => by
      simp only [ArrowCode.map, Assignment.evaluateArrow,
        evaluateObjectLift_precompose mapping assignment]
  | .first _ _ => by
      simp only [ArrowCode.map, Assignment.evaluateArrow,
        evaluateObjectLift_precompose mapping assignment]
  | .second _ _ => by
      simp only [ArrowCode.map, Assignment.evaluateArrow,
        evaluateObjectLift_precompose mapping assignment]
  | .pair _ _ => by
      simp only [ArrowCode.map, Assignment.evaluateArrow,
        evaluateArrow_precompose mapping assignment]
  | .evaluation _ _ => by
      simp only [ArrowCode.map, Assignment.evaluateArrow,
        evaluateObjectLift_precompose mapping assignment]
  | .curry _ _ _ _ => by
      simp only [ArrowCode.map, Assignment.evaluateArrow,
        evaluateObjectLift_precompose mapping assignment,
        evaluateArrow_precompose mapping assignment]
  | .equalizerArrow _ _ _ _ => by
      simp only [ArrowCode.map, Assignment.evaluateArrow,
        evaluateObjectLift_precompose mapping assignment,
        evaluateArrow_precompose mapping assignment]
  | .equalizerLift _ _ _ _ _ _ => by
      simp only [ArrowCode.map, Assignment.evaluateArrow,
        evaluateObjectLift_precompose mapping assignment,
        evaluateArrow_precompose mapping assignment]

end

variable (mapping : SignatureMap signature next) (assignment : Assignment D nextSymbols E)

theorem evaluateObject_precompose (code : ObjectCode C symbols) :
    assignment.evaluateObject (code.map mapping.base mapping.objects mapping.arrows) =
      (mapping.precompose assignment).evaluateObject code :=
  congrArg ULift.down (mapping.evaluateObjectLift_precompose assignment code)

theorem realization_precompose (realization : Realization next assignment) :
    Realization signature (mapping.precompose assignment) where
  source origin :=
    (mapping.evaluateObject_precompose assignment (signature.source origin)).symm.trans
      ((congrArg assignment.evaluateObject (mapping.source origin).symm).trans
        (realization.source (mapping.arrows origin)))
  target origin :=
    (mapping.evaluateObject_precompose assignment (signature.target origin)).symm.trans
      ((congrArg assignment.evaluateObject (mapping.target origin).symm).trans
        (realization.target (mapping.arrows origin)))
  equation origin := by
    obtain ⟨value, source, target, before, after⟩ := realization.equation (mapping.equations origin)
    refine ⟨value, ?_, ?_, ?_, ?_⟩
    · exact (mapping.evaluateObject_precompose assignment (signature.equationSource origin)).symm.trans
        ((congrArg assignment.evaluateObject (mapping.equationSource origin).symm).trans source)
    · exact (mapping.evaluateObject_precompose assignment (signature.equationTarget origin)).symm.trans
        ((congrArg assignment.evaluateObject (mapping.equationTarget origin).symm).trans target)
    · exact (mapping.evaluateArrow_precompose assignment (signature.left origin)).symm.trans
        ((congrArg assignment.evaluateArrow (mapping.left origin).symm).trans before)
    · exact (mapping.evaluateArrow_precompose assignment (signature.right origin)).symm.trans
        ((congrArg assignment.evaluateArrow (mapping.right origin).symm).trans after)

theorem objectValue_precompose (realization : Realization next assignment)
    (object : GeneratedCategory.Object signature) :
    objectValue assignment realization (mapping.object object) =
      objectValue (mapping.precompose assignment) (mapping.realization_precompose assignment realization)
        object := by
  have mapped := objectValue_readout assignment realization (mapping.object object)
  have original := objectValue_readout (mapping.precompose assignment)
    (mapping.realization_precompose assignment realization) object
  exact Option.some.inj
    (mapped.symm.trans ((mapping.evaluateObject_precompose assignment object.code).trans original))

omit [CartesianMonoidalCategory E] [MonoidalClosed E] [HasFiniteLimits E] in
private theorem arrowValue_heq {source target before after : E}
    {first : source ⟶ target} {second : before ⟶ after}
    (same : (⟨source, target, first⟩ : ArrowValue E) = ⟨before, after, second⟩) :
    HEq first second := by
  have sourceSame : source = before := congrArg ArrowValue.source same
  have targetSame : target = after := congrArg ArrowValue.target same
  subst before
  subst after
  exact heq_of_eq (ArrowValue.arrow_injective same)

theorem rawArrowValue_precompose (realization : Realization next assignment)
    {source target : GeneratedCategory.Object signature}
    (arrow : GeneratedCategory.RawHom source target) :
    HEq (rawArrowValue assignment realization (mapping.rawArrow arrow))
      (rawArrowValue (mapping.precompose assignment)
        (mapping.realization_precompose assignment realization) arrow) := by
  have mapped := rawArrowValue_readout assignment realization (mapping.rawArrow arrow)
  have original := rawArrowValue_readout (mapping.precompose assignment)
    (mapping.realization_precompose assignment realization) arrow
  exact arrowValue_heq (Option.some.inj
    (mapped.symm.trans ((mapping.evaluateArrow_precompose assignment arrow.code).trans original)))

theorem functor_precompose (realization : Realization next assignment) :
    mapping.functor ⋙ Interpretation.functor assignment realization =
      Interpretation.functor (mapping.precompose assignment)
        (mapping.realization_precompose assignment realization) := by
  refine _root_.CategoryTheory.Functor.hext
    (F := mapping.functor ⋙ Interpretation.functor assignment realization)
    (G := Interpretation.functor (mapping.precompose assignment)
      (mapping.realization_precompose assignment realization))
    (mapping.objectValue_precompose assignment realization) ?_
  intro source target arrow
  refine Quotient.inductionOn arrow ?_
  intro representative
  exact mapping.rawArrowValue_precompose assignment realization representative

end Mettapedia.CategoryTheory.RelativeClosedSyntax.SignatureMap
