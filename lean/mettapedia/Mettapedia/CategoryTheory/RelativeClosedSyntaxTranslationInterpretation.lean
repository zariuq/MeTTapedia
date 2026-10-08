import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationFunctor
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctor

/-!
# Independent interpretation under coded expression translations

Precomposition evaluates each independently authored target expression with
its actual supplied formation or arrow tree, and retains the composite base
functor. The two structural evaluators commute on every raw
expression, including rejected endpoint checks and equalizer candidates.
Local declaration realization is then transported by these earned equations.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Interpretation

universe u v a w z b r h

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {D : Type w} [Category.{z} D] {nextSymbols : Symbols.{b}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {next : Signature (C := D) (symbols := nextSymbols)}
variable {E : Type r} [Category.{h} E]
variable [CartesianMonoidalCategory E] [MonoidalClosed E] [HasFiniteLimits E]

def translatedObject (mapping : Translation signature next) (origin : symbols.ObjectName) :
    GeneratedCategory.Object next := ⟨mapping.data.objects origin, ⟨mapping.objectTyped origin⟩⟩

def translatedSource (mapping : Translation signature next) (origin : symbols.ArrowName) :
    GeneratedCategory.Object next :=
  ⟨(signature.source origin).translate mapping.data,
    (Regularity.derivation (mapping.arrowTyped origin)).1⟩

def translatedTarget (mapping : Translation signature next) (origin : symbols.ArrowName) :
    GeneratedCategory.Object next :=
  ⟨(signature.target origin).translate mapping.data,
    (Regularity.derivation (mapping.arrowTyped origin)).2⟩

def translatedArrow (mapping : Translation signature next) (origin : symbols.ArrowName) :
    GeneratedCategory.RawHom (mapping.translatedSource origin) (mapping.translatedTarget origin) :=
  ⟨mapping.data.arrows origin, ⟨mapping.arrowTyped origin⟩⟩

def precompose (mapping : Translation signature next)
    (assignment : Assignment D nextSymbols E) (realization : Realization next assignment) :
    Assignment C symbols E where
  base := mapping.data.base ⋙ assignment.base
  object origin := objectValue assignment realization (mapping.translatedObject origin)
  arrow origin := ⟨objectValue assignment realization (mapping.translatedSource origin),
    objectValue assignment realization (mapping.translatedTarget origin),
    rawArrowValue assignment realization (mapping.translatedArrow origin)⟩

mutual

theorem evaluateObjectLift_precompose (mapping : Translation signature next)
    (assignment : Assignment D nextSymbols E) (realization : Realization next assignment) : (code : ObjectCode C symbols) →
    assignment.evaluateObjectLift (code.translate mapping.data) =
      (mapping.precompose assignment realization).evaluateObjectLift code
  | .base _ => rfl
  | .name origin => by
      change ULift.up (assignment.evaluateObject (mapping.data.objects origin)) =
        ULift.up (some (objectValue assignment realization (mapping.translatedObject origin)))
      exact congrArg ULift.up (objectValue_readout assignment realization (mapping.translatedObject origin))
  | .terminal => rfl
  | .product _ _ => by
      simp only [ObjectCode.translate, Assignment.evaluateObjectLift,
        evaluateObjectLift_precompose mapping assignment realization]
  | .exponential _ _ => by
      simp only [ObjectCode.translate, Assignment.evaluateObjectLift,
        evaluateObjectLift_precompose mapping assignment realization]
  | .equalizer _ _ _ _ => by
      simp only [ObjectCode.translate, Assignment.evaluateObjectLift,
        evaluateObjectLift_precompose mapping assignment realization,
        evaluateArrow_precompose mapping assignment realization]

theorem evaluateArrow_precompose (mapping : Translation signature next)
    (assignment : Assignment D nextSymbols E) (realization : Realization next assignment) : (code : ArrowCode C symbols) →
    assignment.evaluateArrow (code.translate mapping.data) =
      (mapping.precompose assignment realization).evaluateArrow code
  | .base _ => rfl
  | .name origin =>
      rawArrowValue_readout assignment realization (mapping.translatedArrow origin)
  | .identity _ => by
      simp only [ArrowCode.translate, Assignment.evaluateArrow,
        evaluateObjectLift_precompose mapping assignment realization]
  | .compose _ _ => by
      simp only [ArrowCode.translate, Assignment.evaluateArrow,
        evaluateArrow_precompose mapping assignment realization]
  | .terminal _ => by
      simp only [ArrowCode.translate, Assignment.evaluateArrow,
        evaluateObjectLift_precompose mapping assignment realization]
  | .first _ _ => by
      simp only [ArrowCode.translate, Assignment.evaluateArrow,
        evaluateObjectLift_precompose mapping assignment realization]
  | .second _ _ => by
      simp only [ArrowCode.translate, Assignment.evaluateArrow,
        evaluateObjectLift_precompose mapping assignment realization]
  | .pair _ _ => by
      simp only [ArrowCode.translate, Assignment.evaluateArrow,
        evaluateArrow_precompose mapping assignment realization]
  | .evaluation _ _ => by
      simp only [ArrowCode.translate, Assignment.evaluateArrow,
        evaluateObjectLift_precompose mapping assignment realization]
  | .curry _ _ _ _ => by
      simp only [ArrowCode.translate, Assignment.evaluateArrow,
        evaluateObjectLift_precompose mapping assignment realization,
        evaluateArrow_precompose mapping assignment realization]
  | .equalizerArrow _ _ _ _ => by
      simp only [ArrowCode.translate, Assignment.evaluateArrow,
        evaluateObjectLift_precompose mapping assignment realization,
        evaluateArrow_precompose mapping assignment realization]
  | .equalizerLift _ _ _ _ _ _ => by
      simp only [ArrowCode.translate, Assignment.evaluateArrow,
        evaluateObjectLift_precompose mapping assignment realization,
        evaluateArrow_precompose mapping assignment realization]

end

variable (mapping : Translation signature next) (assignment : Assignment D nextSymbols E)
variable (realization : Realization next assignment)

theorem evaluateObject_precompose (code : ObjectCode C symbols) :
    assignment.evaluateObject (code.translate mapping.data) =
      (mapping.precompose assignment realization).evaluateObject code :=
  congrArg ULift.down (mapping.evaluateObjectLift_precompose assignment realization code)

theorem realization_precompose :
    Realization signature (mapping.precompose assignment realization) where
  source origin :=
    (mapping.evaluateObject_precompose assignment realization (signature.source origin)).symm.trans
      (objectValue_readout assignment realization (mapping.translatedSource origin))
  target origin :=
    (mapping.evaluateObject_precompose assignment realization (signature.target origin)).symm.trans
      (objectValue_readout assignment realization (mapping.translatedTarget origin))
  equation origin := by
    obtain ⟨value, source, target, before, after⟩ :=
      sound assignment realization (mapping.equationTyped origin)
    exact ⟨value,
      (mapping.evaluateObject_precompose assignment realization (signature.equationSource origin)).symm.trans source,
      (mapping.evaluateObject_precompose assignment realization (signature.equationTarget origin)).symm.trans target,
      (mapping.evaluateArrow_precompose assignment realization (signature.left origin)).symm.trans before,
      (mapping.evaluateArrow_precompose assignment realization (signature.right origin)).symm.trans after⟩

theorem objectValue_precompose
    (object : GeneratedCategory.Object signature) :
    objectValue assignment realization (mapping.object object) =
      objectValue (mapping.precompose assignment realization) (mapping.realization_precompose assignment realization)
        object := by
  have mapped := objectValue_readout assignment realization (mapping.object object)
  have original := objectValue_readout (mapping.precompose assignment realization)
    (mapping.realization_precompose assignment realization) object
  exact Option.some.inj
    (mapped.symm.trans ((mapping.evaluateObject_precompose assignment realization object.code).trans original))

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

theorem rawArrowValue_precompose
    {source target : GeneratedCategory.Object signature}
    (arrow : GeneratedCategory.RawHom source target) :
    HEq (rawArrowValue assignment realization (mapping.rawArrow arrow))
      (rawArrowValue (mapping.precompose assignment realization)
        (mapping.realization_precompose assignment realization) arrow) := by
  have mapped := rawArrowValue_readout assignment realization (mapping.rawArrow arrow)
  have original := rawArrowValue_readout (mapping.precompose assignment realization)
    (mapping.realization_precompose assignment realization) arrow
  exact arrowValue_heq (Option.some.inj
    (mapped.symm.trans ((mapping.evaluateArrow_precompose assignment realization arrow.code).trans original)))

theorem functor_precompose :
    mapping.functor ⋙ Interpretation.functor assignment realization =
      Interpretation.functor (mapping.precompose assignment realization)
        (mapping.realization_precompose assignment realization) := by
  refine _root_.CategoryTheory.Functor.hext
    (F := mapping.functor ⋙ Interpretation.functor assignment realization)
    (G := Interpretation.functor (mapping.precompose assignment realization)
      (mapping.realization_precompose assignment realization))
    (mapping.objectValue_precompose assignment realization) ?_
  intro source target arrow
  refine Quotient.inductionOn arrow ?_
  intro representative
  exact mapping.rawArrowValue_precompose assignment realization representative

end Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation
