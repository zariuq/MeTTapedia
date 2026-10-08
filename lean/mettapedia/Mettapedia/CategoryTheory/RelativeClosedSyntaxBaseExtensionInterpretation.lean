import Mettapedia.CategoryTheory.RelativeClosedSyntaxBaseExtensionPreservation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxSignatureMapInterpretation
import Mettapedia.CategoryTheory.RelativeClosedBaseInterpretation

/-!
# Native consistency of an arbitrary augmented presentation

An independent interpretation over the identity base extends to the local
base-comparison declarations. Original meanings and origins are retained;
the new inverse arrows are interpreted by the actual native identities.
Both raw evaluator comparisons and every local declaration equation are
proved. This gives a consistency witness and complete old-diagram readouts,
rather than a relative free-extension universal property.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseExtension.NativeExtension

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Interpretation

universe u v a

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
variable (signature : Signature (C := C) (symbols := symbols))

def assignment (meanings : Assignment C symbols C) :
    Assignment C (extendedSymbols C symbols) C where
  base := Functor.id C
  object origin := meanings.object origin.down
  arrow origin := match origin with
    | .inl choice =>
        ⟨BaseComparisons.selected choice, BaseComparisons.selected choice,
          𝟙 (BaseComparisons.selected choice)⟩
    | .inr name => meanings.arrow name.down

omit [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C] in
private theorem assignment_eq {names : Symbols} {first second : Assignment C names C}
    (base : first.base = second.base) (objects : first.object = second.object)
    (arrows : first.arrow = second.arrow) : first = second := by
  cases first
  cases second
  dsimp at base objects arrows
  cases base
  cases objects
  cases arrows
  rfl

variable {signature} (meanings : Assignment C symbols C)

theorem original_precompose (baseIdentity : meanings.base = Functor.id C) :
    (originalMap signature).precompose (assignment meanings) = meanings := by
  refine assignment_eq ?_ rfl rfl
  exact (Functor.id_comp (Functor.id C)).trans baseIdentity.symm

theorem comparison_precompose :
    (comparisonMap signature).precompose (assignment meanings) =
      BaseComparisons.NativeDiagram.assignment (C := C) := by
  refine assignment_eq (Functor.id_comp (Functor.id C)) ?_ rfl
  funext origin
  exact origin.down.elim

theorem original_object_read (signature : Signature (C := C) (symbols := symbols))
    (baseIdentity : meanings.base = Functor.id C)
    (code : ObjectCode C symbols) :
    (assignment meanings).evaluateObject (originalObjectCode code) = meanings.evaluateObject code :=
  ((originalMap signature).evaluateObject_precompose (assignment meanings) code).trans
    (congrArg (fun interpretation : Assignment C symbols C => interpretation.evaluateObject code)
      (original_precompose meanings baseIdentity))

theorem original_arrow_read (signature : Signature (C := C) (symbols := symbols))
    (baseIdentity : meanings.base = Functor.id C)
    (code : ArrowCode C symbols) :
    (assignment meanings).evaluateArrow (originalArrowCode code) = meanings.evaluateArrow code :=
  ((originalMap signature).evaluateArrow_precompose (assignment meanings) code).trans
    (congrArg (fun interpretation : Assignment C symbols C => interpretation.evaluateArrow code)
      (original_precompose meanings baseIdentity))

theorem comparison_object_read (signature : Signature (C := C) (symbols := symbols))
    (code : ObjectCode C (BaseComparisons.symbols C)) :
    (assignment meanings).evaluateObject (comparisonObjectCode code) =
      (BaseComparisons.NativeDiagram.assignment (C := C)).evaluateObject code :=
  ((comparisonMap signature).evaluateObject_precompose (assignment meanings) code).trans
    (congrArg (fun interpretation : Assignment C (BaseComparisons.symbols C) C =>
      interpretation.evaluateObject code) (comparison_precompose meanings))

theorem comparison_arrow_read (signature : Signature (C := C) (symbols := symbols))
    (code : ArrowCode C (BaseComparisons.symbols C)) :
    (assignment meanings).evaluateArrow (comparisonArrowCode code) =
      (BaseComparisons.NativeDiagram.assignment (C := C)).evaluateArrow code :=
  ((comparisonMap signature).evaluateArrow_precompose (assignment meanings) code).trans
    (congrArg (fun interpretation : Assignment C (BaseComparisons.symbols C) C =>
      interpretation.evaluateArrow code) (comparison_precompose meanings))

theorem realization (baseIdentity : meanings.base = Functor.id C)
    (original : Realization signature meanings) :
    Realization (extend signature) (assignment meanings) where
  source origin := by
    cases origin with
    | inl choice =>
        exact (comparison_object_read meanings signature (BaseComparisons.sourceCode choice)).trans
          (BaseComparisons.NativeDiagram.source_read choice)
    | inr name =>
        exact (original_object_read meanings signature baseIdentity (signature.source name.down)).trans
          (original.source name.down)
  target origin := by
    cases origin with
    | inl choice =>
        exact (comparison_object_read meanings signature (BaseComparisons.targetCode choice)).trans
          (BaseComparisons.NativeDiagram.target_read choice)
    | inr name =>
        exact (original_object_read meanings signature baseIdentity (signature.target name.down)).trans
          (original.target name.down)
  equation origin := by
    cases origin with
    | inl localOrigin =>
        obtain ⟨value, source, target, before, after⟩ :=
          (BaseComparisons.NativeDiagram.realization (C := C)).equation localOrigin
        exact ⟨value,
          (comparison_object_read meanings signature (BaseComparisons.equationObject localOrigin)).trans source,
          (comparison_object_read meanings signature (BaseComparisons.equationObject localOrigin)).trans target,
          (comparison_arrow_read meanings signature (BaseComparisons.leftCode localOrigin)).trans before,
          (comparison_arrow_read meanings signature (BaseComparisons.rightCode localOrigin)).trans after⟩
    | inr name =>
        obtain ⟨value, source, target, before, after⟩ := original.equation name.down
        exact ⟨value,
          (original_object_read meanings signature baseIdentity (signature.equationSource name.down)).trans source,
          (original_object_read meanings signature baseIdentity (signature.equationTarget name.down)).trans target,
          (original_arrow_read meanings signature baseIdentity (signature.left name.down)).trans before,
          (original_arrow_read meanings signature baseIdentity (signature.right name.down)).trans after⟩

private theorem functor_assignment_eq (first second : Assignment C symbols C)
    (before : Realization signature first) (after : Realization signature second)
    (same : first = second) : Interpretation.functor first before =
      Interpretation.functor second after := by
  subst second
  rfl

theorem original_diagram_readback (baseIdentity : meanings.base = Functor.id C)
    (original : Realization signature meanings) :
    (originalMap signature).functor ⋙
      Interpretation.functor (assignment meanings) (realization meanings baseIdentity original) =
        Interpretation.functor meanings original :=
  ((originalMap signature).functor_precompose (assignment meanings)
    (realization meanings baseIdentity original)).trans
    (functor_assignment_eq _ _ _ original (original_precompose meanings baseIdentity))

end Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseExtension.NativeExtension
