import Mettapedia.CategoryTheory.RelativeClosedBaseWeakInterpretation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxBaseExtensionPreservation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxSignatureMapInterpretation

/-!
# Augmented interpretations over arbitrary weak closed base maps

An independently supplied assignment over a genuine finite-limit closed base
map is extended by the earned base-comparison meanings. The original
declarations, including their complete arrow values and origins, are retained.
Each new local inverse equation and every old declaration equation is proved.

Both independently evaluated diagram restrictions are exact. No literal
equality between the source and target's terminal, product, exponential or
equalizer choices is required. This interpretation extension does not itself
construct the free/forgetful action or its biadjunction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseExtension.WeakExtension

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Interpretation

universe k w

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable {signature : Signature (C := C) (symbols := symbols)}
variable (meanings : Assignment C symbols D)
variable [PreservesFiniteLimits meanings.base] [MonoidalClosedFunctor meanings.base]

def assignment : Assignment C (extendedSymbols C symbols) D where
  base := meanings.base
  object origin := meanings.object origin.down
  arrow origin := match origin with
    | .inl choice => (BaseComparisons.WeakDiagram.assignment meanings.base).arrow choice
    | .inr name => meanings.arrow name.down

omit [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
  [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D] in
private theorem assignment_ext {names : Symbols} {first second : Assignment C names D}
    (base : first.base = second.base) (objects : first.object = second.object)
    (arrows : first.arrow = second.arrow) : first = second := by
  cases first
  cases second
  cases base
  cases objects
  cases arrows
  rfl

theorem original_precompose : (originalMap signature).precompose (assignment meanings) = meanings := by
  exact assignment_ext (Functor.id_comp meanings.base) rfl rfl

theorem comparison_precompose : (comparisonMap signature).precompose (assignment meanings) =
    BaseComparisons.WeakDiagram.assignment meanings.base := by
  refine assignment_ext (Functor.id_comp meanings.base) ?_ rfl
  funext origin
  exact origin.down.elim

include signature in
theorem original_object_read (code : ObjectCode C symbols) :
    (assignment meanings).evaluateObject (originalObjectCode code) = meanings.evaluateObject code :=
  ((originalMap signature).evaluateObject_precompose (assignment meanings) code).trans
    (congrArg (fun interpretation : Assignment C symbols D => interpretation.evaluateObject code)
      (original_precompose (signature := signature) meanings))

include signature in
theorem original_arrow_read (code : ArrowCode C symbols) :
    (assignment meanings).evaluateArrow (originalArrowCode code) = meanings.evaluateArrow code :=
  ((originalMap signature).evaluateArrow_precompose (assignment meanings) code).trans
    (congrArg (fun interpretation : Assignment C symbols D => interpretation.evaluateArrow code)
      (original_precompose (signature := signature) meanings))

include signature in
theorem comparison_object_read (code : ObjectCode C (BaseComparisons.symbols C)) :
    (assignment meanings).evaluateObject (comparisonObjectCode code) =
      (BaseComparisons.WeakDiagram.assignment meanings.base).evaluateObject code :=
  ((comparisonMap signature).evaluateObject_precompose (assignment meanings) code).trans
    (congrArg (fun interpretation : Assignment C (BaseComparisons.symbols C) D =>
      interpretation.evaluateObject code) (comparison_precompose (signature := signature) meanings))

include signature in
theorem comparison_arrow_read (code : ArrowCode C (BaseComparisons.symbols C)) :
    (assignment meanings).evaluateArrow (comparisonArrowCode code) =
      (BaseComparisons.WeakDiagram.assignment meanings.base).evaluateArrow code :=
  ((comparisonMap signature).evaluateArrow_precompose (assignment meanings) code).trans
    (congrArg (fun interpretation : Assignment C (BaseComparisons.symbols C) D =>
      interpretation.evaluateArrow code) (comparison_precompose (signature := signature) meanings))

theorem realization (original : Realization signature meanings) :
    Realization (extend signature) (assignment meanings) where
  source origin := by
    cases origin with
    | inl choice =>
        exact (comparison_object_read (signature := signature) meanings
          (BaseComparisons.sourceCode choice)).trans
            ((BaseComparisons.WeakDiagram.realization meanings.base).source choice)
    | inr name =>
        exact (original_object_read (signature := signature) meanings
          (signature.source name.down)).trans (original.source name.down)
  target origin := by
    cases origin with
    | inl choice =>
        exact (comparison_object_read (signature := signature) meanings
          (BaseComparisons.targetCode choice)).trans
            ((BaseComparisons.WeakDiagram.realization meanings.base).target choice)
    | inr name =>
        exact (original_object_read (signature := signature) meanings
          (signature.target name.down)).trans (original.target name.down)
  equation origin := by
    cases origin with
    | inl localOrigin =>
        obtain ⟨value, source, target, before, after⟩ :=
          (BaseComparisons.WeakDiagram.realization meanings.base).equation localOrigin
        exact ⟨value,
          (comparison_object_read (signature := signature) meanings
            (BaseComparisons.equationObject localOrigin)).trans source,
          (comparison_object_read (signature := signature) meanings
            (BaseComparisons.equationObject localOrigin)).trans target,
          (comparison_arrow_read (signature := signature) meanings
            (BaseComparisons.leftCode localOrigin)).trans before,
          (comparison_arrow_read (signature := signature) meanings
            (BaseComparisons.rightCode localOrigin)).trans after⟩
    | inr name =>
        obtain ⟨value, source, target, before, after⟩ := original.equation name.down
        exact ⟨value,
          (original_object_read (signature := signature) meanings
            (signature.equationSource name.down)).trans source,
          (original_object_read (signature := signature) meanings
            (signature.equationTarget name.down)).trans target,
          (original_arrow_read (signature := signature) meanings
            (signature.left name.down)).trans before,
          (original_arrow_read (signature := signature) meanings
            (signature.right name.down)).trans after⟩

omit [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C] in
private theorem functor_assignment_eq {names : Symbols.{k}}
    {presentation : Signature (C := C) (symbols := names)}
    (first second : Assignment C names D)
    (before : Realization presentation first) (after : Realization presentation second)
    (same : first = second) : Interpretation.functor first before =
      Interpretation.functor second after := by
  subst second
  rfl

theorem original_diagram_readback (original : Realization signature meanings) :
    (originalMap signature).functor ⋙
      Interpretation.functor (assignment meanings) (realization meanings original) =
        Interpretation.functor meanings original :=
  ((originalMap signature).functor_precompose (assignment meanings)
    (realization meanings original)).trans
      (functor_assignment_eq _ _ _ original (original_precompose (signature := signature) meanings))

theorem comparison_diagram_readback (original : Realization signature meanings) :
    (comparisonMap signature).functor ⋙
      Interpretation.functor (assignment meanings) (realization meanings original) =
        BaseComparisons.WeakDiagram.interpretation meanings.base :=
  ((comparisonMap signature).functor_precompose (assignment meanings)
    (realization meanings original)).trans
      (functor_assignment_eq _ _ _ (BaseComparisons.WeakDiagram.realization meanings.base)
        (comparison_precompose (signature := signature) meanings))

end Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseExtension.WeakExtension
