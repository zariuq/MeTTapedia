import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryRulePresentation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxArrowInterpretation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxEquationAdmission

/-!
# Exact semantic admission of operational evidence declarations

Independently supplied firing functions act on the complete authored premise
objects. Structural evaluation computes both endpoint equations. The entire
rule presentation is realized exactly when every firing function has the
independently interpreted source and target. The actual generated firing
arrow reads back that complete function, and the entire original theory
is recovered on restriction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedInternalCategory.RuleInterpretation

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory Interpretation

universe k w z

variable {C : Type k} [Category.{k} C] (vertex : C)
variable {D : Type k} [Category.{k} D] {symbols : Symbols.{k}}
variable {original : Signature (C := D) (symbols := symbols)}
variable (categoryMap : SignatureMap (Presentation.signature vertex) original)
variable {Index : Type k} (declarations : Index → RulePresentation.Declaration vertex categoryMap)
variable {E : Type w} [Category.{z} E]
variable [CartesianMonoidalCategory E] [MonoidalClosed E] [HasFiniteLimits E]
variable (meanings : Assignment D symbols E) (realized : Realization original meanings)

abbrev originalFunctor := Interpretation.functor meanings realized

abbrev premise (origin : Index) := objectValue meanings realized (declarations origin).domain
abbrev programs := objectValue meanings realized (NativeCategory.vertexObject vertex categoryMap)
abbrev edges := objectValue meanings realized (NativeCategory.edgeObject vertex categoryMap)

variable (firing : ∀ origin, premise vertex categoryMap declarations meanings realized origin ⟶
  edges vertex categoryMap meanings realized)

def arrowValue (origin : Index) : ArrowValue E :=
  ⟨premise vertex categoryMap declarations meanings realized origin,
    edges vertex categoryMap meanings realized,firing origin⟩

def arrowAssignment := ArrowExtension.extendAssignment meanings
  (arrowValue vertex categoryMap declarations meanings realized firing)

theorem arrowAdmission : ArrowExtension.AddedAdmission original
    (RulePresentation.arrowDeclaration vertex categoryMap declarations) meanings
      (arrowValue vertex categoryMap declarations meanings realized firing) where
  source origin := objectValue_readout meanings realized (declarations origin).domain
  target _ := objectValue_readout meanings realized (NativeCategory.edgeObject vertex categoryMap)

theorem arrowRealization : Realization (RulePresentation.arrowSignature vertex categoryMap declarations)
    (arrowAssignment vertex categoryMap declarations meanings realized firing) :=
  ArrowExtension.extended_realization original (RulePresentation.arrowDeclaration vertex categoryMap declarations)
    meanings (arrowValue vertex categoryMap declarations meanings realized firing) realized
      (arrowAdmission vertex categoryMap declarations meanings realized firing)

def leftValue (origin : Index × Bool) : ArrowValue E :=
  match origin.2 with
  | false => ⟨premise vertex categoryMap declarations meanings realized origin.1,
      programs vertex categoryMap meanings realized,
      firing origin.1 ≫ (originalFunctor meanings realized).map (classOf (NativeCategory.source vertex categoryMap))⟩
  | true => ⟨premise vertex categoryMap declarations meanings realized origin.1,
      programs vertex categoryMap meanings realized,
      firing origin.1 ≫ (originalFunctor meanings realized).map (classOf (NativeCategory.target vertex categoryMap))⟩

def rightValue (origin : Index × Bool) : ArrowValue E :=
  match origin.2 with
  | false => ⟨premise vertex categoryMap declarations meanings realized origin.1,
      programs vertex categoryMap meanings realized,
      (originalFunctor meanings realized).map (classOf (declarations origin.1).before)⟩
  | true => ⟨premise vertex categoryMap declarations meanings realized origin.1,
      programs vertex categoryMap meanings realized,
      (originalFunctor meanings realized).map (classOf (declarations origin.1).after)⟩

theorem left_read (origin : Index × Bool) :
    (arrowAssignment vertex categoryMap declarations meanings realized firing).evaluateArrow
      (RulePresentation.endpointDeclaration vertex categoryMap declarations origin).left.code =
        some (leftValue vertex categoryMap declarations meanings realized firing origin) := by
  cases origin with
  | mk origin side =>
      cases side with
      | false =>
          exact (arrowAssignment vertex categoryMap declarations meanings realized firing).evaluate_compose _ _ rfl
            ((ArrowExtension.evaluate_arrow_original original
              (RulePresentation.arrowDeclaration vertex categoryMap declarations) meanings
                (arrowValue vertex categoryMap declarations meanings realized firing)
                (NativeCategory.source vertex categoryMap).code).trans
                  (functor_complete_readout meanings realized (NativeCategory.source vertex categoryMap)))
      | true =>
          exact (arrowAssignment vertex categoryMap declarations meanings realized firing).evaluate_compose _ _ rfl
            ((ArrowExtension.evaluate_arrow_original original
              (RulePresentation.arrowDeclaration vertex categoryMap declarations) meanings
                (arrowValue vertex categoryMap declarations meanings realized firing)
                (NativeCategory.target vertex categoryMap).code).trans
                  (functor_complete_readout meanings realized (NativeCategory.target vertex categoryMap)))

theorem right_read (origin : Index × Bool) :
    (arrowAssignment vertex categoryMap declarations meanings realized firing).evaluateArrow
      (RulePresentation.endpointDeclaration vertex categoryMap declarations origin).right.code =
        some (rightValue vertex categoryMap declarations meanings realized origin) := by
  cases origin with
  | mk origin side =>
      cases side with
      | false =>
          exact (ArrowExtension.evaluate_arrow_original original
            (RulePresentation.arrowDeclaration vertex categoryMap declarations) meanings
              (arrowValue vertex categoryMap declarations meanings realized firing)
              (declarations origin).before.code).trans
                (functor_complete_readout meanings realized (declarations origin).before)
      | true =>
          exact (ArrowExtension.evaluate_arrow_original original
            (RulePresentation.arrowDeclaration vertex categoryMap declarations) meanings
              (arrowValue vertex categoryMap declarations meanings realized firing)
              (declarations origin).after.code).trans
                (functor_complete_readout meanings realized (declarations origin).after)

structure LocalLaws : Prop where
  source (origin : Index) : firing origin ≫
      (originalFunctor meanings realized).map (classOf (NativeCategory.source vertex categoryMap)) =
    (originalFunctor meanings realized).map (classOf (declarations origin).before)
  target (origin : Index) : firing origin ≫
      (originalFunctor meanings realized).map (classOf (NativeCategory.target vertex categoryMap)) =
    (originalFunctor meanings realized).map (classOf (declarations origin).after)

theorem diagrams_iff :
    (∀ origin, leftValue vertex categoryMap declarations meanings realized firing origin =
      rightValue vertex categoryMap declarations meanings realized origin) ↔
        LocalLaws vertex categoryMap declarations meanings realized firing := by
  constructor
  · intro diagrams
    exact ⟨fun origin => ArrowValue.arrow_injective (diagrams (origin,false)),
      fun origin => ArrowValue.arrow_injective (diagrams (origin,true))⟩
  · intro laws origin
    cases origin with
    | mk origin side =>
        cases side with
        | false => exact congrArg (fun arrow => (⟨_,_,arrow⟩ : ArrowValue E)) (laws.source origin)
        | true => exact congrArg (fun arrow => (⟨_,_,arrow⟩ : ArrowValue E)) (laws.target origin)

def assignment : Assignment D
    (EquationExtension.extendedSymbols
      (ArrowExtension.extendedSymbols symbols Index) (Index × Bool)) E :=
  EquationExtension.extendAssignment (arrowAssignment vertex categoryMap declarations meanings realized firing)

theorem realization_iff : Realization (RulePresentation.signature vertex categoryMap declarations)
    (assignment vertex categoryMap declarations meanings realized firing) ↔
      LocalLaws vertex categoryMap declarations meanings realized firing :=
  (EquationExtension.realization_iff_readouts (RulePresentation.arrowSignature vertex categoryMap declarations)
    (RulePresentation.endpointDeclaration vertex categoryMap declarations)
    (arrowAssignment vertex categoryMap declarations meanings realized firing)
    (arrowRealization vertex categoryMap declarations meanings realized firing)
    (leftValue vertex categoryMap declarations meanings realized firing)
    (rightValue vertex categoryMap declarations meanings realized)
    (left_read vertex categoryMap declarations meanings realized firing)
    (right_read vertex categoryMap declarations meanings realized firing)).trans
      (diagrams_iff vertex categoryMap declarations meanings realized firing)

variable (laws : LocalLaws vertex categoryMap declarations meanings realized firing)

include laws in
theorem realization : Realization (RulePresentation.signature vertex categoryMap declarations)
    (assignment vertex categoryMap declarations meanings realized firing) :=
  (realization_iff vertex categoryMap declarations meanings realized firing).mpr laws

def functor := Interpretation.functor (assignment vertex categoryMap declarations meanings realized firing)
  (realization vertex categoryMap declarations meanings realized firing laws)

theorem complete_arrow_restriction : (RulePresentation.equationInclusion vertex categoryMap declarations).functor ⋙
    functor vertex categoryMap declarations meanings realized firing laws =
      Interpretation.functor (arrowAssignment vertex categoryMap declarations meanings realized firing)
        (arrowRealization vertex categoryMap declarations meanings realized firing) := by
  have satisfied := (EquationExtension.satisfaction_iff_readouts
    (RulePresentation.arrowSignature vertex categoryMap declarations)
    (RulePresentation.endpointDeclaration vertex categoryMap declarations)
    (arrowAssignment vertex categoryMap declarations meanings realized firing)
    (arrowRealization vertex categoryMap declarations meanings realized firing)
    (leftValue vertex categoryMap declarations meanings realized firing)
    (rightValue vertex categoryMap declarations meanings realized)
    (left_read vertex categoryMap declarations meanings realized firing)
    (right_read vertex categoryMap declarations meanings realized firing)).mpr
      ((diagrams_iff vertex categoryMap declarations meanings realized firing).mpr laws)
  exact EquationExtension.complete_restriction
    (RulePresentation.arrowSignature vertex categoryMap declarations)
    (RulePresentation.endpointDeclaration vertex categoryMap declarations)
    (arrowAssignment vertex categoryMap declarations meanings realized firing)
    (arrowRealization vertex categoryMap declarations meanings realized firing) satisfied

theorem complete_original_restriction : (RulePresentation.arrowInclusion vertex categoryMap declarations).functor ⋙
    (RulePresentation.equationInclusion vertex categoryMap declarations).functor ⋙
      functor vertex categoryMap declarations meanings realized firing laws = originalFunctor meanings realized := by
  rw [complete_arrow_restriction]
  exact ArrowExtension.complete_restriction original (RulePresentation.arrowDeclaration vertex categoryMap declarations)
    meanings (arrowValue vertex categoryMap declarations meanings realized firing) realized
      (arrowAdmission vertex categoryMap declarations meanings realized firing)

theorem fire_complete_read (origin : Index) :
    (⟨(functor vertex categoryMap declarations meanings realized firing laws).obj
        (RulePresentation.ruleDomain vertex categoryMap declarations origin),
      (functor vertex categoryMap declarations meanings realized firing laws).obj
        (RulePresentation.edges vertex categoryMap declarations),
      (functor vertex categoryMap declarations meanings realized firing laws).map
        (classOf (RulePresentation.fire vertex categoryMap declarations origin))⟩ : ArrowValue E) =
      arrowValue vertex categoryMap declarations meanings realized firing origin := by
  have complete := functor_complete_readout (assignment vertex categoryMap declarations meanings realized firing)
    (realization vertex categoryMap declarations meanings realized firing laws)
      (RulePresentation.fire vertex categoryMap declarations origin)
  have originalRead := EquationExtension.evaluate_arrow_original
    (RulePresentation.arrowSignature vertex categoryMap declarations)
    (RulePresentation.endpointDeclaration vertex categoryMap declarations)
    (arrowAssignment vertex categoryMap declarations meanings realized firing)
      (RulePresentation.primitive vertex categoryMap declarations origin).code
  exact Option.some.inj (complete.symm.trans originalRead)

end Mettapedia.CategoryTheory.RelativeClosedInternalCategory.RuleInterpretation
