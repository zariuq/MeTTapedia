import Mettapedia.CategoryTheory.RelativeClosedSyntaxArrowInterpretation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxEquationInterpretation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxSignatureMapComposition
import Mettapedia.CategoryTheory.RelativeClosedSyntaxInterpretationReadout

/-!
# Independently named arrows with authored defining expressions

Each declaration retains a formed raw domain, codomain and complete body.
The extended syntax keeps the new name separately from its defining
equation. Independent target arrows extend a realized interpretation exactly
when their complete values agree with the independently evaluated bodies.
All original expressions and quotient arrows are recovered by restriction.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.DefinitionExtension

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory Interpretation

universe k w z
variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable (original : Signature (C := C) (symbols := symbols))

structure Declaration where
  source : Object original
  target : Object original
  body : RawHom source target

variable {Index : Type k} (declarations : Index → Declaration original)

def arrowDeclaration (origin : Index) : ArrowExtension.Declaration original :=
  ⟨(declarations origin).source, (declarations origin).target⟩

def arrowSignature := ArrowExtension.extend original (arrowDeclaration original declarations)
def arrowInclusion := ArrowExtension.inclusion original (arrowDeclaration original declarations)
def primitive (origin : Index) :=
  ArrowExtension.generator original (arrowDeclaration original declarations) origin

def definingDeclaration (origin : Index) : EquationExtension.Declaration (arrowSignature original declarations) where
  source := (arrowInclusion original declarations).object (declarations origin).source
  target := (arrowInclusion original declarations).object (declarations origin).target
  left := primitive original declarations origin
  right := (arrowInclusion original declarations).rawArrow (declarations origin).body

def signature := EquationExtension.extend (arrowSignature original declarations)
  (definingDeclaration original declarations)
def definingInclusion := EquationExtension.inclusion (arrowSignature original declarations)
  (definingDeclaration original declarations)
def inclusion := (arrowInclusion original declarations).compose (definingInclusion original declarations)

def headers (formed : HeaderFormation original) : HeaderFormation (signature original declarations) :=
  EquationExtension.headers (arrowSignature original declarations) (definingDeclaration original declarations)
    (ArrowExtension.headers original (arrowDeclaration original declarations) formed)

def namedRaw (origin : Index) := (definingInclusion original declarations).rawArrow
  (primitive original declarations origin)

def definedRaw (origin : Index) := (definingInclusion original declarations).rawArrow
  (definingDeclaration original declarations origin).right

theorem named_eq_body (origin : Index) :
    classOf (namedRaw original declarations origin) =
      classOf (definedRaw original declarations origin) :=
  EquationExtension.equation_class (arrowSignature original declarations)
    (definingDeclaration original declarations) origin

variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (meanings : Assignment C symbols D) (values : Index → ArrowValue D)

def arrowAssignment := ArrowExtension.extendAssignment meanings values
def assignment := EquationExtension.extendAssignment (Index := Index) (arrowAssignment meanings values)

omit [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D] in
theorem restricted_assignment : (inclusion original declarations).precompose (assignment meanings values) =
    meanings := by
  cases meanings
  rfl

theorem evaluate_object_original (code : ObjectCode C symbols) :
    (assignment meanings values).evaluateObject
      (code.map (inclusion original declarations).base (inclusion original declarations).objects
        (inclusion original declarations).arrows) =
      meanings.evaluateObject code :=
  ((inclusion original declarations).evaluateObject_precompose (assignment meanings values) code).trans
    (congrArg (fun supplied : Assignment C symbols D => supplied.evaluateObject code)
      (restricted_assignment original declarations meanings values))

theorem evaluate_arrow_original (code : ArrowCode C symbols) :
    (assignment meanings values).evaluateArrow
      (code.map (inclusion original declarations).base (inclusion original declarations).objects
        (inclusion original declarations).arrows) =
      meanings.evaluateArrow code :=
  ((inclusion original declarations).evaluateArrow_precompose (assignment meanings values) code).trans
    (congrArg (fun supplied : Assignment C symbols D => supplied.evaluateArrow code)
      (restricted_assignment original declarations meanings values))

variable (realized : Realization original meanings)

def expected (origin : Index) : ArrowValue D :=
  ⟨objectValue meanings realized (declarations origin).source,
    objectValue meanings realized (declarations origin).target,
    rawArrowValue meanings realized (declarations origin).body⟩

theorem expected_read (origin : Index) :
    meanings.evaluateArrow (declarations origin).body.code =
      some (expected original declarations meanings realized origin) :=
  rawArrowValue_readout meanings realized (declarations origin).body

def LocalAdmission : Prop := ∀ origin, values origin = expected original declarations meanings realized origin

theorem added_headers (admitted : LocalAdmission original declarations meanings values realized) :
    ArrowExtension.AddedAdmission original (arrowDeclaration original declarations) meanings values where
  source origin := by
    rw [admitted origin]
    exact objectValue_readout meanings realized (declarations origin).source
  target origin := by
    rw [admitted origin]
    exact objectValue_readout meanings realized (declarations origin).target

theorem arrow_realized (admitted : LocalAdmission original declarations meanings values realized) :
    Realization (arrowSignature original declarations) (arrowAssignment meanings values) :=
  ArrowExtension.extended_realization original (arrowDeclaration original declarations) meanings values
    realized (added_headers original declarations meanings values realized admitted)

theorem defining_satisfied (admitted : LocalAdmission original declarations meanings values realized) :
    EquationExtension.Satisfies (arrowSignature original declarations) (definingDeclaration original declarations)
      (arrowAssignment meanings values) (arrow_realized original declarations meanings values realized admitted) := by
  intro origin
  have first := functor_map_heq (arrowAssignment meanings values)
    (arrow_realized original declarations meanings values realized admitted)
    (primitive original declarations origin) (values origin).arrow rfl
  have bodyRead := (ArrowExtension.evaluate_arrow_original original (arrowDeclaration original declarations)
    meanings values (declarations origin).body.code).trans
      (expected_read original declarations meanings realized origin)
  have second := functor_map_heq (arrowAssignment meanings values)
    (arrow_realized original declarations meanings values realized admitted)
    (definingDeclaration original declarations origin).right
    (expected original declarations meanings realized origin).arrow bodyRead
  exact eq_of_heq (first.trans ((ArrowValue.arrows_heq (admitted origin)).trans second.symm))

theorem extended_realization (admitted : LocalAdmission original declarations meanings values realized) :
    Realization (signature original declarations) (assignment meanings values) :=
  EquationExtension.extended_realization (arrowSignature original declarations)
    (definingDeclaration original declarations) (arrowAssignment meanings values)
    (arrow_realized original declarations meanings values realized admitted)
    (defining_satisfied original declarations meanings values realized admitted)

theorem necessary_admission (extended : Realization (signature original declarations) (assignment meanings values)) :
    LocalAdmission original declarations meanings values realized := by
  intro origin
  obtain ⟨value, _, _, first, second⟩ := extended.equation (Sum.inr origin)
  have leftRead := (EquationExtension.evaluate_arrow_original (arrowSignature original declarations)
    (definingDeclaration original declarations) (arrowAssignment meanings values)
    (primitive original declarations origin).code).trans
      (show (arrowAssignment meanings values).evaluateArrow (primitive original declarations origin).code =
        some (values origin) from rfl)
  have rightRead := (EquationExtension.evaluate_arrow_original (arrowSignature original declarations)
    (definingDeclaration original declarations) (arrowAssignment meanings values)
    (definingDeclaration original declarations origin).right.code).trans
      ((ArrowExtension.evaluate_arrow_original original (arrowDeclaration original declarations)
        meanings values (declarations origin).body.code).trans
          (expected_read original declarations meanings realized origin))
  exact Option.some.inj (leftRead.symm.trans (first.trans (second.symm.trans rightRead)))

theorem realization_iff :
    Realization (signature original declarations) (assignment meanings values) ↔
      LocalAdmission original declarations meanings values realized :=
  ⟨necessary_admission original declarations meanings values realized,
    extended_realization original declarations meanings values realized⟩

theorem complete_restriction (admitted : LocalAdmission original declarations meanings values realized) :
    (inclusion original declarations).functor ⋙ Interpretation.functor (assignment meanings values)
      (extended_realization original declarations meanings values realized admitted) =
        Interpretation.functor meanings realized := by
  simpa only [restricted_assignment] using (inclusion original declarations).functor_precompose
    (assignment meanings values) (extended_realization original declarations meanings values realized admitted)

theorem named_read (origin : Index) :
    (assignment meanings values).evaluateArrow (namedRaw original declarations origin).code =
      some (values origin) :=
  (EquationExtension.evaluate_arrow_original (arrowSignature original declarations)
    (definingDeclaration original declarations) (arrowAssignment meanings values) _).trans rfl

end Mettapedia.CategoryTheory.RelativeClosedSyntax.DefinitionExtension
