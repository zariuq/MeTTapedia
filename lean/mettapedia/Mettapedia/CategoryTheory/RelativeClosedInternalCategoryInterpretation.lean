import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryEquationReadout
import Mettapedia.CategoryTheory.RelativeClosedSyntaxEquationInterpretation

/-!
# Exact seven-diagram admission of generated categories

The complete target parser computes both sides of all category declarations.
Its admission is equivalent to the independently supplied finite endpoint,
unit and triple diagrams. Restriction recovers every original arrow, while
the diagrams construct the actual target category at all generalized stages.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedInternalCategory.CategoryInterpretation

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory Interpretation

universe k w z

variable {C : Type k} [Category.{k} C] (vertex : C)
variable {D : Type w} [Category.{z} D] [CartesianMonoidalCategory D]
variable [MonoidalClosed D] [HasFiniteLimits D]
variable (base : C ⥤ D) (meaning : Meaning.Operations (base.obj vertex))

def assignment : Assignment C
    (EquationExtension.extendedSymbols (EquationExtension.extendedSymbols symbols
      (ULift.{k} EndpointLaw)) (ULift.{k} Presentation.Law)) D :=
  EquationExtension.extendAssignment (EquationReadout.assignment vertex base meaning)

variable (endpointLaws : Meaning.EndpointLaws vertex base meaning)

include endpointLaws in
theorem endpointRealization : Realization (endpointSignature vertex)
    (EquationReadout.assignment vertex base meaning) :=
  EquationExtension.extended_realization (signature vertex) (endpointDeclaration vertex)
    (Meaning.assignment vertex base meaning) (Meaning.realization vertex base meaning)
    ((Meaning.local_admission_iff vertex base meaning).mpr endpointLaws)

def leftValue (origin : ULift.{k} Presentation.Law) : ArrowValue D :=
  let operations := ModelDiagrams.endpoints vertex base meaning endpointLaws
  let triples := ModelDiagrams.triples vertex base meaning endpointLaws
  match origin.down with
  | .leftUnit => ⟨meaning.edge,meaning.edge,
      InternalCategoryPresentedDiagrams.compose operations (operations.source ≫ operations.unit)
        (𝟙 operations.edge) (by
          change (meaning.source ≫ meaning.unit) ≫ meaning.target = (𝟙 meaning.edge) ≫ meaning.source
          simp only [Category.assoc,endpointLaws.unitTarget,Category.comp_id,Category.id_comp])⟩
  | .rightUnit => ⟨meaning.edge,meaning.edge,
      InternalCategoryPresentedDiagrams.compose operations (𝟙 operations.edge)
        (operations.target ≫ operations.unit) (by
          change (𝟙 meaning.edge) ≫ meaning.target = (meaning.target ≫ meaning.unit) ≫ meaning.source
          simp only [Category.assoc,endpointLaws.unitSource,Category.comp_id,Category.id_comp])⟩
  | .associativity => ⟨triples.pt,meaning.edge,
      InternalCategoryPresentedDiagrams.associateLeft operations triples⟩

def rightValue (origin : ULift.{k} Presentation.Law) : ArrowValue D :=
  match origin.down with
  | .leftUnit => ⟨meaning.edge,meaning.edge,𝟙 meaning.edge⟩
  | .rightUnit => ⟨meaning.edge,meaning.edge,𝟙 meaning.edge⟩
  | .associativity => ⟨(ModelDiagrams.triples vertex base meaning endpointLaws).pt,meaning.edge,
      InternalCategoryPresentedDiagrams.associateRight
        (ModelDiagrams.endpoints vertex base meaning endpointLaws)
        (ModelDiagrams.triples vertex base meaning endpointLaws)⟩

theorem left_read (origin : ULift.{k} Presentation.Law) :
    (EquationReadout.assignment vertex base meaning).evaluateArrow
      (Presentation.declaration vertex origin).left.code =
        some (leftValue vertex base meaning endpointLaws origin) := by
  cases origin with
  | up origin =>
    cases origin with
    | leftUnit =>
      exact (EquationReadout.assignment vertex base meaning).evaluate_compose _ _
        (EquationReadout.unit_left_read vertex base meaning endpointLaws)
        (EquationReadout.composition_read vertex base meaning)
    | rightUnit =>
      exact (EquationReadout.assignment vertex base meaning).evaluate_compose _ _
        (EquationReadout.unit_right_read vertex base meaning endpointLaws)
        (EquationReadout.composition_read vertex base meaning)
    | associativity => exact EquationReadout.associate_left_read vertex base meaning endpointLaws

theorem right_read (origin : ULift.{k} Presentation.Law) :
    (EquationReadout.assignment vertex base meaning).evaluateArrow
      (Presentation.declaration vertex origin).right.code =
        some (rightValue vertex base meaning endpointLaws origin) := by
  cases origin with
  | up origin =>
    cases origin with
    | leftUnit =>
      exact (EquationReadout.assignment vertex base meaning).evaluate_identity
        (EquationReadout.edge_read vertex base meaning)
    | rightUnit =>
      exact (EquationReadout.assignment vertex base meaning).evaluate_identity
        (EquationReadout.edge_read vertex base meaning)
    | associativity => exact EquationReadout.associate_right_read vertex base meaning endpointLaws

theorem local_admission_iff :
    EquationExtension.Satisfies (endpointSignature vertex) (Presentation.declaration vertex)
      (EquationReadout.assignment vertex base meaning) (endpointRealization vertex base meaning endpointLaws) ↔
        ModelDiagrams.LocalLaws vertex base meaning endpointLaws := by
  have diagram (origin : ULift.{k} Presentation.Law) :
      (Interpretation.functor (EquationReadout.assignment vertex base meaning)
        (endpointRealization vertex base meaning endpointLaws)).map
          (classOf (Presentation.declaration vertex origin).left) =
      (Interpretation.functor (EquationReadout.assignment vertex base meaning)
        (endpointRealization vertex base meaning endpointLaws)).map
          (classOf (Presentation.declaration vertex origin).right) ↔
        leftValue vertex base meaning endpointLaws origin = rightValue vertex base meaning endpointLaws origin := by
    have left := Interpretation.functor_complete_readout (EquationReadout.assignment vertex base meaning)
      (endpointRealization vertex base meaning endpointLaws) (Presentation.declaration vertex origin).left
    have right := Interpretation.functor_complete_readout (EquationReadout.assignment vertex base meaning)
      (endpointRealization vertex base meaning endpointLaws) (Presentation.declaration vertex origin).right
    have leftSame := Option.some.inj (left.symm.trans (left_read vertex base meaning endpointLaws origin))
    have rightSame := Option.some.inj (right.symm.trans (right_read vertex base meaning endpointLaws origin))
    constructor
    · intro same
      exact leftSame.symm.trans ((congrArg (fun arrow => (⟨_,_,arrow⟩ : ArrowValue D)) same).trans rightSame)
    · intro same
      exact ArrowValue.arrow_injective (leftSame.trans (same.trans rightSame.symm))
  constructor
  · intro satisfied
    exact ⟨ArrowValue.arrow_injective ((diagram (ULift.up Presentation.Law.leftUnit)).mp (satisfied _)),
      ArrowValue.arrow_injective ((diagram (ULift.up Presentation.Law.rightUnit)).mp (satisfied _)),
      ArrowValue.arrow_injective ((diagram (ULift.up Presentation.Law.associativity)).mp (satisfied _))⟩
  · intro laws origin
    apply (diagram origin).mpr
    cases origin with
    | up origin =>
      cases origin with
      | leftUnit => exact congrArg (fun arrow => (⟨_,_,arrow⟩ : ArrowValue D)) laws.leftUnit
      | rightUnit => exact congrArg (fun arrow => (⟨_,_,arrow⟩ : ArrowValue D)) laws.rightUnit
      | associativity => exact congrArg (fun arrow => (⟨_,_,arrow⟩ : ArrowValue D)) laws.associativity

variable (laws : ModelDiagrams.LocalLaws vertex base meaning endpointLaws)

include endpointLaws laws in
theorem realization : Realization (Presentation.signature vertex) (assignment vertex base meaning) :=
  EquationExtension.extended_realization (endpointSignature vertex) (Presentation.declaration vertex)
    (EquationReadout.assignment vertex base meaning) (endpointRealization vertex base meaning endpointLaws)
    ((local_admission_iff vertex base meaning endpointLaws).mpr laws)

def functor : Object (Presentation.signature vertex) ⥤ D :=
  Interpretation.functor (assignment vertex base meaning) (realization vertex base meaning endpointLaws laws)

theorem complete_endpoint_restriction : (Presentation.inclusion vertex).functor ⋙
    functor vertex base meaning endpointLaws laws =
      Interpretation.functor (EquationReadout.assignment vertex base meaning)
        (endpointRealization vertex base meaning endpointLaws) :=
  EquationExtension.complete_restriction (endpointSignature vertex) (Presentation.declaration vertex)
    (EquationReadout.assignment vertex base meaning) (endpointRealization vertex base meaning endpointLaws)
    ((local_admission_iff vertex base meaning endpointLaws).mpr laws)

theorem complete_primitive_restriction :
    (endpointInclusion vertex).functor ⋙ (Presentation.inclusion vertex).functor ⋙
      functor vertex base meaning endpointLaws laws =
        Interpretation.functor (Meaning.assignment vertex base meaning) (Meaning.realization vertex base meaning) := by
  rw [complete_endpoint_restriction]
  exact EquationExtension.complete_restriction (signature vertex) (endpointDeclaration vertex)
    (Meaning.assignment vertex base meaning) (Meaning.realization vertex base meaning)
    ((Meaning.local_admission_iff vertex base meaning).mpr endpointLaws)

omit endpointLaws laws in
theorem seven_diagram_admission_iff :
    Realization (Presentation.signature vertex) (assignment vertex base meaning) ↔
      ∃ endpointLaws : Meaning.EndpointLaws vertex base meaning,
        ModelDiagrams.LocalLaws vertex base meaning endpointLaws := by
  constructor
  · intro admitted
    have restricted := (Presentation.inclusion vertex).realization_precompose
      (assignment vertex base meaning) admitted
    have original : Realization (endpointSignature vertex) (EquationReadout.assignment vertex base meaning) := by
      simpa only [Presentation.inclusion, assignment, EquationExtension.restricted_assignment] using restricted
    have endpointLaws := (Meaning.endpoint_realization_iff vertex base meaning).mp original
    refine ⟨endpointLaws,(local_admission_iff vertex base meaning endpointLaws).mp ?_⟩
    exact EquationExtension.necessary_satisfaction (endpointSignature vertex) (Presentation.declaration vertex)
      (EquationReadout.assignment vertex base meaning) (endpointRealization vertex base meaning endpointLaws) admitted
  · rintro ⟨endpointLaws,laws⟩
    exact realization vertex base meaning endpointLaws laws

end Mettapedia.CategoryTheory.RelativeClosedInternalCategory.CategoryInterpretation
