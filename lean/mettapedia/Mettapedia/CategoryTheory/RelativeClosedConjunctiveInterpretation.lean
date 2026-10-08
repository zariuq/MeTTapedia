import Mettapedia.CategoryTheory.RelativeClosedConjunctivePresentation
import Mettapedia.CategoryTheory.InternalConjunctiveObject
import Mettapedia.CategoryTheory.RelativeClosedSyntaxEquationInterpretation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxBaseExtensionModels

/-!
# Independent meanings and exact local logical admission

The target supplies a proposition object and two complete operation arrows.
Four finite arrow diagrams state the local conjunctive laws. The structural
evaluator computes every side of the authored equation pairs independently.
Its local realization exists exactly when those diagrams commute.

A weak finite-limit closed base then earns the native interpretation of the
extended theory, retaining the original base functor and complete operation
values. No whole-expression soundness or free-extension law is an input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedConjunctive.Interpretation

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open RelativeClosedSyntax RelativeClosedSyntax.Interpretation

universe k w

variable {C : Type k} [Category.{k} C]
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]

abbrev Meaning (D : Type w) [Category.{k} D] [CartesianMonoidalCategory D] :=
  InternalConjunctiveObject.Operations D

variable (base : C ⥤ D) (meaning : Meaning D)

abbrev swapBody := InternalConjunctiveObject.Operations.swapBody meaning

abbrev associateLeft := InternalConjunctiveObject.Operations.associateLeft meaning

abbrev associateRight := InternalConjunctiveObject.Operations.associateRight meaning

abbrev diagonalBody := InternalConjunctiveObject.Operations.diagonalBody meaning

abbrev truthUnitBody := InternalConjunctiveObject.Operations.truthUnitBody meaning

abbrev Laws := InternalConjunctiveObject.Operations.Laws meaning

def assignment : Assignment C (symbols : Symbols.{k}) D where
  base := base
  object _ := meaning.proposition
  arrow origin := match origin.down with
    | .truth => ⟨𝟙_ D, meaning.proposition, meaning.truth⟩
    | .conjunction => ⟨meaning.proposition ⊗ meaning.proposition, meaning.proposition, meaning.conjunction⟩

theorem operations_realized : Realization (signature (C := C)) (assignment base meaning) where
  source origin := by
    cases origin with
    | up origin =>
      cases origin with
      | truth => rfl
      | conjunction => exact Assignment.evaluate_product (assignment base meaning) rfl rfl
  target origin := by
    cases origin with
    | up origin => cases origin <;> rfl
  equation origin := origin.down.elim

def leftValue (origin : ULift.{k} Law) : ArrowValue D :=
  match origin.down with
  | .commutativity => ⟨meaning.proposition ⊗ meaning.proposition, meaning.proposition, swapBody meaning⟩
  | .associativity => ⟨(meaning.proposition ⊗ meaning.proposition) ⊗ meaning.proposition,
      meaning.proposition, associateLeft meaning⟩
  | .idempotence => ⟨meaning.proposition, meaning.proposition, diagonalBody meaning⟩
  | .truthUnit => ⟨meaning.proposition, meaning.proposition, truthUnitBody meaning⟩

def rightValue (origin : ULift.{k} Law) : ArrowValue D :=
  match origin.down with
  | .commutativity => ⟨meaning.proposition ⊗ meaning.proposition, meaning.proposition, meaning.conjunction⟩
  | .associativity => ⟨(meaning.proposition ⊗ meaning.proposition) ⊗ meaning.proposition,
      meaning.proposition, associateRight meaning⟩
  | .idempotence => ⟨meaning.proposition, meaning.proposition, 𝟙 meaning.proposition⟩
  | .truthUnit => ⟨meaning.proposition, meaning.proposition, 𝟙 meaning.proposition⟩

theorem declaration_source_read (origin : ULift.{k} Law) :
    (assignment base meaning).evaluateObject (declaration (C := C) origin).source.code =
      some (leftValue meaning origin).source := by
  cases origin with
  | up origin =>
    cases origin with
    | commutativity => exact Assignment.evaluate_product (assignment base meaning) rfl rfl
    | associativity =>
        exact Assignment.evaluate_product (assignment base meaning)
          (Assignment.evaluate_product (assignment base meaning) rfl rfl) rfl
    | idempotence => rfl
    | truthUnit => rfl

theorem declaration_target_read (origin : ULift.{k} Law) :
    (assignment base meaning).evaluateObject (declaration (C := C) origin).target.code =
      some (leftValue meaning origin).target := by
  cases origin with
  | up origin => cases origin <;> rfl

theorem declaration_left_read (origin : ULift.{k} Law) :
    (assignment base meaning).evaluateArrow (declaration (C := C) origin).left.code =
      some (leftValue meaning origin) := by
  let values := assignment base meaning
  have omegaRead : values.evaluateObject (omegaCode (C := C)) = some meaning.proposition := rfl
  have pairRead := values.evaluate_product omegaRead omegaRead
  have meetRead : values.evaluateArrow (.name (ULift.up Operation.conjunction)) =
      some (⟨meaning.proposition ⊗ meaning.proposition, meaning.proposition, meaning.conjunction⟩ : ArrowValue D) := rfl
  cases origin with
  | up origin =>
    cases origin with
    | commutativity =>
      exact values.evaluate_compose _ _
        (values.evaluate_pair _ _ (values.evaluate_second omegaRead omegaRead) (values.evaluate_first omegaRead omegaRead))
        meetRead
    | associativity =>
      exact values.evaluate_compose _ _
        (values.evaluate_pair _ _
          (values.evaluate_compose _ _ (values.evaluate_first pairRead omegaRead) meetRead)
          (values.evaluate_second pairRead omegaRead)) meetRead
    | idempotence =>
      exact values.evaluate_compose _ _
        (values.evaluate_pair _ _ (values.evaluate_identity omegaRead) (values.evaluate_identity omegaRead)) meetRead
    | truthUnit =>
      have truthRead : values.evaluateArrow (.name (ULift.up Operation.truth)) =
          some (⟨𝟙_ D, meaning.proposition, meaning.truth⟩ : ArrowValue D) := rfl
      exact values.evaluate_compose _ _ (values.evaluate_pair _ _ (values.evaluate_identity omegaRead)
        (values.evaluate_compose _ _ (values.evaluate_terminal_arrow omegaRead) truthRead)) meetRead

theorem declaration_right_read (origin : ULift.{k} Law) :
    (assignment base meaning).evaluateArrow (declaration (C := C) origin).right.code =
      some (rightValue meaning origin) := by
  let values := assignment base meaning
  have omegaRead : values.evaluateObject (omegaCode (C := C)) = some meaning.proposition := rfl
  have pairRead := values.evaluate_product omegaRead omegaRead
  have meetRead : values.evaluateArrow (.name (ULift.up Operation.conjunction)) =
      some (⟨meaning.proposition ⊗ meaning.proposition, meaning.proposition, meaning.conjunction⟩ : ArrowValue D) := rfl
  cases origin with
  | up origin =>
    cases origin with
    | commutativity => exact meetRead
    | associativity =>
      exact values.evaluate_compose _ _ (values.evaluate_pair _ _
        (values.evaluate_compose _ _ (values.evaluate_first pairRead omegaRead) (values.evaluate_first omegaRead omegaRead))
        (values.evaluate_compose _ _ (values.evaluate_pair _ _
          (values.evaluate_compose _ _ (values.evaluate_first pairRead omegaRead) (values.evaluate_second omegaRead omegaRead))
          (values.evaluate_second pairRead omegaRead)) meetRead)) meetRead
    | idempotence => exact values.evaluate_identity omegaRead
    | truthUnit => exact values.evaluate_identity omegaRead

omit [MonoidalClosed D] [HasFiniteLimits D] in
theorem local_values_equal (laws : Laws meaning) (origin : ULift.{k} Law) :
    leftValue meaning origin = rightValue meaning origin := by
  cases origin with
  | up origin =>
    cases origin with
    | commutativity => exact congrArg (fun arrow => (⟨_, _, arrow⟩ : ArrowValue D)) laws.commutativity
    | associativity => exact congrArg (fun arrow => (⟨_, _, arrow⟩ : ArrowValue D)) laws.associativity
    | idempotence => exact congrArg (fun arrow => (⟨_, _, arrow⟩ : ArrowValue D)) laws.idempotence
    | truthUnit => exact congrArg (fun arrow => (⟨_, _, arrow⟩ : ArrowValue D)) laws.truthUnit

def lawfulAssignment : Assignment C (EquationExtension.extendedSymbols symbols (ULift.{k} Law)) D :=
  EquationExtension.extendAssignment (assignment base meaning)

theorem lawful_realization (laws : Laws meaning) :
    Realization (lawfulSignature (C := C)) (lawfulAssignment base meaning) where
  source origin := (EquationExtension.evaluate_object_original signature declaration (assignment base meaning) _).trans
    ((operations_realized base meaning).source origin)
  target origin := (EquationExtension.evaluate_object_original signature declaration (assignment base meaning) _).trans
    ((operations_realized base meaning).target origin)
  equation origin := by
    cases origin with
    | inl origin => exact origin.down.elim
    | inr origin =>
      refine ⟨leftValue meaning origin, ?_, ?_, ?_, ?_⟩
      · exact (EquationExtension.evaluate_object_original signature declaration (assignment base meaning) _).trans
          (declaration_source_read base meaning origin)
      · exact (EquationExtension.evaluate_object_original signature declaration (assignment base meaning) _).trans
          (declaration_target_read base meaning origin)
      · exact (EquationExtension.evaluate_arrow_original signature declaration (assignment base meaning) _).trans
          (declaration_left_read base meaning origin)
      · exact (EquationExtension.evaluate_arrow_original signature declaration (assignment base meaning) _).trans
          ((declaration_right_read base meaning origin).trans (congrArg some (local_values_equal meaning laws origin).symm))

theorem necessary_laws (realized : Realization (lawfulSignature (C := C)) (lawfulAssignment base meaning)) :
    Laws meaning := by
  have same (origin : ULift.{k} Law) : leftValue meaning origin = rightValue meaning origin := by
    obtain ⟨value, _, _, first, second⟩ := realized.equation (.inr origin)
    have left := (declaration_left_read base meaning origin).symm.trans
      ((EquationExtension.evaluate_arrow_original signature declaration (assignment base meaning) _).symm.trans first)
    have right := (declaration_right_read base meaning origin).symm.trans
      ((EquationExtension.evaluate_arrow_original signature declaration (assignment base meaning) _).symm.trans second)
    exact Option.some.inj (left.trans right.symm)
  exact ⟨ArrowValue.arrow_injective (same (ULift.up .commutativity)),
    ArrowValue.arrow_injective (same (ULift.up .associativity)),
    ArrowValue.arrow_injective (same (ULift.up .idempotence)),
    ArrowValue.arrow_injective (same (ULift.up .truthUnit))⟩

theorem realization_iff :
    Realization (lawfulSignature (C := C)) (lawfulAssignment base meaning) ↔ Laws meaning :=
  ⟨necessary_laws base meaning, lawful_realization base meaning⟩

variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
variable [PreservesFiniteLimits base] [MonoidalClosedFunctor base]

def nativeModel (laws : Laws meaning) : SemanticModels.Model (nativeSignature (C := C)) D :=
  BaseExtension.Models.extendModel
    ⟨⟨lawfulAssignment base meaning, lawful_realization base meaning laws⟩,
      (by change PreservesFiniteLimits base; infer_instance),
      (by change MonoidalClosedFunctor base; infer_instance)⟩

theorem native_restriction (laws : Laws meaning) :
    (BaseExtension.Models.restrict (nativeModel base meaning laws)).model =
      (⟨lawfulAssignment base meaning, lawful_realization base meaning laws⟩ : SemanticModels.Model lawfulSignature D) :=
  BaseExtension.Models.original_model_recovered _

end Mettapedia.CategoryTheory.RelativeClosedConjunctive.Interpretation
