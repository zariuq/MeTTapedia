import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierDiagramReadout

/-!
# Exact local admission and actual generated quantifier interpretation

The six independently computed raw diagram readings characterize local
admission. They earn the extended declaration realization and complete
quotient functor. Restriction retains every old raw expression and the
whole old interpretation. At each target context, the actual finite
diagrams derive both quantifier adjunctions rather than assume them.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Interpretation

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open RelativeClosedSyntax GeneratedCategory

universe k w z
variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable (original : Signature (C := C) (symbols := symbols))
variable (language : PredicateSyntax original)
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (meanings : RelativeClosedSyntax.Interpretation.Assignment C symbols D)
variable (old : RelativeClosedSyntax.Interpretation.Realization original meanings)
variable (operations : InternalConjunctiveObject.Operations D)
variable (meaning : Meaning original meanings old operations)
variable (propositionRead : RawInterpretation.ObjectReads meanings language.proposition operations.proposition)
variable (conjunctionRead : RawInterpretation.Reads meanings language.conjunction operations.conjunction)

def finalAssignment : RelativeClosedSyntax.Interpretation.Assignment C
    (EquationExtension.extendedSymbols (ArrowExtension.extendedSymbols symbols (Operation original)) (Law original)) D :=
  EquationExtension.extendAssignment (assignment original meanings old operations meaning)

include propositionRead conjunctionRead

theorem satisfies (admitted : Admission original meanings old operations meaning) :
    EquationExtension.Satisfies (arrowSignature original language) (declaration original language)
      (assignment original meanings old operations meaning)
      (headers_realized original language meanings old operations meaning propositionRead) := by
  intro origin
  rcases origin with ⟨diagram, route⟩
  cases diagram with
  | universalMonotonicity =>
    have readings := monotonicity_read original language meanings old operations meaning propositionRead conjunctionRead .universal route
    exact (RawInterpretation.parallel_readings_iff _ _ readings.1 readings.2).mpr
      (admitted.universalMonotonicity route).ordered
  | universalUnit =>
    have readings := universal_unit_read original language meanings old operations meaning propositionRead conjunctionRead route
    exact (RawInterpretation.parallel_readings_iff _ _ readings.1 readings.2).mpr (admitted.universalUnit route)
  | universalCounit =>
    have readings := universal_counit_read original language meanings old operations meaning propositionRead conjunctionRead route
    exact (RawInterpretation.parallel_readings_iff _ _ readings.1 readings.2).mpr (admitted.universalCounit route)
  | existentialMonotonicity =>
    have readings := monotonicity_read original language meanings old operations meaning propositionRead conjunctionRead .existential route
    exact (RawInterpretation.parallel_readings_iff _ _ readings.1 readings.2).mpr
      (admitted.existentialMonotonicity route).ordered
  | existentialUnit =>
    have readings := existential_unit_read original language meanings old operations meaning propositionRead conjunctionRead route
    exact (RawInterpretation.parallel_readings_iff _ _ readings.1 readings.2).mpr (admitted.existentialUnit route)
  | existentialCounit =>
    have readings := existential_counit_read original language meanings old operations meaning propositionRead conjunctionRead route
    exact (RawInterpretation.parallel_readings_iff _ _ readings.1 readings.2).mpr (admitted.existentialCounit route)

theorem necessary (satisfied : EquationExtension.Satisfies (arrowSignature original language) (declaration original language)
    (assignment original meanings old operations meaning)
    (headers_realized original language meanings old operations meaning propositionRead)) :
    Admission original meanings old operations meaning where
  universalMonotonicity route := by
    have readings := monotonicity_read original language meanings old operations meaning propositionRead conjunctionRead .universal route
    exact ⟨(RawInterpretation.parallel_readings_iff _ _ readings.1 readings.2).mp (satisfied ⟨.universalMonotonicity, route⟩)⟩
  universalUnit route := by
    have readings := universal_unit_read original language meanings old operations meaning propositionRead conjunctionRead route
    exact (RawInterpretation.parallel_readings_iff _ _ readings.1 readings.2).mp (satisfied ⟨.universalUnit, route⟩)
  universalCounit route := by
    have readings := universal_counit_read original language meanings old operations meaning propositionRead conjunctionRead route
    exact (RawInterpretation.parallel_readings_iff _ _ readings.1 readings.2).mp (satisfied ⟨.universalCounit, route⟩)
  existentialMonotonicity route := by
    have readings := monotonicity_read original language meanings old operations meaning propositionRead conjunctionRead .existential route
    exact ⟨(RawInterpretation.parallel_readings_iff _ _ readings.1 readings.2).mp (satisfied ⟨.existentialMonotonicity, route⟩)⟩
  existentialUnit route := by
    have readings := existential_unit_read original language meanings old operations meaning propositionRead conjunctionRead route
    exact (RawInterpretation.parallel_readings_iff _ _ readings.1 readings.2).mp (satisfied ⟨.existentialUnit, route⟩)
  existentialCounit route := by
    have readings := existential_counit_read original language meanings old operations meaning propositionRead conjunctionRead route
    exact (RawInterpretation.parallel_readings_iff _ _ readings.1 readings.2).mp (satisfied ⟨.existentialCounit, route⟩)

theorem satisfied_iff :
    EquationExtension.Satisfies (arrowSignature original language) (declaration original language)
      (assignment original meanings old operations meaning)
      (headers_realized original language meanings old operations meaning propositionRead) ↔
        Admission original meanings old operations meaning :=
  ⟨necessary original language meanings old operations meaning propositionRead conjunctionRead,
    satisfies original language meanings old operations meaning propositionRead conjunctionRead⟩

theorem realized (admitted : Admission original meanings old operations meaning) :
    RelativeClosedSyntax.Interpretation.Realization (signature original language)
      (finalAssignment original meanings old operations meaning) :=
  EquationExtension.extended_realization (arrowSignature original language) (declaration original language)
    (assignment original meanings old operations meaning)
    (headers_realized original language meanings old operations meaning propositionRead)
    (satisfies original language meanings old operations meaning propositionRead conjunctionRead admitted)

theorem realization_iff :
    RelativeClosedSyntax.Interpretation.Realization (signature original language)
      (finalAssignment original meanings old operations meaning) ↔
        Admission original meanings old operations meaning :=
  (EquationExtension.realization_iff_satisfaction (arrowSignature original language) (declaration original language)
    (assignment original meanings old operations meaning)
    (headers_realized original language meanings old operations meaning propositionRead)).trans
    (satisfied_iff original language meanings old operations meaning propositionRead conjunctionRead)

def diagram (admitted : Admission original meanings old operations meaning) : Object (signature original language) ⥤ D :=
  RelativeClosedSyntax.Interpretation.functor (finalAssignment original meanings old operations meaning)
    (realized original language meanings old operations meaning propositionRead conjunctionRead admitted)

theorem complete_old_restriction (admitted : Admission original meanings old operations meaning) :
    (arrowInclusion original language).functor ⋙ (equationInclusion original language).functor ⋙
        diagram original language meanings old operations meaning propositionRead conjunctionRead admitted =
      RelativeClosedSyntax.Interpretation.functor meanings old := by
  have nextRead := EquationExtension.complete_restriction (arrowSignature original language) (declaration original language)
    (assignment original meanings old operations meaning)
    (headers_realized original language meanings old operations meaning propositionRead)
    (satisfies original language meanings old operations meaning propositionRead conjunctionRead admitted)
  have inherited := congrArg
    (fun target : Object (arrowSignature original language) ⥤ D => (arrowInclusion original language).functor ⋙ target) nextRead
  exact inherited.trans (ArrowExtension.complete_restriction original (arrowDeclaration original language)
    meanings (added original meanings old operations meaning) old
    (added_headers original language meanings old operations meaning propositionRead))

omit propositionRead conjunctionRead in
def universalQualification (admitted : Admission original meanings old operations meaning) (route : Route original) :
    InternalPredicateQuantifier.Universal operations (routeValue original meanings old route) where
  operation := meaning.universal route
  monotonicity := admitted.universalMonotonicity route
  unit := admitted.universalUnit route
  counit := admitted.universalCounit route

omit propositionRead conjunctionRead in
def existentialQualification (admitted : Admission original meanings old operations meaning) (route : Route original) :
    InternalPredicateExistential.Existential operations (routeValue original meanings old route) where
  operation := meaning.existential route
  monotonicity := admitted.existentialMonotonicity route
  unit := admitted.existentialUnit route
  counit := admitted.existentialCounit route

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Interpretation
