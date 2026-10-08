import Mettapedia.CategoryTheory.RelativeClosedPredicateLogicDeclarationReadout
import Mettapedia.CategoryTheory.RelativeClosedSyntaxInterpretationReadout
import Mettapedia.CategoryTheory.RelativeClosedSyntaxBaseExtensionModels

/-!
# Exact finite-law admission and earned predicate-presentation models

The complete independent readings of every authored equation earn
declaration realization from the local finite diagrams. Conversely,
realizing the declarations forces precisely those diagrams. The actual
quotient interpretation is therefore obtained from local semantic data,
with no whole-model soundness or free-extension universal property field.

A separately supplied weak finite-limit closed base earns the native base
extension at the explicit common hom universe of its closed comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedPredicateLogic.Interpretation

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax RelativeClosedSyntax.Interpretation GeneratedCategory

universe k w z
variable {C : Type k} [Category.{k} C]
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (base : C ⥤ D) (meaning : Meaning base)

theorem declarations_satisfied (admitted : Admission base meaning) :
    EquationExtension.Satisfies (signature (C := C)) declaration
      (assignment base meaning) (headers_realized base meaning) := by
  intro origin
  have first := functor_map_heq (assignment base meaning) (headers_realized base meaning)
    (declaration origin).left (leftValue base meaning origin).arrow
    (declaration_left_read base meaning origin)
  have second := functor_map_heq (assignment base meaning) (headers_realized base meaning)
    (declaration origin).right (rightValue base meaning origin).arrow
    (declaration_right_read base meaning origin)
  exact eq_of_heq (first.trans
    ((ArrowValue.arrows_heq (local_values_equal base meaning admitted origin)).trans second.symm))

def lawfulAssignment : Assignment C (EquationExtension.extendedSymbols (symbols C) (Law C)) D :=
  EquationExtension.extendAssignment (assignment base meaning)

theorem lawful_realization (admitted : Admission base meaning) :
    Realization (lawfulSignature (C := C)) (lawfulAssignment base meaning) :=
  EquationExtension.extended_realization (signature (C := C)) declaration
    (assignment base meaning) (headers_realized base meaning) (declarations_satisfied base meaning admitted)

theorem necessary_admission
    (realized : Realization (lawfulSignature (C := C)) (lawfulAssignment base meaning)) :
    Admission base meaning := by
  have satisfied := EquationExtension.necessary_satisfaction (signature (C := C)) declaration
    (assignment base meaning) (headers_realized base meaning) realized
  have same (origin : Law C) : leftValue base meaning origin = rightValue base meaning origin := by
    have first := (declaration_left_read base meaning origin).symm.trans
      (functor_complete_readout (assignment base meaning) (headers_realized base meaning) (declaration origin).left)
    have second := (declaration_right_read base meaning origin).symm.trans
      (functor_complete_readout (assignment base meaning) (headers_realized base meaning) (declaration origin).right)
    have actual := congrArg
      (fun arrow => some (⟨(functor (assignment base meaning) (headers_realized base meaning)).obj
        (declaration origin).source,
        (functor (assignment base meaning) (headers_realized base meaning)).obj (declaration origin).target,
        arrow⟩ : ArrowValue D)) (satisfied origin)
    exact Option.some.inj (first.trans (actual.trans second.symm))
  exact {
    conjunction := {
      commutativity := ArrowValue.arrow_injective (same (Law.commutativity (C := C)))
      associativity := ArrowValue.arrow_injective (same (Law.associativity (C := C)))
      idempotence := ArrowValue.arrow_injective (same (Law.idempotence (C := C)))
      truthUnit := ArrowValue.arrow_injective (same (Law.truthUnit (C := C))) }
    implicationMonotonicity := ArrowValue.arrow_injective (same (Law.implicationMonotonicity (C := C)))
    implicationUnit := ArrowValue.arrow_injective (same (Law.implicationUnit (C := C)))
    implicationCounit := ArrowValue.arrow_injective (same (Law.implicationCounit (C := C)))
    universalMonotonicity := fun route => ⟨ArrowValue.arrow_injective (same (Law.universalMonotonicity route))⟩
    universalUnit := fun route => ArrowValue.arrow_injective (same (Law.universalUnit route))
    universalCounit := fun route => ArrowValue.arrow_injective (same (Law.universalCounit route))
    existentialMonotonicity := fun route => ⟨ArrowValue.arrow_injective (same (Law.existentialMonotonicity route))⟩
    existentialUnit := fun route => ArrowValue.arrow_injective (same (Law.existentialUnit route))
    existentialCounit := fun route => ArrowValue.arrow_injective (same (Law.existentialCounit route)) }

theorem realization_iff_admission :
    Realization (lawfulSignature (C := C)) (lawfulAssignment base meaning) ↔ Admission base meaning :=
  ⟨necessary_admission base meaning, lawful_realization base meaning⟩

section CommonTarget

variable {E : Type w} [Category.{k} E]
variable [CartesianMonoidalCategory E] [MonoidalClosed E] [HasFiniteLimits E]

def model (base : C ⥤ E) (meaning : Meaning base) (admitted : Admission base meaning) :
    SemanticModels.Model (lawfulSignature (C := C)) E :=
  ⟨lawfulAssignment base meaning, lawful_realization base meaning admitted⟩

section NativeBase

variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
def nativeModel (base : C ⥤ E) (meaning : Meaning base) (admitted : Admission base meaning)
    [PreservesFiniteLimits base] [MonoidalClosedFunctor base] :
    SemanticModels.Model (nativeSignature (C := C)) E :=
  BaseExtension.Models.extendModel
    ⟨model base meaning admitted,
      (by change PreservesFiniteLimits base; infer_instance),
      (by change MonoidalClosedFunctor base; infer_instance)⟩

theorem native_restriction (base : C ⥤ E) (meaning : Meaning base) (admitted : Admission base meaning)
    [PreservesFiniteLimits base] [MonoidalClosedFunctor base] :
    (BaseExtension.Models.restrict (nativeModel base meaning admitted)).model = model base meaning admitted :=
  BaseExtension.Models.original_model_recovered _

end NativeBase

end CommonTarget

end Mettapedia.CategoryTheory.RelativeClosedPredicateLogic.Interpretation
