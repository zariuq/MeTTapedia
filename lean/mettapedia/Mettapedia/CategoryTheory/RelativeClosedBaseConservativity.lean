import Mettapedia.CategoryTheory.RelativeClosedBaseRealizationUniqueness
import Mathlib.CategoryTheory.Equivalence

/-!
# Conservativity of the independently generated closed base presentation

The base comparison syntax retains all original objects and arrows. Its
native interpreter is a retraction. The local inverse declarations also
determine the complete primitive assignment of every finite-limit closed
interpretation, so reconstruction supplies the other comparison.

These two earned comparisons give an actual equivalence with the original
base. Raw formal object presentations remain distinct objects; the theorem
compares them coherently rather than identifying their spellings.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseComparisons.Conservativity

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Interpretation FunctorNormalization GeneratedCategory

universe k w

variable {C : Type k} [Category.{k} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]

abbrev Guest := Object (signature (C := C))
abbrev inclusion : C ⥤ Guest (C := C) := base (C := C)
abbrev native : Guest (C := C) ⥤ C := NativeDiagram.interpretation (C := C)

instance native_finite : PreservesFiniteLimits (native (C := C)) := by
  dsimp only [native, NativeDiagram.interpretation]
  infer_instance

instance native_closed : MonoidalClosedFunctor (native (C := C)) := by
  dsimp only [native, NativeDiagram.interpretation]
  infer_instance

theorem native_retraction : inclusion (C := C) ⋙ native (C := C) = 𝟭 C :=
  NativeDiagram.base_recovery (C := C)

instance inclusion_faithful : (inclusion (C := C)).Faithful :=
  Functor.Faithful.of_comp_eq (native_retraction (C := C))

variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (first second : Guest (C := C) ⥤ D)
variable [PreservesFiniteLimits first] [MonoidalClosedFunctor first]
variable [PreservesFiniteLimits second] [MonoidalClosedFunctor second]

theorem complete_assignment_from_base
    (same : inclusion (C := C) ⋙ first = inclusion (C := C) ⋙ second) :
    FunctorNormalization.assignment first (headers (C := C)) =
      FunctorNormalization.assignment second (headers (C := C)) :=
  RealizationUniqueness.assignment_equal _
    (reconstruction_realization first (headers (C := C))) _
    (reconstruction_realization second (headers (C := C))) same

private theorem interpretation_equal
    {before after : Assignment C (symbols C) D}
    (firstMeaning : Realization (signature (C := C)) before)
    (secondMeaning : Realization (signature (C := C)) after) (same : before = after) :
    Interpretation.functor before firstMeaning = Interpretation.functor after secondMeaning := by
  cases same
  rfl

theorem reconstructed_equal_from_base
    (same : inclusion (C := C) ⋙ first = inclusion (C := C) ⋙ second) :
    reconstructedFunctor first (headers (C := C)) =
      reconstructedFunctor second (headers (C := C)) :=
  interpretation_equal _ _ (complete_assignment_from_base first second same)

/-- Equality on the authored base earns a comparison on every formal object
and every generated arrow, through their actual reconstruction. -/
def comparison_from_base
    (same : inclusion (C := C) ⋙ first = inclusion (C := C) ⋙ second) : first ≅ second :=
  parserComparison first (headers (C := C)) ≪≫
    eqToIso (reconstructed_equal_from_base first second same) ≪≫
      (parserComparison second (headers (C := C))).symm

omit [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
  [PreservesFiniteLimits first] [MonoidalClosedFunctor first]
  [PreservesFiniteLimits second] [MonoidalClosedFunctor second] in
theorem original_arrow_equality_iff {source target : C} (first second : source ⟶ target) :
    (inclusion (C := C)).map first = (inclusion (C := C)).map second ↔ first = second :=
  ⟨fun same => (inclusion (C := C)).map_injective same,
    fun same => congrArg (inclusion (C := C)).map same⟩

def generated_comparison : 𝟭 (Guest (C := C)) ≅ native (C := C) ⋙ inclusion (C := C) := by
  letI : MonoidalClosedFunctor (𝟭 (Guest (C := C))) := {
    comparison_iso := fun domain => by
      have (target : Guest (C := C)) :
          IsIso ((expComparison (𝟭 (Guest (C := C))) domain).natTrans.app target) := by
        rw [Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence.exponential_identity]
        exact IsIso.id (C := Guest (C := C)) ((ihom domain).obj target)
      exact NatIso.isIso_of_isIso_app _ }
  letI : PreservesFiniteLimits (native (C := C) ⋙ inclusion (C := C)) :=
    comp_preservesFiniteLimits _ _
  letI : MonoidalClosedFunctor (native (C := C) ⋙ inclusion (C := C)) :=
    Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence.closed_composition _ _
  apply comparison_from_base
  exact (Functor.comp_id (inclusion (C := C))).trans
    ((congrArg (fun route : C ⥤ C => route ⋙ inclusion (C := C))
      (native_retraction (C := C))).trans (Functor.id_comp (inclusion (C := C)))).symm

/-- The equivalence follows from both earned complete comparisons. -/
def equivalence : C ≌ Guest (C := C) :=
  _root_.CategoryTheory.Equivalence.mk (inclusion (C := C)) (native (C := C))
    (eqToIso (native_retraction (C := C))).symm (generated_comparison (C := C)).symm

instance inclusion_full : (inclusion (C := C)).Full :=
  inferInstanceAs (equivalence (C := C)).functor.Full

theorem every_formal_object_represented (formal : Guest (C := C)) :
    Nonempty ((inclusion (C := C)).obj ((native (C := C)).obj formal) ≅ formal) :=
  ⟨(generated_comparison (C := C)).symm.app formal⟩

end Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseComparisons.Conservativity
