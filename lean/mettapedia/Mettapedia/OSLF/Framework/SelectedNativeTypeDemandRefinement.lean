import Mathlib.CategoryTheory.Functor.Basic
import Mettapedia.OSLF.Framework.SelectedNativeTypeDemand
import Mettapedia.OSLF.Framework.SelectedNativeTypeFoundationRefinement

/-!
# Stable-prefix refinement of profiled native-type demands

Incremental generation may append newly selected occurrences, but it must not
renumber an old occurrence or silently change an old local hypercube profile.
`Refinement earlier later` therefore carries the exact complete residual whose
ordered append reconstructs `later`.

This category describes stable incremental growth.  It deliberately does not
invent directed edges between different vertices over one fixed occurrence
list; that separate hypercube-edge question depends on the generated typing
rules and their semantic interpretation.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.GSLT.LanguageDef
open CategoryTheory

namespace SelectedNativeTypeDemand

/-- Exact complete residual witnessing stable-prefix growth. -/
structure Refinement {source : ValidatedLanguageDef}
    (earlier later : SelectedNativeTypeDemand source) where
  residual : SelectedNativeTypeDemand source
  target_eq : earlier.append residual = later

namespace Refinement

@[ext]
theorem ext {source : ValidatedLanguageDef}
    {earlier later : SelectedNativeTypeDemand source}
    {first second : Refinement earlier later}
    (residual : first.residual = second.residual) : first = second := by
  cases first
  cases second
  cases residual
  rfl

/-- Empty residual is the stable-prefix identity. -/
def id {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    Refinement demand demand where
  residual := SelectedNativeTypeDemand.empty source
  target_eq := append_empty demand

/-- Consecutive residuals compose by ordered demand append. -/
def comp {source : ValidatedLanguageDef}
    {first second third : SelectedNativeTypeDemand source}
    (earlier : Refinement first second)
    (later : Refinement second third) :
    Refinement first third where
  residual := earlier.residual.append later.residual
  target_eq := by
    calc
      first.append (earlier.residual.append later.residual) =
          (first.append earlier.residual).append later.residual :=
        (append_assoc first earlier.residual later.residual).symm
      _ = second.append later.residual := by rw [earlier.target_eq]
      _ = third := later.target_eq

/-- Forget local profiles and obtain the corresponding exact refinement of
the grounded syntactic foundation. -/
def foundation {source : ValidatedLanguageDef}
    {earlier later : SelectedNativeTypeDemand source}
    (refinement : Refinement earlier later) :
    SelectedNativeTypeFoundation.DemandRefinement
      earlier.foundation later.foundation where
  residual := refinement.residual.foundation
  target_eq := by
    simpa using
      congrArg SelectedNativeTypeDemand.foundation refinement.target_eq

/-- Every refinement retains the complete authored occurrence prefix. -/
theorem typings_prefix {source : ValidatedLanguageDef}
    {earlier later : SelectedNativeTypeDemand source}
    (refinement : Refinement earlier later) :
    earlier.foundation.typings.IsPrefix later.foundation.typings :=
  refinement.foundation.typings_prefix

/-- Every refinement retains the complete authored profile-wire prefix. -/
theorem choices_prefix {source : ValidatedLanguageDef}
    {earlier later : SelectedNativeTypeDemand source}
    (refinement : Refinement earlier later) :
    earlier.choices.IsPrefix later.choices := by
  rw [← refinement.target_eq, append_choices]
  exact List.prefix_append _ _

end Refinement

/-- Profiled demands over one fixed source form a category under exact
stable-prefix growth. -/
instance demandCategory (source : ValidatedLanguageDef) :
    CategoryTheory.Category (SelectedNativeTypeDemand source) where
  Hom := Refinement
  id := Refinement.id
  comp := Refinement.comp
  id_comp morphism := by
    apply Refinement.ext
    exact empty_append morphism.residual
  comp_id morphism := by
    apply Refinement.ext
    exact append_empty morphism.residual
  assoc first second third := by
    apply Refinement.ext
    exact append_assoc first.residual second.residual third.residual

/-- Append one declared complete residual. -/
def appendRefinement {source : ValidatedLanguageDef}
    (earlier residual : SelectedNativeTypeDemand source) :
    earlier ⟶ earlier.append residual where
  residual := residual
  target_eq := rfl

/-! ## Positive and negative controls -/

namespace RefinementCanary

/-- Every complete residual induces stable-prefix refinement. -/
theorem appended_demand_has_refinement
    {source : ValidatedLanguageDef}
    (earlier residual : SelectedNativeTypeDemand source) :
    Nonempty (earlier ⟶ earlier.append residual) :=
  ⟨appendRefinement earlier residual⟩

/-- A target that does not retain the authored occurrence prefix cannot be a
stable incremental refinement. -/
theorem no_refinement_without_typing_prefix
    {source : ValidatedLanguageDef}
    {earlier later : SelectedNativeTypeDemand source}
    (notPrefix :
      ¬ earlier.foundation.typings.IsPrefix later.foundation.typings) :
    IsEmpty (earlier ⟶ later) := by
  constructor
  intro refinement
  exact notPrefix refinement.typings_prefix

/-- A target that changes an already allocated profile row cannot be a stable
incremental refinement, even if its occurrence list is unchanged. -/
theorem no_refinement_without_choice_prefix
    {source : ValidatedLanguageDef}
    {earlier later : SelectedNativeTypeDemand source}
    (notPrefix : ¬ earlier.choices.IsPrefix later.choices) :
    IsEmpty (earlier ⟶ later) := by
  constructor
  intro refinement
  exact notPrefix refinement.choices_prefix

end RefinementCanary

#print axioms Refinement.comp
#print axioms Refinement.foundation
#print axioms Refinement.typings_prefix
#print axioms Refinement.choices_prefix
#print axioms appendRefinement
#print axioms RefinementCanary.appended_demand_has_refinement
#print axioms RefinementCanary.no_refinement_without_typing_prefix
#print axioms RefinementCanary.no_refinement_without_choice_prefix

end SelectedNativeTypeDemand

end Mettapedia.OSLF.Framework
