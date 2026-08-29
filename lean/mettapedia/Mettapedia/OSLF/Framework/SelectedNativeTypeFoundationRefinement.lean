import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef.StructuralCategory
import Mettapedia.OSLF.Framework.SelectedNativeTypeFoundationValidation

/-!
# Append-only refinement of the selected native-type foundation demand

Changing the source language and asking for more of one fixed source are
different operations.  The former is structural reindexing; the latter is an
ordered vertical refinement.  This module gives demand growth its own
category rather than overloading source-language morphisms with two meanings.

A refinement carries its exact residual demand.  Composition concatenates
residuals, and sparse generation sends it to the canonical append-only
inclusion of the resulting flat calculus GSLTs.  Old carrier and occurrence
slots therefore remain stable by construction.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.GSLT.LanguageDef
open CategoryTheory

namespace SelectedNativeTypeFoundation

/-- Exact ordered residual witnessing growth from one demand to another. -/
structure DemandRefinement {source : ValidatedLanguageDef}
    (earlier later : Demand source) where
  residual : Demand source
  target_eq : earlier.append residual = later

namespace DemandRefinement

@[ext]
theorem ext {source : ValidatedLanguageDef}
    {earlier later : Demand source}
    {first second : DemandRefinement earlier later}
    (residual : first.residual = second.residual) : first = second := by
  cases first
  cases second
  cases residual
  rfl

/-- Empty residual is the refinement identity. -/
def id {source : ValidatedLanguageDef} (demand : Demand source) :
    DemandRefinement demand demand where
  residual := Demand.empty source
  target_eq := Demand.append_empty demand

/-- Ordered residuals compose by demand concatenation. -/
def comp {source : ValidatedLanguageDef}
    {first second third : Demand source}
    (earlier : DemandRefinement first second)
    (later : DemandRefinement second third) :
    DemandRefinement first third where
  residual := earlier.residual.append later.residual
  target_eq := by
    calc
      first.append (earlier.residual.append later.residual) =
          (first.append earlier.residual).append later.residual :=
        (Demand.append_assoc first earlier.residual later.residual).symm
      _ = second.append later.residual := by rw [earlier.target_eq]
      _ = third := later.target_eq

/-- Every exact residual makes the earlier typing list an authored prefix of
the later list. -/
theorem typings_prefix {source : ValidatedLanguageDef}
    {earlier later : Demand source}
    (refinement : DemandRefinement earlier later) :
    earlier.typings.IsPrefix later.typings := by
  rw [← refinement.target_eq]
  exact List.prefix_append _ _

end DemandRefinement

/-- Ordered demands over one fixed source form a category under exact
append-only refinement. -/
instance demandCategory (source : ValidatedLanguageDef) :
    CategoryTheory.Category (Demand source) where
  Hom := DemandRefinement
  id := DemandRefinement.id
  comp := DemandRefinement.comp
  id_comp morphism := by
    apply DemandRefinement.ext
    exact Demand.empty_append morphism.residual
  comp_id morphism := by
    apply DemandRefinement.ext
    exact Demand.append_empty morphism.residual
  assoc first second third := by
    apply DemandRefinement.ext
    exact Demand.append_assoc first.residual second.residual third.residual

/-- Append a declared residual demand. -/
def appendRefinement {source : ValidatedLanguageDef}
    (earlier residual : Demand source) :
    earlier ⟶ earlier.append residual where
  residual := residual
  target_eq := rfl

/-- Generated flat calculi vary functorially with append-only demand growth
over a fixed source GSLT. -/
noncomputable def refinementFunctor (source : ValidatedLanguageDef) :
    CategoryTheory.Functor (Demand source) ValidatedCalculusLanguageDef where
  obj demand := validated demand
  map {X Y} refinement := by
    apply CalculusStructuralMorphism.ofAppendOnly
    have appendOnly := definition_appendOnly X refinement.residual
    rw [refinement.target_eq] at appendOnly
    exact appendOnly
  map_id demand := by
    apply CalculusStructuralMorphism.ext
    rfl
  map_comp earlier later := by
    apply CalculusStructuralMorphism.ext
    exact CalculusLanguageSymbols.comp_id CalculusLanguageSymbols.id

/-! ## Positive and negative controls -/

namespace RefinementCanary

/-- Every residual demand induces a structural inclusion of the complete
generated calculus. -/
theorem appended_demand_maps_complete_calculus
    {source : ValidatedLanguageDef} (earlier residual : Demand source) :
    Nonempty
      (validated earlier ⟶ validated (earlier.append residual)) :=
  ⟨(refinementFunctor source).map (appendRefinement earlier residual)⟩

/-- A demand whose ordered typing list does not retain the source prefix
admits no vertical refinement arrow. -/
theorem no_refinement_without_typing_prefix
    {source : ValidatedLanguageDef} {earlier later : Demand source}
    (notPrefix : ¬ earlier.typings.IsPrefix later.typings) :
    IsEmpty (earlier ⟶ later) := by
  constructor
  intro refinement
  exact notPrefix refinement.typings_prefix

end RefinementCanary

#print axioms DemandRefinement.comp
#print axioms DemandRefinement.typings_prefix
#print axioms appendRefinement
#print axioms refinementFunctor
#print axioms RefinementCanary.appended_demand_maps_complete_calculus
#print axioms RefinementCanary.no_refinement_without_typing_prefix

end SelectedNativeTypeFoundation

end Mettapedia.OSLF.Framework
