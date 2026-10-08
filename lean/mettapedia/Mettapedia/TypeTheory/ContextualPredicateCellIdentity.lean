import Mettapedia.TypeTheory.ContextualPredicateMorphism
import Mettapedia.TypeTheory.ContextualCartesianCellIdentity

/-!
# Identity propagation through guarded and proposition contexts

A contextual transformation fixing an assumption's unrestricted context
also fixes its guarded context. The actual mapped assumption inclusion is
monic, earned from its independent target inclusion and the local
assumption comparison. Ordinary proposition displays are instances of the
single closed proposition display; their identity follows from cartesian
naturality and the chosen proposition substitution law.

No component identity for all guarded contexts or all proposition contexts
is an admission field.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualPredicateCellIdentity

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateCapabilities ContextualPredicateMorphism
open ContextualCartesianCellIdentity

universe c s t m p q
variable {C D : CwfWithTerminal.{c,s,t,m}}

/-- Local assumption preservation transports the actual monicity of the
target inclusion to the complete mapped source inclusion. -/
theorem mapped_assumption_inclusion_injective
    {mapping : StrictCwfMorphism C D}
    {source : PredicateDoctrine.{c,s,t,m,p} C.toCwf}
    {target : PredicateDoctrine.{c,s,t,m,q} D.toCwf}
    {predicates : DoctrinePreservation mapping source target}
    {sourceOperations : AssumptionOperations source}
    {targetOperations : AssumptionOperations target}
    (preserved : AssumptionPreservation predicates sourceOperations targetOperations)
    {Γ : C.toCwf.Ctx} (predicate : source.Predicate Γ)
    (object : D.toCwf.base.Context) :
    Function.Injective (fun arrow : object ⟶
      mapping.toFamilyMorphism.base.obj ⟨sourceOperations.assumed Γ predicate⟩ =>
        arrow ≫ mapping.toFamilyMorphism.base.map (sourceOperations.inclusion predicate)) := by
  intro first second equal
  change first ≫ mapping.toFamilyMorphism.base.map (sourceOperations.inclusion predicate) =
    second ≫ mapping.toFamilyMorphism.base.map (sourceOperations.inclusion predicate) at equal
  rw [preserved.inclusion predicate] at equal
  rw [← Category.assoc, ← Category.assoc] at equal
  have compared := targetOperations.inclusion_monic (predicates.hom Γ predicate)
    (first ≫ eqToHom (preserved.assumed Γ predicate))
    (second ≫ eqToHom (preserved.assumed Γ predicate)) equal
  exact (cancel_mono (eqToHom (preserved.assumed Γ predicate))).mp compared

/-- A guarded-context component is determined by its unrestricted reading.
The target monicity used here is supplied by the actual local assumption
capability, rather than by a component identity premise. -/
theorem assumption_fixed
    {mapping : StrictCwfMorphism C D}
    {source : PredicateDoctrine.{c,s,t,m,p} C.toCwf}
    {target : PredicateDoctrine.{c,s,t,m,q} D.toCwf}
    {predicates : DoctrinePreservation mapping source target}
    {sourceOperations : AssumptionOperations source}
    {targetOperations : AssumptionOperations target}
    (preserved : AssumptionPreservation predicates sourceOperations targetOperations)
    (cell : mapping.toFamilyMorphism.base ⟶ mapping.toFamilyMorphism.base)
    {Γ : C.toCwf.Ctx} (predicate : source.Predicate Γ)
    (baseFixed : cell.app ⟨Γ⟩ = 𝟙 (mapping.toFamilyMorphism.base.obj ⟨Γ⟩)) :
    cell.app ⟨sourceOperations.assumed Γ predicate⟩ =
      𝟙 (mapping.toFamilyMorphism.base.obj ⟨sourceOperations.assumed Γ predicate⟩) := by
  apply mapped_assumption_inclusion_injective preserved predicate
    (mapping.toFamilyMorphism.base.obj ⟨sourceOperations.assumed Γ predicate⟩)
  have natural := cell.naturality
    (show (⟨sourceOperations.assumed Γ predicate⟩ : C.toCwf.base.Context) ⟶ ⟨Γ⟩ from
      sourceOperations.inclusion predicate)
  rw [baseFixed, Category.comp_id] at natural
  simpa only [Category.id_comp] using natural.symm

/-- The ordinary proposition type is closed under its specified chosen
substitution. One closed display component and the actual current base
component therefore determine every proposition display component. -/
theorem omega_fixed (mapping : StrictCwfMorphism C D)
    (cell : mapping.toFamilyMorphism.base ⟶ mapping.toFamilyMorphism.base)
    {source : PredicateDoctrine.{c,s,t,m,p} C.toCwf}
    (operations : PropositionOperations source) (Γ : C.toCwf.Ctx)
    (baseFixed : cell.app ⟨Γ⟩ = 𝟙 (mapping.toFamilyMorphism.base.obj ⟨Γ⟩))
    (closedFixed : cell.app ⟨C.toCwf.ext C.empty (operations.omega C.empty)⟩ =
      𝟙 (mapping.toFamilyMorphism.base.obj ⟨C.toCwf.ext C.empty (operations.omega C.empty)⟩)) :
    cell.app ⟨C.toCwf.ext Γ (operations.omega Γ)⟩ =
      𝟙 (mapping.toFamilyMorphism.base.obj ⟨C.toCwf.ext Γ (operations.omega Γ)⟩) := by
  have fixed := reindexed_fixed mapping cell (C.toEmpty Γ)
    (operations.omega C.empty) baseFixed closedFixed
  rw [operations.omega_substitution] at fixed
  exact fixed

end Mettapedia.TypeTheory.ContextualPredicateCellIdentity
