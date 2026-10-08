import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementClassifyingCellUniqueness

/-!
# Predicate coherence of admitted classifying comparisons

The independent comparison of every supplied definable predicate class
earns predicate compatibility on chosen scopes. Actual predicate
substitution through the raw-context presentation conjugation transports
that equality to every retained context. Declaration-admitted corrected
cells inherit the earned comparison by the proved complete-cell uniqueness.

Thus predicate coherence is a consequence of local model-map laws and
source readbacks. It is not an all-expression or all-cell preservation
assumption, and definable predicates are not identified with all subobjects.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.ModelMapComparison

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualPredicateCapabilities
open Mettapedia.TypeTheory.ContextualPredicateModel
open Mettapedia.TypeTheory.ContextualPredicateModelScopes
open Mettapedia.TypeTheory.ContextualComprehensionMorphism
open Refinement.Abstract

universe u z p c s t m q
variable {S : Symbols.{u}} {D : Signature S}
  {C : CwfWithTerminal.{max u z,max u z,max u z,max u z}}
  {targetModel : LocalModel.{max u z,max u z,max u z,max u z,p} C}
  {target : ModelData S C targetModel}
variable (headers : HeaderFormation D)
  (first second : ModelMap (Interpretation.sourceData.{u,z} headers) target)

private theorem predicate_reindex_equality
    {E : CwfWithTerminal.{c,s,t,m}}
    (doctrine : PredicateDoctrine.{c,s,t,m,q} E.toCwf)
    {Γ Δ : E.toCwf.base.Context} (same : Γ = Δ)
    {φ : doctrine.Predicate Γ.val} {ψ : doctrine.Predicate Δ.val}
    (readings : HEq φ ψ) : doctrine.reindex (eqToHom same) ψ = φ := by
  cases same
  cases eq_of_heq readings
  exact doctrine.reindex_id φ

private theorem predicate_heq_mixed {n : Nat} {Γ : QuotientCwf.QContext D}
    (mixed : ScopeData (QuotientCwf.withTerminal D) (generatedModel D).doctrine
      (generatedModel D).assumptions n Γ)
    (predicate : (Interpretation.sourceLocalModel.{u,z} D).doctrine.Predicate (ULift.up Γ)) :
    HEq (first.predicates.doctrine.hom _ predicate)
      (second.predicates.doctrine.hom _ predicate) := by
  rcases Γ with ⟨⟨arity,raw,formed⟩⟩
  have count := SyntacticScopes.scope_arity mixed
  cases count
  exact predicate_heq headers first second ⟨raw,formed,mixed⟩ predicate

/-- Predicate values commute with the complete raw-context comparison,
including both actual presentation arrows and the earned equality at the
chosen intermediate context. -/
theorem correctedIso_predicate_raw (Γ : QuotientCwf.QContext D)
    (predicate : (Interpretation.sourceLocalModel.{u,z} D).doctrine.Predicate (ULift.up Γ)) :
    targetModel.doctrine.reindex
      ((correctedIso headers first second).hom.base.app ⟨ULift.up Γ⟩)
      (second.predicates.doctrine.hom (ULift.up Γ) predicate) =
        first.predicates.doctrine.hom (ULift.up Γ) predicate := by
  let normalized := (Presentation.quotientNormalizer D).obj Γ
  let comparison := Presentation.quotientComparison Γ
  let incoming : (Interpretation.SourceModel.{u,z} D).toCwf.Sub
    (ULift.up Γ) (ULift.up normalized) := ULift.up comparison.inv
  let outgoing : (Interpretation.SourceModel.{u,z} D).toCwf.Sub
    (ULift.up normalized) (ULift.up Γ) := ULift.up comparison.hom
  let sourceDoctrine := (Interpretation.sourceLocalModel.{u,z} D).doctrine
  let pulled := sourceDoctrine.reindex outgoing predicate
  let objects := congrArg (fun functor => functor.obj Γ)
    (normalized_functor_equal headers first second)
  have readings := predicate_heq_mixed headers first second (Presentation.selectedScopeData Γ.as) pulled
  have compared := predicate_reindex_equality targetModel.doctrine objects readings
  change targetModel.doctrine.reindex (eqToHom objects)
    (second.predicates.doctrine.hom (ULift.up normalized) pulled) =
      first.predicates.doctrine.hom (ULift.up normalized) pulled at compared
  rw [correctedIso_base_component, contextIso_hom_component]
  change targetModel.doctrine.reindex
    (first.morphism.toFamilyMorphism.base.map incoming ≫ eqToHom objects ≫
      second.morphism.toFamilyMorphism.base.map outgoing)
    (second.predicates.doctrine.hom (ULift.up Γ) predicate) = _
  calc
    _ = targetModel.doctrine.reindex (first.morphism.toFamilyMorphism.base.map incoming)
        (targetModel.doctrine.reindex (eqToHom objects)
          (targetModel.doctrine.reindex (second.morphism.toFamilyMorphism.base.map outgoing)
            (second.predicates.doctrine.hom (ULift.up Γ) predicate))) := by
      exact (targetModel.doctrine.reindex_comp _ _ _).trans
        (congrArg (targetModel.doctrine.reindex (first.morphism.toFamilyMorphism.base.map incoming))
          (targetModel.doctrine.reindex_comp _ _ _))
    _ = targetModel.doctrine.reindex (first.morphism.toFamilyMorphism.base.map incoming)
        (targetModel.doctrine.reindex (eqToHom objects)
          (second.predicates.doctrine.hom (ULift.up normalized) pulled)) := by
      exact congrArg
        (fun value => targetModel.doctrine.reindex
          (first.morphism.toFamilyMorphism.base.map incoming)
          (targetModel.doctrine.reindex (eqToHom objects) value))
        (second.predicates.doctrine.natural outgoing predicate).symm
    _ = targetModel.doctrine.reindex (first.morphism.toFamilyMorphism.base.map incoming)
        (first.predicates.doctrine.hom (ULift.up normalized) pulled) := by
      exact congrArg
        (targetModel.doctrine.reindex (first.morphism.toFamilyMorphism.base.map incoming)) compared
    _ = first.predicates.doctrine.hom (ULift.up Γ)
        (sourceDoctrine.reindex incoming pulled) :=
      (first.predicates.doctrine.natural incoming pulled).symm
    _ = first.predicates.doctrine.hom (ULift.up Γ) predicate := by
      have inverse : (incoming ≫ outgoing) =
          (𝟙 (⟨ULift.up Γ⟩ : (Interpretation.SourceModel.{u,z} D).toCwf.base.Context)) :=
        congrArg ULift.up comparison.inv_hom_id
      change (Interpretation.SourceModel.{u,z} D).toCwf.compS outgoing incoming =
        (Interpretation.SourceModel.{u,z} D).toCwf.idS (ULift.up Γ) at inverse
      have recovered : sourceDoctrine.reindex incoming pulled = predicate :=
        (sourceDoctrine.reindex_comp incoming outgoing predicate).symm.trans
          ((congrArg (fun arrow => sourceDoctrine.reindex arrow predicate) inverse).trans
            (sourceDoctrine.reindex_id predicate))
      exact congrArg (first.predicates.doctrine.hom (ULift.up Γ)) recovered

theorem correctedIso_predicate (Γ : (Interpretation.SourceModel.{u,z} D).toCwf.Ctx)
    (predicate : (Interpretation.sourceLocalModel.{u,z} D).doctrine.Predicate Γ) :
    targetModel.doctrine.reindex ((correctedIso headers first second).hom.base.app ⟨Γ⟩)
      (second.predicates.doctrine.hom Γ predicate) = first.predicates.doctrine.hom Γ predicate := by
  cases Γ with
  | up raw => exact correctedIso_predicate_raw headers first second raw predicate

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.ModelMapComparison

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.ClassifyingCells

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Refinement.Abstract ModelMapComparison

universe u z p
variable {S : Symbols.{u}} {D : Signature S}
  {C : CwfWithTerminal.{max u z,max u z,max u z,max u z}}
variable (headers : HeaderFormation D)
  (target : Interpretation.QualifiedModel.{u,max u z,max u z,max u z,max u z,p} D C)
  (first second : ModelMap (sourceModel.{u,z} headers).data target.data)

/-- All definable predicate readings commute for every declaration-admitted
corrected cell. This global compatibility is earned rather than admitted. -/
theorem admitted_predicate_coherence
    (candidate : CorrectedTransformationData first.morphism.toPseudo second.morphism.toPseudo)
    (admitted : PrimitiveAdmission headers target first second candidate)
    (Γ : (Interpretation.SourceModel.{u,z} D).toCwf.Ctx)
    (predicate : (sourceModel.{u,z} headers).localModel.doctrine.Predicate Γ) :
    target.localModel.doctrine.reindex (candidate.base.app ⟨Γ⟩)
      (second.predicates.doctrine.hom Γ predicate) = first.predicates.doctrine.hom Γ predicate := by
  rw [cell_unique headers target first second candidate admitted]
  exact correctedIso_predicate headers first second Γ predicate

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.ClassifyingCells
