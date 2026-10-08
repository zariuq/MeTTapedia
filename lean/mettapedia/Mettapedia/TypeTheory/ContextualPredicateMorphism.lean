import Mettapedia.TypeTheory.ContextualPredicateModel
import Mettapedia.TypeTheory.ContextualComprehensionMorphism

/-!
# Local predicate comparisons of contextual model maps

A contextual map acts on the actual Heyting predicate fibres, commutes with
substitution and preserves both display quantifiers. Ordinary proposition
terms, guarded assumption contexts and retained refinement terms have their
own local comparisons. No expression interpreter, generated judgment
soundness or classifying universal property is a field of these interfaces.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualPredicateMorphism

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateCapabilities ContextualPredicateModel
open ContextualComprehensionMorphism (context)
open ContextualProductComparison (selfExtend)

universe c s t m p q
variable {C D : CwfWithTerminal.{c,s,t,m}}

structure DoctrinePreservation (mapping : StrictCwfMorphism C D)
    (source : PredicateDoctrine.{c,s,t,m,p} C.toCwf)
    (target : PredicateDoctrine.{c,s,t,m,q} D.toCwf) where
  hom : (Γ : C.toCwf.Ctx) → HeytingHom (source.Predicate Γ) (target.Predicate (context mapping Γ))
  natural : ∀ {Γ Δ : C.toCwf.Ctx} (substitution : C.toCwf.Sub Γ Δ)
    (predicate : source.Predicate Δ),
    hom Γ (source.reindex substitution predicate) =
      target.reindex (mapping.toFamilyMorphism.base.map substitution) (hom Δ predicate)
  all : ∀ {Γ : C.toCwf.Ctx} (type : C.toCwf.Ty Γ)
    (predicate : source.Predicate (C.toCwf.ext Γ type))
    (body : target.Predicate (D.toCwf.ext (context mapping Γ) (mapping.toFamilyMorphism.mapType type))),
    HEq (hom (C.toCwf.ext Γ type) predicate) body →
      hom Γ (source.all type predicate) = target.all (mapping.toFamilyMorphism.mapType type) body
  some : ∀ {Γ : C.toCwf.Ctx} (type : C.toCwf.Ty Γ)
    (predicate : source.Predicate (C.toCwf.ext Γ type))
    (body : target.Predicate (D.toCwf.ext (context mapping Γ) (mapping.toFamilyMorphism.mapType type))),
    HEq (hom (C.toCwf.ext Γ type) predicate) body →
      hom Γ (source.some type predicate) = target.some (mapping.toFamilyMorphism.mapType type) body

namespace DoctrinePreservation

theorem guard {mapping : StrictCwfMorphism C D}
    {source : PredicateDoctrine.{c,s,t,m,p} C.toCwf}
    {target : PredicateDoctrine.{c,s,t,m,q} D.toCwf}
    (preserved : DoctrinePreservation mapping source target)
    {Γ Δ : C.toCwf.Ctx} (predicate : source.Predicate Δ) (substitution : C.toCwf.Sub Γ Δ)
    (evidence : source.reindex substitution predicate = ⊤) :
    target.reindex (mapping.toFamilyMorphism.base.map substitution) (preserved.hom Δ predicate) = ⊤ := by
  rw [← preserved.natural substitution predicate, evidence, map_top]

end DoctrinePreservation

structure PropositionPreservation {mapping : StrictCwfMorphism C D}
    {source : PredicateDoctrine.{c,s,t,m,p} C.toCwf}
    {target : PredicateDoctrine.{c,s,t,m,q} D.toCwf}
    (predicates : DoctrinePreservation mapping source target)
    (sourceOperations : PropositionOperations source) (targetOperations : PropositionOperations target) where
  formation : ∀ Γ : C.toCwf.Ctx,
    mapping.toFamilyMorphism.mapType (sourceOperations.omega Γ) =
      targetOperations.omega (context mapping Γ)
  quote : ∀ {Γ : C.toCwf.Ctx} (predicate : source.Predicate Γ),
    HEq (mapping.toFamilyMorphism.mapTerm (sourceOperations.quote predicate))
      (targetOperations.quote (predicates.hom Γ predicate))

namespace PropositionPreservation

theorem holds {mapping : StrictCwfMorphism C D}
    {source : PredicateDoctrine.{c,s,t,m,p} C.toCwf}
    {target : PredicateDoctrine.{c,s,t,m,q} D.toCwf}
    {predicates : DoctrinePreservation mapping source target}
    {sourceOperations : PropositionOperations source} {targetOperations : PropositionOperations target}
    (preserved : PropositionPreservation predicates sourceOperations targetOperations)
    {Γ : C.toCwf.Ctx} (term : C.toCwf.Tm Γ (sourceOperations.omega Γ))
    (value : D.toCwf.Tm (context mapping Γ) (targetOperations.omega (context mapping Γ)))
    (terms : HEq (mapping.toFamilyMorphism.mapTerm term) value) :
    predicates.hom Γ (sourceOperations.holds term) = targetOperations.holds value := by
  have quotations := preserved.quote (sourceOperations.holds term)
  rw [sourceOperations.quote_holds] at quotations
  have equal : targetOperations.quote (predicates.hom Γ (sourceOperations.holds term)) = value :=
    eq_of_heq (quotations.symm.trans terms)
  calc
    _ = targetOperations.holds (targetOperations.quote
        (predicates.hom Γ (sourceOperations.holds term))) := (targetOperations.holds_quote _).symm
    _ = _ := congrArg targetOperations.holds equal

end PropositionPreservation

structure AssumptionPreservation {mapping : StrictCwfMorphism C D}
    {source : PredicateDoctrine.{c,s,t,m,p} C.toCwf}
    {target : PredicateDoctrine.{c,s,t,m,q} D.toCwf}
    (predicates : DoctrinePreservation mapping source target)
    (sourceOperations : AssumptionOperations source) (targetOperations : AssumptionOperations target) where
  assumed : ∀ (Γ : C.toCwf.Ctx) (predicate : source.Predicate Γ),
    mapping.toFamilyMorphism.base.obj ⟨sourceOperations.assumed Γ predicate⟩ =
      (⟨targetOperations.assumed (context mapping Γ) (predicates.hom Γ predicate)⟩ : D.toCwf.base.Context)
  inclusion : ∀ {Γ : C.toCwf.Ctx} (predicate : source.Predicate Γ),
    mapping.toFamilyMorphism.base.map (show C.toCwf.Sub (sourceOperations.assumed Γ predicate) Γ from
      sourceOperations.inclusion predicate) = eqToHom (assumed Γ predicate) ≫
        (show D.toCwf.Sub (targetOperations.assumed (context mapping Γ) (predicates.hom Γ predicate))
          (context mapping Γ) from targetOperations.inclusion (predicates.hom Γ predicate))

namespace AssumptionPreservation

theorem select {mapping : StrictCwfMorphism C D}
    {source : PredicateDoctrine.{c,s,t,m,p} C.toCwf}
    {target : PredicateDoctrine.{c,s,t,m,q} D.toCwf}
    {predicates : DoctrinePreservation mapping source target}
    {sourceOperations : AssumptionOperations source} {targetOperations : AssumptionOperations target}
    (preserved : AssumptionPreservation predicates sourceOperations targetOperations)
    {Γ Δ : C.toCwf.Ctx} (predicate : source.Predicate Δ) (substitution : C.toCwf.Sub Γ Δ)
    (evidence : source.reindex substitution predicate = ⊤) :
    mapping.toFamilyMorphism.base.map (sourceOperations.select predicate substitution evidence) ≫
      eqToHom (preserved.assumed Δ predicate) =
        targetOperations.select (predicates.hom Δ predicate)
          (mapping.toFamilyMorphism.base.map substitution) (predicates.guard predicate substitution evidence) := by
  apply targetOperations.inclusion_monic (predicates.hom Δ predicate)
  change (mapping.toFamilyMorphism.base.map (sourceOperations.select predicate substitution evidence) ≫
      eqToHom (preserved.assumed Δ predicate)) ≫ targetOperations.inclusion (predicates.hom Δ predicate) =
    targetOperations.select (predicates.hom Δ predicate)
      (mapping.toFamilyMorphism.base.map substitution) (predicates.guard predicate substitution evidence) ≫
        targetOperations.inclusion (predicates.hom Δ predicate)
  calc
    _ = mapping.toFamilyMorphism.base.map (sourceOperations.select predicate substitution evidence) ≫
        mapping.toFamilyMorphism.base.map (sourceOperations.inclusion predicate) := by
      rw [Category.assoc, preserved.inclusion predicate]
    _ = mapping.toFamilyMorphism.base.map
        (sourceOperations.select predicate substitution evidence ≫ sourceOperations.inclusion predicate) :=
      (mapping.toFamilyMorphism.base.map_comp _ _).symm
    _ = mapping.toFamilyMorphism.base.map substitution :=
      congrArg mapping.toFamilyMorphism.base.map (sourceOperations.select_beta predicate substitution evidence)
    _ = _ := (targetOperations.select_beta (predicates.hom Δ predicate)
      (mapping.toFamilyMorphism.base.map substitution) (predicates.guard predicate substitution evidence)).symm

end AssumptionPreservation

structure RefinementPreservation {mapping : StrictCwfMorphism C D}
    {source : PredicateDoctrine.{c,s,t,m,p} C.toCwf}
    {target : PredicateDoctrine.{c,s,t,m,q} D.toCwf}
    (predicates : DoctrinePreservation mapping source target)
    (sourceOperations : RefinementOperations source) (targetOperations : RefinementOperations target) where
  formation : ∀ {Γ : C.toCwf.Ctx} (type : C.toCwf.Ty Γ)
    (predicate : source.Predicate (C.toCwf.ext Γ type))
    (body : target.Predicate (D.toCwf.ext (context mapping Γ) (mapping.toFamilyMorphism.mapType type))),
    HEq (predicates.hom (C.toCwf.ext Γ type) predicate) body →
      mapping.toFamilyMorphism.mapType (sourceOperations.refined type predicate) =
        targetOperations.refined (mapping.toFamilyMorphism.mapType type) body
  intro : ∀ {Γ : C.toCwf.Ctx} (type : C.toCwf.Ty Γ)
    (predicate : source.Predicate (C.toCwf.ext Γ type))
    (body : target.Predicate (D.toCwf.ext (context mapping Γ) (mapping.toFamilyMorphism.mapType type))),
    HEq (predicates.hom (C.toCwf.ext Γ type) predicate) body →
      ∀ (term : C.toCwf.Tm Γ type)
        (guard : source.reindex (selfExtend C.toCwf term) predicate = ⊤)
        (transportedGuard : target.reindex (selfExtend D.toCwf (mapping.toFamilyMorphism.mapTerm term)) body = ⊤),
      HEq (mapping.toFamilyMorphism.mapTerm (sourceOperations.intro type predicate term guard))
        (targetOperations.intro (mapping.toFamilyMorphism.mapType type) body
          (mapping.toFamilyMorphism.mapTerm term) transportedGuard)
  forget : ∀ {Γ : C.toCwf.Ctx} (type : C.toCwf.Ty Γ)
    (predicate : source.Predicate (C.toCwf.ext Γ type))
    (body : target.Predicate (D.toCwf.ext (context mapping Γ) (mapping.toFamilyMorphism.mapType type))),
    HEq (predicates.hom (C.toCwf.ext Γ type) predicate) body →
      ∀ (term : C.toCwf.Tm Γ (sourceOperations.refined type predicate))
        (value : D.toCwf.Tm (context mapping Γ)
          (targetOperations.refined (mapping.toFamilyMorphism.mapType type) body)),
      HEq (mapping.toFamilyMorphism.mapTerm term) value →
      HEq (mapping.toFamilyMorphism.mapTerm (sourceOperations.forget type predicate term))
        (targetOperations.forget (mapping.toFamilyMorphism.mapType type) body value)

structure PredicateLogicalPreservation (mapping : StrictCwfMorphism C D)
    (source : LocalModel.{c,s,t,m,p} C) (target : LocalModel.{c,s,t,m,q} D) where
  doctrine : DoctrinePreservation mapping source.doctrine target.doctrine
  propositions : PropositionPreservation doctrine source.propositions target.propositions
  assumptions : AssumptionPreservation doctrine source.assumptions target.assumptions
  refinements : RefinementPreservation doctrine source.refinements target.refinements

end Mettapedia.TypeTheory.ContextualPredicateMorphism
