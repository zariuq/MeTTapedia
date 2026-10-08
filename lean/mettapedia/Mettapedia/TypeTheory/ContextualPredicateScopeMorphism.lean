import Mettapedia.TypeTheory.ContextualPredicateMorphism
import Mettapedia.TypeTheory.ContextualPredicateModelScopes
import Mettapedia.TypeTheory.ContextualTelescopeMorphism

/-!
# Actual mixed-scope images of contextual predicate morphisms

Data binders use the mapped comprehension and its generic variable. Predicate
assumptions use their actual selected context and inclusion. The resulting
finite variable readings retain all supplied dependent values, and successful
guarded argument assembly computes the mapped substitution. No comparison of
complete expressions or generated rule trees is a capability field.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualPredicateScopeMorphism

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateCapabilities ContextualPredicateMorphism
open ContextualPredicateModelScopes ContextualModelTelescopes
open ContextualComprehensionMorphism
open ContextualTelescopeMorphism (ValueImage imageArrow imageArrow_heq imageType imageType_heq)

universe c s t m p q
variable {C D : CwfWithTerminal.{c,s,t,m}}
  {source : PredicateDoctrine.{c,s,t,m,p} C.toCwf}
  {target : PredicateDoctrine.{c,s,t,m,q} D.toCwf}
  {sourceAssumptions : AssumptionOperations source}
  {targetAssumptions : AssumptionOperations target}

structure ScopeImage (F : StrictCwfMorphism C D) {n : Nat}
    (first : Scope C source sourceAssumptions n)
    (second : Scope D target targetAssumptions n) : Prop where
  contexts : context F first.1 = second.1
  variableReadouts : ∀ index, ValueImage F (first.2.lookup index) (second.2.lookup index)

theorem assumption_images {F : StrictCwfMorphism C D}
    {predicates : DoctrinePreservation F source target}
    (preserved : AssumptionPreservation predicates sourceAssumptions targetAssumptions)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx} (contexts : context F Γ = Γ')
    {φ : source.Predicate Γ} {φ' : target.Predicate Γ'}
    (values : HEq (predicates.hom Γ φ) φ') :
    context F (sourceAssumptions.assumed Γ φ) = targetAssumptions.assumed Γ' φ' := by
  cases contexts
  cases eq_of_heq values
  exact congrArg ContextualBase.Context.val (preserved.assumed Γ φ)

theorem inclusion_heq {F : StrictCwfMorphism C D}
    {predicates : DoctrinePreservation F source target}
    (preserved : AssumptionPreservation predicates sourceAssumptions targetAssumptions)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx} (contexts : context F Γ = Γ')
    {φ : source.Predicate Γ} {φ' : target.Predicate Γ'}
    (values : HEq (predicates.hom Γ φ) φ') :
    HEq (F.toFamilyMorphism.base.map
      (show C.toCwf.Sub (sourceAssumptions.assumed Γ φ) Γ from sourceAssumptions.inclusion φ))
      (show D.toCwf.Sub (targetAssumptions.assumed Γ' φ') Γ' from targetAssumptions.inclusion φ') := by
  cases contexts
  cases eq_of_heq values
  have read := preserved.inclusion φ
  exact (heq_of_eq read).trans
    (eqToHom_hom_heq (E := D.toCwf) (preserved.assumed Γ φ) _)

theorem substituted_predicate_heq {F : StrictCwfMorphism C D}
    (preserved : DoctrinePreservation F source target)
    {Γ Δ : C.toCwf.Ctx} {Γ' Δ' : D.toCwf.Ctx}
    (sources : context F Γ = Γ') (targets : context F Δ = Δ')
    {predicate : source.Predicate Δ} {predicate' : target.Predicate Δ'}
    (values : HEq (preserved.hom Δ predicate) predicate')
    {substitution : C.toCwf.Sub Γ Δ} {substitution' : D.toCwf.Sub Γ' Δ'}
    (arrows : HEq (F.toFamilyMorphism.base.map substitution) substitution') :
    HEq (preserved.hom Γ (source.reindex substitution predicate))
      (target.reindex substitution' predicate') := by
  rw [preserved.natural substitution predicate]
  cases sources
  cases targets
  cases eq_of_heq values
  cases eq_of_heq arrows
  rfl

namespace ScopeImage

theorem nil (F : StrictCwfMorphism C D) :
    ScopeImage F (Scope.nil C source sourceAssumptions)
      (Scope.nil D target targetAssumptions) :=
  ⟨congrArg ContextualBase.Context.val F.empty_preserved, fun index => Fin.elim0 index⟩

theorem snoc (F : StrictCwfMorphism C D) {n : Nat}
    {Γ : Scope C source sourceAssumptions n} {Γ' : Scope D target targetAssumptions n}
    (previous : ScopeImage F Γ Γ') {A : C.toCwf.Ty Γ.1} {A' : D.toCwf.Ty Γ'.1}
    (types : HEq (F.toFamilyMorphism.mapType A) A') :
    ScopeImage F (Γ.snoc A) (Γ'.snoc A') := by
  have extensions := extension_images F previous.contexts types
  have weakenings := (projection_heq F Γ.1 A).trans (wk_heq previous.contexts types)
  refine ⟨extensions, ?_⟩
  intro index
  cases index using Fin.cases with
  | zero =>
      exact ⟨substituted_type_heq F extensions previous.contexts types weakenings,
        (variable_heq F Γ.1 A).trans (vz_heq previous.contexts types)⟩
  | succ index =>
      exact (previous.variableReadouts index).substitute F extensions previous.contexts weakenings

theorem assume (F : StrictCwfMorphism C D)
    {predicates : DoctrinePreservation F source target}
    (preserved : AssumptionPreservation predicates sourceAssumptions targetAssumptions)
    {n : Nat} {Γ : Scope C source sourceAssumptions n}
    {Γ' : Scope D target targetAssumptions n} (previous : ScopeImage F Γ Γ')
    {φ : source.Predicate Γ.1} {φ' : target.Predicate Γ'.1}
    (values : HEq (predicates.hom Γ.1 φ) φ') :
    ScopeImage F (Γ.assume φ) (Γ'.assume φ') := by
  refine ⟨assumption_images preserved previous.contexts values, ?_⟩
  intro index
  exact (previous.variableReadouts index).substitute F
    (assumption_images preserved previous.contexts values) previous.contexts
    (inclusion_heq preserved previous.contexts values)

theorem components (F : StrictCwfMorphism C D) {n : Nat}
    {Δ : Scope C source sourceAssumptions n} {Δ' : Scope D target targetAssumptions n}
    (targets : ScopeImage F Δ Δ') {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (sources : context F Γ = Γ') (σ : C.toCwf.Sub Γ Δ.1) (index : Fin n) :
    ValueImage F (Δ.2.components σ index)
      (Δ'.2.components (imageArrow F sources targets.contexts σ) index) :=
  (targets.variableReadouts index).substitute F sources targets.contexts
    (imageArrow_heq F sources targets.contexts σ)

theorem assemble (F : StrictCwfMorphism C D) {n : Nat}
    {Δ : Scope C source sourceAssumptions n} {Δ' : Scope D target targetAssumptions n}
    (targets : ScopeImage F Δ Δ') {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (sources : context F Γ = Γ')
    (supplied : Fin n → Option (Value C.toCwf Γ))
    (supplied' : Fin n → Option (Value D.toCwf Γ'))
    (σ : C.toCwf.Sub Γ Δ.1) (assembled : Δ.2.assemble? supplied = some σ)
    (values : ∀ index value, supplied index = some value →
      ∃ value', supplied' index = some value' ∧ ValueImage F value value') :
    Δ'.2.assemble? supplied' = some (imageArrow F sources targets.contexts σ) := by
  apply (ScopeData.assemble?_eq_some_iff _ _ _).mpr
  intro index
  have sourceRead := ScopeData.assemble?_sound _ _ σ assembled index
  rcases values index _ sourceRead with ⟨value', targetRead, related⟩
  have actual := targets.components F sources σ index
  have equalTypes : value'.1 =
      (Δ'.2.components (imageArrow F sources targets.contexts σ) index).1 :=
    eq_of_heq (related.types.symm.trans actual.types)
  have equalValues : value' =
      Δ'.2.components (imageArrow F sources targets.contexts σ) index :=
    Sigma.ext equalTypes (related.terms.symm.trans actual.terms)
  exact targetRead.trans (congrArg some equalValues)

end ScopeImage

def imagePredicate {F : StrictCwfMorphism C D}
    (preserved : DoctrinePreservation F source target)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx} (contexts : context F Γ = Γ')
    (predicate : source.Predicate Γ) : target.Predicate Γ' :=
  contexts ▸ preserved.hom Γ predicate

theorem imagePredicate_heq {F : StrictCwfMorphism C D}
    (preserved : DoctrinePreservation F source target)
    {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx} (contexts : context F Γ = Γ')
    (predicate : source.Predicate Γ) :
    HEq (preserved.hom Γ predicate) (imagePredicate preserved contexts predicate) :=
  (transport_heq contexts _).symm

/-- The chosen mixed image is built from its actual binders, including every
guarded assumption, rather than selected from its endpoint alone. -/
def mixedImage (F : StrictCwfMorphism C D)
    {predicates : DoctrinePreservation F source target}
    (preserved : AssumptionPreservation predicates sourceAssumptions targetAssumptions) :
    {n : Nat} → {Γ : C.toCwf.Ctx} → (scope : ScopeData C source sourceAssumptions n Γ) →
      {targetScope : Scope D target targetAssumptions n // ScopeImage F ⟨Γ, scope⟩ targetScope}
  | _, _, .nil => ⟨Scope.nil D target targetAssumptions, ScopeImage.nil F⟩
  | _, _, .snoc previous type =>
      let earlier := mixedImage F preserved previous
      let actual := imageType F earlier.property.contexts type
      ⟨earlier.val.snoc actual, earlier.property.snoc F (imageType_heq F _ type)⟩
  | _, _, .assume previous predicate =>
      let earlier := mixedImage F preserved previous
      let actual := imagePredicate predicates earlier.property.contexts predicate
      ⟨earlier.val.assume actual, earlier.property.assume F preserved
        (imagePredicate_heq predicates _ predicate)⟩

def imageScope (F : StrictCwfMorphism C D)
    {predicates : DoctrinePreservation F source target}
    (preserved : AssumptionPreservation predicates sourceAssumptions targetAssumptions)
    {n : Nat} (scope : Scope C source sourceAssumptions n) :
    Scope D target targetAssumptions n :=
  (mixedImage F preserved scope.2).val

theorem imageScope_comparison (F : StrictCwfMorphism C D)
    {predicates : DoctrinePreservation F source target}
    (preserved : AssumptionPreservation predicates sourceAssumptions targetAssumptions)
    {n : Nat} (scope : Scope C source sourceAssumptions n) :
    ScopeImage F scope (imageScope F preserved scope) :=
  (mixedImage F preserved scope.2).property

@[simp] theorem imageScope_nil (F : StrictCwfMorphism C D)
    {predicates : DoctrinePreservation F source target}
    (preserved : AssumptionPreservation predicates sourceAssumptions targetAssumptions) :
    imageScope F preserved (Scope.nil C source sourceAssumptions) =
      Scope.nil D target targetAssumptions := rfl

theorem imageScope_snoc (F : StrictCwfMorphism C D)
    {predicates : DoctrinePreservation F source target}
    (preserved : AssumptionPreservation predicates sourceAssumptions targetAssumptions)
    {n : Nat} (scope : Scope C source sourceAssumptions n) (type : C.toCwf.Ty scope.1) :
    imageScope F preserved (scope.snoc type) = (imageScope F preserved scope).snoc
      (imageType F (imageScope_comparison F preserved scope).contexts type) := rfl

theorem imageScope_assume (F : StrictCwfMorphism C D)
    {predicates : DoctrinePreservation F source target}
    (preserved : AssumptionPreservation predicates sourceAssumptions targetAssumptions)
    {n : Nat} (scope : Scope C source sourceAssumptions n)
    (predicate : source.Predicate scope.1) :
    imageScope F preserved (scope.assume predicate) = (imageScope F preserved scope).assume
      (imagePredicate predicates (imageScope_comparison F preserved scope).contexts predicate) := rfl

end Mettapedia.TypeTheory.ContextualPredicateScopeMorphism
