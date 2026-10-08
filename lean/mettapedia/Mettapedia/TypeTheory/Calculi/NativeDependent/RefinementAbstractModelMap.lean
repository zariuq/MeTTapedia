import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractConstructorInterpretation
import Mettapedia.TypeTheory.ContextualPredicateScopeMorphism
import Mettapedia.TypeTheory.ContextualSumMorphism

/-!
# Local maps between independent mixed predicate models

An actual strict contextual morphism preserves local dependent constructors,
predicate fibres, ordinary proposition terms, satisfying assumption contexts
and complete refinement values. Each primitive retains its independently
supplied mixed header and family, section or predicate meaning. There is no
compatibility field for whole expressions or generated proof trees.

Successful value checks are preserved. Failure reflection is not required:
a contextual map may identify distinct type or predicate presentations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualComprehensionMorphism
open Mettapedia.TypeTheory.ContextualTelescopeMorphism
open Mettapedia.TypeTheory.ContextualLogicalMorphism
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualTypeOperations

universe a c s t m p q

open Mettapedia.TypeTheory.ContextualPredicateModel
open Mettapedia.TypeTheory.ContextualPredicateMorphism
open Mettapedia.TypeTheory.ContextualPredicateScopeMorphism

variable {S : Symbols.{a}} {C D : CwfWithTerminal.{c, s, t, m}}
  {sourceModel : LocalModel.{c,s,t,m,p} C} {targetModel : LocalModel.{c,s,t,m,q} D}

/-- Declaration-local meanings over an actual strict contextual map. -/
structure ModelMap (source : ModelData S C sourceModel) (target : ModelData S D targetModel) where
  morphism : StrictCwfMorphism C D
  logical : LogicalPreservation morphism sourceModel.products targetModel.products
    sourceModel.sums.operations targetModel.sums.operations
  predicates : PredicateLogicalPreservation morphism sourceModel targetModel
  typeParameters : ∀ symbol,
    ScopeImage morphism (source.typeParameters symbol) (target.typeParameters symbol)
  typeFamily : ∀ symbol,
    HEq (morphism.toFamilyMorphism.mapType (source.typeFamily symbol)) (target.typeFamily symbol)
  termParameters : ∀ symbol,
    ScopeImage morphism (source.termParameters symbol) (target.termParameters symbol)
  termType : ∀ symbol,
    HEq (morphism.toFamilyMorphism.mapType (source.termType symbol)) (target.termType symbol)
  termValue : ∀ symbol,
    HEq (morphism.toFamilyMorphism.mapTerm (source.termValue symbol)) (target.termValue symbol)
  predicateParameters : ∀ symbol,
    ScopeImage morphism (source.predicateParameters symbol) (target.predicateParameters symbol)
  predicateValue : ∀ symbol,
    HEq (predicates.doctrine.hom (source.predicateParameters symbol).1
      (source.predicateValue symbol)) (target.predicateValue symbol)

namespace ModelMap

variable {source : ModelData S C sourceModel} {target : ModelData S D targetModel}
variable (mapping : ModelMap source target)

theorem familyAt_image {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (contexts : context mapping.morphism Γ = Γ') (symbol : S.TypeSymbol)
    (arguments : C.toCwf.Sub Γ (source.typeParameters symbol).1) :
    HEq (mapping.morphism.toFamilyMorphism.mapType (source.familyAt symbol arguments))
      (target.familyAt symbol (imageArrow mapping.morphism contexts
        (mapping.typeParameters symbol).contexts arguments)) :=
  substituted_type_heq mapping.morphism contexts (mapping.typeParameters symbol).contexts
    (mapping.typeFamily symbol) (imageArrow_heq mapping.morphism contexts
      (mapping.typeParameters symbol).contexts arguments)

theorem primitiveAt_image {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (contexts : context mapping.morphism Γ = Γ') (symbol : S.TermSymbol)
    (arguments : C.toCwf.Sub Γ (source.termParameters symbol).1) :
    ValueImage mapping.morphism (source.primitiveAt symbol arguments)
      (target.primitiveAt symbol (imageArrow mapping.morphism contexts
        (mapping.termParameters symbol).contexts arguments)) :=
  ⟨substituted_type_heq mapping.morphism contexts (mapping.termParameters symbol).contexts
      (mapping.termType symbol) (imageArrow_heq mapping.morphism contexts
        (mapping.termParameters symbol).contexts arguments),
    substituted_term_heq mapping.morphism contexts (mapping.termParameters symbol).contexts
      (mapping.termType symbol) (mapping.termValue symbol) (imageArrow_heq mapping.morphism contexts
        (mapping.termParameters symbol).contexts arguments)⟩

theorem predicateAt_image {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (contexts : context mapping.morphism Γ = Γ') (symbol : S.PredicateSymbol)
    (arguments : C.toCwf.Sub Γ (source.predicateParameters symbol).1) :
    HEq (mapping.predicates.doctrine.hom Γ (source.predicateAt symbol arguments))
      (target.predicateAt symbol (imageArrow mapping.morphism contexts
        (mapping.predicateParameters symbol).contexts arguments)) :=
  substituted_predicate_heq mapping.predicates.doctrine contexts
    (mapping.predicateParameters symbol).contexts (mapping.predicateValue symbol)
    (imageArrow_heq mapping.morphism contexts
      (mapping.predicateParameters symbol).contexts arguments)

theorem proposition_image {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (contexts : context mapping.morphism Γ = Γ') :
    HEq (mapping.morphism.toFamilyMorphism.mapType (sourceModel.propositions.omega Γ))
      (targetModel.propositions.omega Γ') := by
  cases contexts
  exact heq_of_eq (mapping.predicates.propositions.formation Γ)

theorem quote_image {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (contexts : context mapping.morphism Γ = Γ')
    {predicate : sourceModel.doctrine.Predicate Γ}
    {predicate' : targetModel.doctrine.Predicate Γ'}
    (predicates : HEq (mapping.predicates.doctrine.hom Γ predicate) predicate') :
    ValueImage mapping.morphism
      (⟨sourceModel.propositions.omega Γ, sourceModel.propositions.quote predicate⟩ : Value C.toCwf Γ)
      (⟨targetModel.propositions.omega Γ', targetModel.propositions.quote predicate'⟩ : Value D.toCwf Γ') := by
  cases contexts
  cases eq_of_heq predicates
  exact ⟨heq_of_eq (mapping.predicates.propositions.formation Γ),
    mapping.predicates.propositions.quote predicate⟩

theorem holds_image {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (contexts : context mapping.morphism Γ = Γ')
    (term : C.toCwf.Tm Γ (sourceModel.propositions.omega Γ))
    (term' : D.toCwf.Tm Γ' (targetModel.propositions.omega Γ'))
    (terms : HEq (mapping.morphism.toFamilyMorphism.mapTerm term) term') :
    HEq (mapping.predicates.doctrine.hom Γ (sourceModel.propositions.holds term))
      (targetModel.propositions.holds term') := by
  cases contexts
  exact heq_of_eq (mapping.predicates.propositions.holds term term' terms)

theorem all_image {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (contexts : context mapping.morphism Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (types : HEq (mapping.morphism.toFamilyMorphism.mapType A) A')
    {predicate : sourceModel.doctrine.Predicate (C.toCwf.ext Γ A)}
    {predicate' : targetModel.doctrine.Predicate (D.toCwf.ext Γ' A')}
    (predicates : HEq (mapping.predicates.doctrine.hom (C.toCwf.ext Γ A) predicate) predicate') :
    HEq (mapping.predicates.doctrine.hom Γ (sourceModel.doctrine.all A predicate))
      (targetModel.doctrine.all A' predicate') := by
  cases contexts
  cases eq_of_heq types
  exact heq_of_eq (mapping.predicates.doctrine.all A predicate predicate' predicates)

theorem exists_image {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (contexts : context mapping.morphism Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (types : HEq (mapping.morphism.toFamilyMorphism.mapType A) A')
    {predicate : sourceModel.doctrine.Predicate (C.toCwf.ext Γ A)}
    {predicate' : targetModel.doctrine.Predicate (D.toCwf.ext Γ' A')}
    (predicates : HEq (mapping.predicates.doctrine.hom (C.toCwf.ext Γ A) predicate) predicate') :
    HEq (mapping.predicates.doctrine.hom Γ (sourceModel.doctrine.some A predicate))
      (targetModel.doctrine.some A' predicate') := by
  cases contexts
  cases eq_of_heq types
  exact heq_of_eq (mapping.predicates.doctrine.some A predicate predicate' predicates)

theorem refinement_image {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (contexts : context mapping.morphism Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (types : HEq (mapping.morphism.toFamilyMorphism.mapType A) A')
    {predicate : sourceModel.doctrine.Predicate (C.toCwf.ext Γ A)}
    {predicate' : targetModel.doctrine.Predicate (D.toCwf.ext Γ' A')}
    (predicates : HEq (mapping.predicates.doctrine.hom (C.toCwf.ext Γ A) predicate) predicate') :
    HEq (mapping.morphism.toFamilyMorphism.mapType (sourceModel.refinements.refined A predicate))
      (targetModel.refinements.refined A' predicate') := by
  cases contexts
  cases eq_of_heq types
  exact heq_of_eq (mapping.predicates.refinements.formation A predicate predicate' predicates)

theorem guard_image {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (contexts : context mapping.morphism Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (types : HEq (mapping.morphism.toFamilyMorphism.mapType A) A')
    {predicate : sourceModel.doctrine.Predicate (C.toCwf.ext Γ A)}
    {predicate' : targetModel.doctrine.Predicate (D.toCwf.ext Γ' A')}
    (predicates : HEq (mapping.predicates.doctrine.hom (C.toCwf.ext Γ A) predicate) predicate')
    (term : C.toCwf.Tm Γ A) (term' : D.toCwf.Tm Γ' A')
    (terms : HEq (mapping.morphism.toFamilyMorphism.mapTerm term) term')
    (guard : sourceModel.doctrine.reindex (selfExtend C.toCwf term) predicate = ⊤) :
    targetModel.doctrine.reindex (selfExtend D.toCwf term') predicate' = ⊤ := by
  have readings := substituted_predicate_heq mapping.predicates.doctrine contexts
    (extension_images mapping.morphism contexts types) predicates
    (self_extension_heq mapping.morphism contexts types term term' terms)
  rw [guard, map_top] at readings
  cases contexts
  exact (eq_of_heq readings).symm

theorem refine_image {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (contexts : context mapping.morphism Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (types : HEq (mapping.morphism.toFamilyMorphism.mapType A) A')
    {predicate : sourceModel.doctrine.Predicate (C.toCwf.ext Γ A)}
    {predicate' : targetModel.doctrine.Predicate (D.toCwf.ext Γ' A')}
    (predicates : HEq (mapping.predicates.doctrine.hom (C.toCwf.ext Γ A) predicate) predicate')
    (term : C.toCwf.Tm Γ A) (term' : D.toCwf.Tm Γ' A')
    (terms : HEq (mapping.morphism.toFamilyMorphism.mapTerm term) term')
    (guard : sourceModel.doctrine.reindex (selfExtend C.toCwf term) predicate = ⊤)
    (guard' : targetModel.doctrine.reindex (selfExtend D.toCwf term') predicate' = ⊤) :
    ValueImage mapping.morphism
      (⟨sourceModel.refinements.refined A predicate,
        sourceModel.refinements.intro A predicate term guard⟩ : Value C.toCwf Γ)
      (⟨targetModel.refinements.refined A' predicate',
        targetModel.refinements.intro A' predicate' term' guard'⟩ : Value D.toCwf Γ') := by
  have typeRead := mapping.refinement_image contexts types predicates
  refine ⟨typeRead, ?_⟩
  cases contexts
  cases eq_of_heq types
  cases eq_of_heq terms
  exact mapping.predicates.refinements.intro A predicate predicate' predicates term guard guard'

theorem forget_image {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
    (contexts : context mapping.morphism Γ = Γ')
    {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
    (types : HEq (mapping.morphism.toFamilyMorphism.mapType A) A')
    {predicate : sourceModel.doctrine.Predicate (C.toCwf.ext Γ A)}
    {predicate' : targetModel.doctrine.Predicate (D.toCwf.ext Γ' A')}
    (predicates : HEq (mapping.predicates.doctrine.hom (C.toCwf.ext Γ A) predicate) predicate')
    (term : C.toCwf.Tm Γ (sourceModel.refinements.refined A predicate))
    (term' : D.toCwf.Tm Γ' (targetModel.refinements.refined A' predicate'))
    (terms : HEq (mapping.morphism.toFamilyMorphism.mapTerm term) term') :
    ValueImage mapping.morphism
      (⟨A, sourceModel.refinements.forget A predicate term⟩ : Value C.toCwf Γ)
      (⟨A', targetModel.refinements.forget A' predicate' term'⟩ : Value D.toCwf Γ') := by
  refine ⟨types, ?_⟩
  cases contexts
  cases eq_of_heq types
  exact mapping.predicates.refinements.forget A predicate predicate' predicates term term' terms

variable {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
  (contexts : context mapping.morphism Γ = Γ')
  {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
  (domains : HEq (mapping.morphism.toFamilyMorphism.mapType A) A')
  {B : C.toCwf.Ty (C.toCwf.ext Γ A)} {B' : D.toCwf.Ty (D.toCwf.ext Γ' A')}
  (codomains : HEq (mapping.morphism.toFamilyMorphism.mapType B) B')

include contexts domains codomains

theorem lambda_image (body : C.toCwf.Tm (C.toCwf.ext Γ A) B)
    (body' : D.toCwf.Tm (D.toCwf.ext Γ' A') B')
    (bodies : HEq (mapping.morphism.toFamilyMorphism.mapTerm body) body') :
    ValueImage mapping.morphism
      (⟨sourceModel.products.pi A B, sourceModel.products.lam body⟩ : Value C.toCwf Γ)
      (⟨targetModel.products.pi A' B', targetModel.products.lam body'⟩ : Value D.toCwf Γ') :=
  ⟨mapping.logical.products.formation contexts domains codomains,
    mapping.logical.products.abstraction contexts domains codomains body body' bodies⟩

theorem application_image
    (function : C.toCwf.Tm Γ (sourceModel.products.pi A B))
    (function' : D.toCwf.Tm Γ' (targetModel.products.pi A' B'))
    (functions : HEq (mapping.morphism.toFamilyMorphism.mapTerm function) function')
    (argument : C.toCwf.Tm Γ A) (argument' : D.toCwf.Tm Γ' A')
    (arguments : HEq (mapping.morphism.toFamilyMorphism.mapTerm argument) argument') :
    ValueImage mapping.morphism
      (⟨C.toCwf.tySub B (selfExtend C.toCwf argument), sourceModel.products.app function argument⟩ :
        Value C.toCwf Γ)
      (⟨D.toCwf.tySub B' (selfExtend D.toCwf argument'), targetModel.products.app function' argument'⟩ :
        Value D.toCwf Γ') :=
  ⟨substituted_type_heq mapping.morphism contexts
      (extension_images mapping.morphism contexts domains) codomains
      (self_extension_heq mapping.morphism contexts domains argument argument' arguments),
    mapping.logical.products.application contexts domains codomains
      function function' argument argument' functions arguments⟩

theorem pair_image (first : C.toCwf.Tm Γ A) (first' : D.toCwf.Tm Γ' A')
    (firsts : HEq (mapping.morphism.toFamilyMorphism.mapTerm first) first')
    (second : C.toCwf.Tm Γ (C.toCwf.tySub B (selfExtend C.toCwf first)))
    (second' : D.toCwf.Tm Γ' (D.toCwf.tySub B' (selfExtend D.toCwf first')))
    (seconds : HEq (mapping.morphism.toFamilyMorphism.mapTerm second) second') :
    ValueImage mapping.morphism
      (⟨sourceModel.sums.operations.sigma A B, sourceModel.sums.operations.pair first second⟩ : Value C.toCwf Γ)
      (⟨targetModel.sums.operations.sigma A' B', targetModel.sums.operations.pair first' second'⟩ : Value D.toCwf Γ') :=
  ⟨mapping.logical.sums.formation contexts domains codomains,
    mapping.logical.sums.pairing contexts domains codomains first first' second second' firsts seconds⟩

theorem first_image (pair : C.toCwf.Tm Γ (sourceModel.sums.operations.sigma A B))
    (pair' : D.toCwf.Tm Γ' (targetModel.sums.operations.sigma A' B'))
    (pairs : HEq (mapping.morphism.toFamilyMorphism.mapTerm pair) pair') :
    ValueImage mapping.morphism (⟨A, sourceModel.sums.operations.fst pair⟩ : Value C.toCwf Γ)
      (⟨A', targetModel.sums.operations.fst pair'⟩ : Value D.toCwf Γ') :=
  ⟨domains, mapping.logical.sums.firstProjection contexts domains codomains pair pair' pairs⟩

theorem second_image (pair : C.toCwf.Tm Γ (sourceModel.sums.operations.sigma A B))
    (pair' : D.toCwf.Tm Γ' (targetModel.sums.operations.sigma A' B'))
    (pairs : HEq (mapping.morphism.toFamilyMorphism.mapTerm pair) pair') :
    ValueImage mapping.morphism
      (⟨C.toCwf.tySub B (selfExtend C.toCwf (sourceModel.sums.operations.fst pair)),
        sourceModel.sums.operations.snd pair⟩ : Value C.toCwf Γ)
      (⟨D.toCwf.tySub B' (selfExtend D.toCwf (targetModel.sums.operations.fst pair')),
        targetModel.sums.operations.snd pair'⟩ : Value D.toCwf Γ') :=
  ⟨substituted_type_heq mapping.morphism contexts
      (extension_images mapping.morphism contexts domains) codomains
      (self_extension_heq mapping.morphism contexts domains _ _
        (mapping.logical.sums.firstProjection contexts domains codomains pair pair' pairs)),
    mapping.logical.sums.secondProjection contexts domains codomains pair pair' pairs⟩

/-- Full-motive elimination is earned from local sum constructors and the
actual packing/unpacking comparisons; it is not a model-map field. -/
theorem sumElimination_image
    (M : C.toCwf.Ty (C.toCwf.ext Γ (sourceModel.sums.operations.sigma A B)))
    (M' : D.toCwf.Ty (D.toCwf.ext Γ' (targetModel.sums.operations.sigma A' B')))
    (motives : HEq (mapping.morphism.toFamilyMorphism.mapType M) M')
    (body : C.toCwf.Tm (C.toCwf.ext (C.toCwf.ext Γ A) B)
      (C.toCwf.tySub M (pack sourceModel.sums A B)))
    (body' : D.toCwf.Tm (D.toCwf.ext (D.toCwf.ext Γ' A') B')
      (D.toCwf.tySub M' (pack targetModel.sums A' B')))
    (bodies : HEq (mapping.morphism.toFamilyMorphism.mapTerm body) body')
    (pair : C.toCwf.Tm Γ (sourceModel.sums.operations.sigma A B))
    (pair' : D.toCwf.Tm Γ' (targetModel.sums.operations.sigma A' B'))
    (pairs : HEq (mapping.morphism.toFamilyMorphism.mapTerm pair) pair') :
    ValueImage mapping.morphism
      (⟨C.toCwf.tySub M (selfExtend C.toCwf pair),
        C.toCwf.tmSub (eliminate sourceModel.sums A B M body) (selfExtend C.toCwf pair)⟩ : Value C.toCwf Γ)
      (⟨D.toCwf.tySub M' (selfExtend D.toCwf pair'),
        D.toCwf.tmSub (eliminate targetModel.sums A' B' M' body') (selfExtend D.toCwf pair')⟩ : Value D.toCwf Γ') :=
  ⟨substituted_type_heq mapping.morphism contexts
      (extension_images mapping.morphism contexts
        (mapping.logical.sums.formation contexts domains codomains)) motives
      (self_extension_heq mapping.morphism contexts
        (mapping.logical.sums.formation contexts domains codomains) pair pair' pairs),
    elimination_application_heq mapping.morphism sourceModel.sums targetModel.sums mapping.logical.sums
      contexts domains codomains M M' motives body body' bodies pair pair' pairs⟩

end ModelMap

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract
