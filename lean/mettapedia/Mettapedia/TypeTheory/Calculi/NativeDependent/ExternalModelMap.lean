import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalConstructorInterpretation
import Mettapedia.TypeTheory.ContextualTelescopeMorphism
import Mettapedia.TypeTheory.ContextualSumMorphism

/-!
# Local maps between independent external dependent models

The capabilities concern a strict contextual morphism, individual logical
constructors, and each primitive's finite parameter telescope and supplied
meaning. There is no compatibility field for complete expressions or
generated judgments. The image equations retain the chosen type
presentations; general pseudo logical comparisons are a separate interface.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualComprehensionMorphism
open Mettapedia.TypeTheory.ContextualTelescopeMorphism
open Mettapedia.TypeTheory.ContextualLogicalMorphism
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualTypeOperations

universe a c s t m

variable {S : Symbols.{a}} {C D : CwfWithTerminal.{c, s, t, m}}

/-- Declaration-local meanings over an actual strict contextual map. -/
structure ModelMap (source : ModelData S C) (target : ModelData S D) where
  morphism : StrictCwfMorphism C D
  logical : LogicalPreservation morphism source.products target.products
    source.sums.operations target.sums.operations
  typeParameters : ∀ symbol,
    ContextImage morphism (source.typeParameters symbol) (target.typeParameters symbol)
  typeFamily : ∀ symbol,
    HEq (morphism.toFamilyMorphism.mapType (source.typeFamily symbol)) (target.typeFamily symbol)
  termParameters : ∀ symbol,
    ContextImage morphism (source.termParameters symbol) (target.termParameters symbol)
  termType : ∀ symbol,
    HEq (morphism.toFamilyMorphism.mapType (source.termType symbol)) (target.termType symbol)
  termValue : ∀ symbol,
    HEq (morphism.toFamilyMorphism.mapTerm (source.termValue symbol)) (target.termValue symbol)

namespace ModelMap

variable {source : ModelData S C} {target : ModelData S D}
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
      (⟨source.products.pi A B, source.products.lam body⟩ : Value C.toCwf Γ)
      (⟨target.products.pi A' B', target.products.lam body'⟩ : Value D.toCwf Γ') :=
  ⟨mapping.logical.products.formation contexts domains codomains,
    mapping.logical.products.abstraction contexts domains codomains body body' bodies⟩

theorem application_image
    (function : C.toCwf.Tm Γ (source.products.pi A B))
    (function' : D.toCwf.Tm Γ' (target.products.pi A' B'))
    (functions : HEq (mapping.morphism.toFamilyMorphism.mapTerm function) function')
    (argument : C.toCwf.Tm Γ A) (argument' : D.toCwf.Tm Γ' A')
    (arguments : HEq (mapping.morphism.toFamilyMorphism.mapTerm argument) argument') :
    ValueImage mapping.morphism
      (⟨C.toCwf.tySub B (selfExtend C.toCwf argument), source.products.app function argument⟩ :
        Value C.toCwf Γ)
      (⟨D.toCwf.tySub B' (selfExtend D.toCwf argument'), target.products.app function' argument'⟩ :
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
      (⟨source.sums.operations.sigma A B, source.sums.operations.pair first second⟩ : Value C.toCwf Γ)
      (⟨target.sums.operations.sigma A' B', target.sums.operations.pair first' second'⟩ : Value D.toCwf Γ') :=
  ⟨mapping.logical.sums.formation contexts domains codomains,
    mapping.logical.sums.pairing contexts domains codomains first first' second second' firsts seconds⟩

theorem first_image (pair : C.toCwf.Tm Γ (source.sums.operations.sigma A B))
    (pair' : D.toCwf.Tm Γ' (target.sums.operations.sigma A' B'))
    (pairs : HEq (mapping.morphism.toFamilyMorphism.mapTerm pair) pair') :
    ValueImage mapping.morphism (⟨A, source.sums.operations.fst pair⟩ : Value C.toCwf Γ)
      (⟨A', target.sums.operations.fst pair'⟩ : Value D.toCwf Γ') :=
  ⟨domains, mapping.logical.sums.firstProjection contexts domains codomains pair pair' pairs⟩

theorem second_image (pair : C.toCwf.Tm Γ (source.sums.operations.sigma A B))
    (pair' : D.toCwf.Tm Γ' (target.sums.operations.sigma A' B'))
    (pairs : HEq (mapping.morphism.toFamilyMorphism.mapTerm pair) pair') :
    ValueImage mapping.morphism
      (⟨C.toCwf.tySub B (selfExtend C.toCwf (source.sums.operations.fst pair)),
        source.sums.operations.snd pair⟩ : Value C.toCwf Γ)
      (⟨D.toCwf.tySub B' (selfExtend D.toCwf (target.sums.operations.fst pair')),
        target.sums.operations.snd pair'⟩ : Value D.toCwf Γ') :=
  ⟨substituted_type_heq mapping.morphism contexts
      (extension_images mapping.morphism contexts domains) codomains
      (self_extension_heq mapping.morphism contexts domains _ _
        (mapping.logical.sums.firstProjection contexts domains codomains pair pair' pairs)),
    mapping.logical.sums.secondProjection contexts domains codomains pair pair' pairs⟩

/-- Full-motive elimination is earned from local sum constructors and the
actual packing/unpacking comparisons; it is not a model-map field. -/
theorem sumElimination_image
    (M : C.toCwf.Ty (C.toCwf.ext Γ (source.sums.operations.sigma A B)))
    (M' : D.toCwf.Ty (D.toCwf.ext Γ' (target.sums.operations.sigma A' B')))
    (motives : HEq (mapping.morphism.toFamilyMorphism.mapType M) M')
    (body : C.toCwf.Tm (C.toCwf.ext (C.toCwf.ext Γ A) B)
      (C.toCwf.tySub M (pack source.sums A B)))
    (body' : D.toCwf.Tm (D.toCwf.ext (D.toCwf.ext Γ' A') B')
      (D.toCwf.tySub M' (pack target.sums A' B')))
    (bodies : HEq (mapping.morphism.toFamilyMorphism.mapTerm body) body')
    (pair : C.toCwf.Tm Γ (source.sums.operations.sigma A B))
    (pair' : D.toCwf.Tm Γ' (target.sums.operations.sigma A' B'))
    (pairs : HEq (mapping.morphism.toFamilyMorphism.mapTerm pair) pair') :
    ValueImage mapping.morphism
      (⟨C.toCwf.tySub M (selfExtend C.toCwf pair),
        C.toCwf.tmSub (eliminate source.sums A B M body) (selfExtend C.toCwf pair)⟩ : Value C.toCwf Γ)
      (⟨D.toCwf.tySub M' (selfExtend D.toCwf pair'),
        D.toCwf.tmSub (eliminate target.sums A' B' M' body') (selfExtend D.toCwf pair')⟩ : Value D.toCwf Γ') :=
  ⟨substituted_type_heq mapping.morphism contexts
      (extension_images mapping.morphism contexts
        (mapping.logical.sums.formation contexts domains codomains)) motives
      (self_extension_heq mapping.morphism contexts
        (mapping.logical.sums.formation contexts domains codomains) pair pair' pairs),
    elimination_application_heq mapping.morphism source.sums target.sums mapping.logical.sums
      contexts domains codomains M M' motives body body' bodies pair pair' pairs⟩

end ModelMap

end Mettapedia.TypeTheory.Calculi.NativeDependent.External
