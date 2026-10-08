import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalModelMapCommutation
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalEvidenceExtraction

/-!
# Context, substitution and certificate readouts of local model maps

Canonical finite comprehension fixes the image telescope, not merely its
endpoint. Thus authored context equations and all dependent substitution
equations preserve their actual interpretations. The generated-certificate
comparison uses earned soundness and the independent raw evaluators.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualComprehensionMorphism
open Mettapedia.TypeTheory.ContextualTelescopeMorphism
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualPiEta

universe a c s t m

variable {S : Symbols.{a}} {C D : CwfWithTerminal.{c, s, t, m}}
  {source : ModelData S C} {target : ModelData S D}

namespace ModelMap

theorem evaluateContext_image (mapping : ModelMap source target) :
    {n : Nat} → (raw : ContextExpr S n) → (Γ : Context C n) →
    source.evaluateContext raw = some Γ →
    target.evaluateContext raw = some (imageContext mapping.morphism Γ)
  | _, .nil, Γ, evaluated => by
      have actual : Context.nil C = Γ := Option.some.inj evaluated
      rw [← actual, imageContext_nil]
      rfl
  | _, .snoc raw domain, Γ, evaluated => by
      rw [ModelData.evaluateContext] at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨previous, previousRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨A, typeRead, last⟩
      have actual : previous.snoc A = Γ := Option.some.inj last
      rw [← actual, imageContext_snoc]
      have previousImage := evaluateContext_image mapping raw previous previousRead
      have contexts := imageContext_comparison mapping.morphism previous
      rcases mapping.evaluateType_image domain previous _ contexts A typeRead with
        ⟨A', typeImage, types⟩
      have annotation : A' = imageType mapping.morphism contexts.contexts A :=
        eq_of_heq (types.symm.trans (imageType_heq mapping.morphism contexts.contexts A))
      rw [annotation] at typeImage
      exact target.evaluateContext_snoc raw domain _ _ previousImage typeImage

theorem evaluateType_image_unique (mapping : ModelMap source target) {n : Nat}
    (type : TypeExpr S n) (Γ : Context C n) (Γ' : Context D n)
    (contexts : ContextImage mapping.morphism Γ Γ')
    (A : C.toCwf.Ty Γ.1) (A' : D.toCwf.Ty Γ'.1)
    (sourceRead : source.evaluateType Γ type = some A)
    (targetRead : target.evaluateType Γ' type = some A') :
    HEq (mapping.morphism.toFamilyMorphism.mapType A) A' := by
  rcases mapping.evaluateType_image type Γ Γ' contexts A sourceRead with ⟨actual, read, related⟩
  cases Option.some.inj (read.symm.trans targetRead)
  exact related

theorem evaluateTerm_image_unique (mapping : ModelMap source target) {n : Nat}
    (term : TermExpr S n) (Γ : Context C n) (Γ' : Context D n)
    (contexts : ContextImage mapping.morphism Γ Γ')
    (value : Value C.toCwf Γ.1) (value' : Value D.toCwf Γ'.1)
    (sourceRead : source.evaluateTerm Γ term = some value)
    (targetRead : target.evaluateTerm Γ' term = some value') :
    ValueImage mapping.morphism value value' := by
  rcases mapping.evaluateTerm_image term Γ Γ' contexts value sourceRead with ⟨actual, read, related⟩
  cases Option.some.inj (read.symm.trans targetRead)
  exact related

theorem checked_image (mapping : ModelMap source target) {n : Nat}
    (type : TypeExpr S n) (term : TermExpr S n) (Γ : Context C n) (Γ' : Context D n)
    (contexts : ContextImage mapping.morphism Γ Γ') (A : C.toCwf.Ty Γ.1)
    (value : C.toCwf.Tm Γ.1 A) (typeRead : source.evaluateType Γ type = some A)
    (termRead : source.evaluateTerm Γ term = some ⟨A, value⟩) :
    ∃ A' : D.toCwf.Ty Γ'.1, ∃ value' : D.toCwf.Tm Γ'.1 A',
      target.evaluateType Γ' type = some A' ∧
      target.evaluateTerm Γ' term = some ⟨A', value'⟩ ∧
      ValueImage mapping.morphism (⟨A, value⟩ : Value C.toCwf Γ.1) ⟨A', value'⟩ := by
  rcases mapping.evaluateType_image type Γ Γ' contexts A typeRead with ⟨A', typeImage, types⟩
  rcases mapping.evaluateTerm_image term Γ Γ' contexts _ termRead with ⟨actual, termImage, related⟩
  rcases ValueImage.at_type mapping.morphism contexts.contexts types value actual related with
    ⟨value', valueRead, terms⟩
  rw [valueRead] at termImage
  exact ⟨A', value', typeImage, termImage, ⟨types, terms⟩⟩

theorem evaluateSubstitution_image (mapping : ModelMap source target) {n k : Nat}
    (Γ : Context C n) (Δ : Context C k) (Γ' : Context D n) (Δ' : Context D k)
    (sources : ContextImage mapping.morphism Γ Γ') (targets : ContextImage mapping.morphism Δ Δ')
    (substitution : Substitution S k n) (arrow : C.toCwf.Sub Γ.1 Δ.1)
    (evaluated : source.evaluateSubstitution Γ Δ substitution = some arrow) :
    target.evaluateSubstitution Γ' Δ' substitution =
      some (imageArrow mapping.morphism sources.contexts targets.contexts arrow) := by
  exact targets.assemble mapping.morphism sources.contexts _ _ arrow evaluated
    (fun index value read => mapping.evaluateTerm_image (substitution index) Γ Γ' sources value read)

/-- Every semantic judgment is preserved as a consequence of the actual
expression/context/substitution comparisons, including equations. -/
theorem interprets (mapping : ModelMap source target) {judgment : Judgment S}
    (interpreted : Interprets source judgment) : Interprets target judgment := by
  cases judgment with
  | context raw =>
      rcases interpreted with ⟨Γ, contextRead⟩
      exact ⟨_, mapping.evaluateContext_image raw Γ contextRead⟩
  | type raw type =>
      rcases interpreted with ⟨Γ, A, contextRead, typeRead⟩
      rcases mapping.evaluateType_image type Γ _ (imageContext_comparison _ Γ) A typeRead with
        ⟨A', typeImage, _⟩
      exact ⟨_, A', mapping.evaluateContext_image raw Γ contextRead, typeImage⟩
  | term raw term type =>
      rcases interpreted with ⟨Γ, A, value, contextRead, typeRead, termRead⟩
      rcases mapping.checked_image type term Γ _ (imageContext_comparison _ Γ) A value
        typeRead termRead with ⟨A', value', typeImage, termImage, _⟩
      exact ⟨_, A', value', mapping.evaluateContext_image raw Γ contextRead, typeImage, termImage⟩
  | substitution rawSource rawTarget substitution =>
      rcases interpreted with ⟨Γ, Δ, arrow, sourceRead, targetRead, arrowRead⟩
      exact ⟨_, _, _, mapping.evaluateContext_image rawSource Γ sourceRead,
        mapping.evaluateContext_image rawTarget Δ targetRead,
        mapping.evaluateSubstitution_image Γ Δ _ _ (imageContext_comparison _ Γ)
          (imageContext_comparison _ Δ) substitution arrow arrowRead⟩
  | contextEq first second =>
      rcases interpreted with ⟨Γ, firstRead, secondRead⟩
      exact ⟨_, mapping.evaluateContext_image first Γ firstRead,
        mapping.evaluateContext_image second Γ secondRead⟩
  | typeEq raw first second =>
      rcases interpreted with ⟨Γ, A, contextRead, firstRead, secondRead⟩
      have contexts := imageContext_comparison mapping.morphism Γ
      rcases mapping.evaluateType_image first Γ _ contexts A firstRead with ⟨A', firstImage, firstTypes⟩
      rcases mapping.evaluateType_image second Γ _ contexts A secondRead with ⟨A'', secondImage, secondTypes⟩
      have same : A'' = A' := eq_of_heq (secondTypes.symm.trans firstTypes)
      rw [same] at secondImage
      exact ⟨_, A', mapping.evaluateContext_image raw Γ contextRead, firstImage, secondImage⟩
  | termEq raw first second type =>
      rcases interpreted with ⟨Γ, A, value, contextRead, typeRead, firstRead, secondRead⟩
      have contexts := imageContext_comparison mapping.morphism Γ
      rcases mapping.checked_image type first Γ _ contexts A value typeRead firstRead with
        ⟨A', value', typeImage, firstImage, firstValues⟩
      rcases mapping.evaluateTerm_image second Γ _ contexts _ secondRead with
        ⟨actual, secondImage, secondValues⟩
      have equalValues : actual = ⟨A', value'⟩ :=
        Sigma.ext (eq_of_heq (secondValues.types.symm.trans firstValues.types))
          (secondValues.terms.symm.trans firstValues.terms)
      rw [equalValues] at secondImage
      exact ⟨_, A', value', mapping.evaluateContext_image raw Γ contextRead, typeImage, firstImage, secondImage⟩
  | substitutionEq rawSource rawTarget first second =>
      rcases interpreted with ⟨Γ, Δ, arrow, sourceRead, targetRead, firstRead, secondRead⟩
      have sources := imageContext_comparison mapping.morphism Γ
      have targets := imageContext_comparison mapping.morphism Δ
      exact ⟨_, _, _, mapping.evaluateContext_image rawSource Γ sourceRead,
        mapping.evaluateContext_image rawTarget Δ targetRead,
        mapping.evaluateSubstitution_image Γ Δ _ _ sources targets first arrow firstRead,
        mapping.evaluateSubstitution_image Γ Δ _ _ sources targets second arrow secondRead⟩

end ModelMap

namespace Derivation

variable {signature : Signature S}

/-- The local model-map laws carry the actual generated certificate's
interpretation; no whole-judgment preservation hypothesis is supplied. -/
theorem sound_modelMap (mapping : ModelMap source target)
    (realization : SignatureRealization source signature)
    (stable : StrictPiSubstitution source.products) (beta : PiBeta source.products)
    (eta : PiEta source.products stable.1) {judgment : Judgment S}
    (derivation : Derivation signature judgment) : Interprets target judgment :=
  mapping.interprets (derivation.sound source realization stable beta eta)

/-- Supplied source and target certificate readouts compare at the exact
image section, independently of the chosen derivation trees. -/
theorem termSection_modelMap (mapping : ModelMap source target)
    (sourceRealization : SignatureRealization source signature)
    (sourceStable : StrictPiSubstitution source.products) (sourceBeta : PiBeta source.products)
    (sourceEta : PiEta source.products sourceStable.1)
    (targetRealization : SignatureRealization target signature)
    (targetStable : StrictPiSubstitution target.products) (targetBeta : PiBeta target.products)
    (targetEta : PiEta target.products targetStable.1)
    {n : Nat} {raw : ContextExpr S n} {term : TermExpr S n} {type : TypeExpr S n}
    (first second : Derivation signature (.term raw term type))
    (Γ : Context C n) (Γ' : Context D n) (contexts : ContextImage mapping.morphism Γ Γ')
    (A : C.toCwf.Ty Γ.1) (A' : D.toCwf.Ty Γ'.1)
    (sourceContext : source.evaluateContext raw = some Γ)
    (sourceType : source.evaluateType Γ type = some A)
    (targetContext : target.evaluateContext raw = some Γ')
    (targetType : target.evaluateType Γ' type = some A') :
    HEq (mapping.morphism.toFamilyMorphism.mapTerm
      (first.termSection source sourceRealization sourceStable sourceBeta sourceEta
        Γ A sourceContext sourceType))
      (second.termSection target targetRealization targetStable targetBeta targetEta
        Γ' A' targetContext targetType) :=
  (mapping.evaluateTerm_image_unique term Γ Γ' contexts _ _
    (first.termSection_readout source sourceRealization sourceStable sourceBeta sourceEta
      Γ A sourceContext sourceType)
    (second.termSection_readout target targetRealization targetStable targetBeta targetEta
      Γ' A' targetContext targetType)).terms

end Derivation

end Mettapedia.TypeTheory.Calculi.NativeDependent.External
