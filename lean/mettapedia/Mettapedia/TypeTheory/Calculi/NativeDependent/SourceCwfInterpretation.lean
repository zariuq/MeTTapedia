import Mettapedia.TypeTheory.Calculi.NativeDependent.SourceCwfDeclarations
import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableIndexedFibreReadout

/-!
# Native interpretation of source dependent declarations

Source comprehension gives the actual dependent family and its natural
sections. Generated object scopes are compared with represented source
contexts in both directions, retaining every generalized element. Raw
evaluation then proves realization of the independently authored headers.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfDeclarations

open _root_.CategoryTheory Opposite
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualModelTelescopes NativeLocalTypeFormers
open DisplayedPresheafTransport DisplayedPresheafComprehension

universe u w w'
variable {K : Cwf.{u, u, w, w'}}

noncomputable section

abbrev emptyScope : Scope (Base K) 0 := RepresentableDeclarations.emptyScope
abbrev objectMeaning (object : Base K) := RepresentableDeclarations.objectMeaning object
abbrev objectScope (object : Base K) := RepresentableDeclarations.objectScope object
abbrev objectName (object : Base K) := RepresentableDeclarations.objectName object
abbrev objectNameInverse (object : Base K) := RepresentableDeclarations.objectNameInverse object

def displayArrow {context : K.Ctx} (type : K.Ty context) : ArrowSymbol K :=
  ⟨⟨K.ext context type⟩, ⟨context⟩, K.wk type⟩

def sourceMeaning {context : K.Ctx} (type : K.Ty context) :
    NativeType (objectScope (⟨context⟩ : Base K)).1 :=
  RepresentableIndexedDeclarations.fibreMeaning (displayArrow type)

abbrev sourceFamily {context : K.Ctx} (type : K.Ty context) :
    DisplayedFamily (objectScope (⟨context⟩ : Base K)).1 := (sourceMeaning type).decoded

abbrev sourceScope {context : K.Ctx} (type : K.Ty context) : Scope (Base K) 2 :=
  (objectScope (⟨context⟩ : Base K)).snoc (sourceMeaning type)

/-- Interpret a source section through the generated object-context map. -/
def generatedSection {context : K.Ctx} {type : K.Ty context}
    (sectionValue : (CwfYoneda.family K type).sections) : (sourceMeaning type).decoded.sections :=
  reindexDisplayedSection (objectName (⟨context⟩ : Base K))
    (CwfYoneda.family K type) sectionValue

/-- Read a complete generated section on every represented source environment. -/
def originalSection {context : K.Ctx} {type : K.Ty context}
    (sectionValue : (sourceMeaning type).decoded.sections) : (CwfYoneda.family K type).sections where
  val point := sectionValue.val ⟨point.1, (objectNameInverse (⟨context⟩ : Base K)).app point.1 point.2⟩
  property := by
    intro first second change
    exact sectionValue.property ((objectNameInverse (⟨context⟩ : Base K)).mapElements.map change)

theorem original_generated_section {context : K.Ctx} {type : K.Ty context}
    (sectionValue : (CwfYoneda.family K type).sections) :
    originalSection (generatedSection sectionValue) = sectionValue := by
  apply (Functor.sections_ext_iff).2
  intro point
  rfl

theorem generated_original_section {context : K.Ctx} {type : K.Ty context}
    (sectionValue : (sourceMeaning type).decoded.sections) :
    generatedSection (originalSection sectionValue) = sectionValue := by
  apply (Functor.sections_ext_iff).2
  rintro ⟨world, singleton, environment⟩
  cases singleton
  rfl

/-- The generated object-context comparison gives a bijection of complete sections. -/
def generatedSectionEquiv {context : K.Ctx} (type : K.Ty context) :
    (CwfYoneda.family K type).sections ≃ (sourceMeaning type).decoded.sections where
  toFun := generatedSection
  invFun := originalSection
  left_inv := original_generated_section
  right_inv := generated_original_section

def sourceValue {context : K.Ctx} {type : K.Ty context} (term : K.Tm context type) :
    (sourceMeaning type).decoded.sections := generatedSection (CwfYoneda.interpretTerm K term)

/-- Arbitrary native sections of a generated source declaration are exactly
source terms, rather than only source terms' observations. -/
def sourceTermEquiv {context : K.Ctx} (type : K.Ty context) :
    K.Tm context type ≃ (sourceMeaning type).decoded.sections :=
  (CwfYoneda.termSectionEquiv K type).trans (generatedSectionEquiv type)

theorem sourceValue_current {context : K.Ctx} {type : K.Ty context}
    (term : K.Tm context type) (world : (Base K)ᵒᵖ)
    (environment : K.Sub world.unop.val context) :
    ((sourceValue term).val ⟨world, ⟨PUnit.unit, environment⟩⟩).val =
      K.pair environment type (K.tmSub term environment) := rfl

theorem sourceValue_injective {context : K.Ctx} {type : K.Ty context} :
    Function.Injective (sourceValue (K := K) (type := type)) :=
  (sourceTermEquiv type).injective

def forgetType {context : K.Ctx} (type : K.Ty context) : NativeType (sourceScope type).1 :=
  RepresentableIndexedDeclarations.forgetType (displayArrow type)

def forgetValue {context : K.Ctx} (type : K.Ty context) : (forgetType type).decoded.sections :=
  RepresentableIndexedDeclarations.forgetValue (displayArrow type)

def model (K : Cwf.{u, u, w, w'}) : ModelData (symbols K) (Base K) where
  typeParameters := fun symbol => match symbol with
    | .object _ => emptyScope
    | .source (context := context) _ => objectScope (⟨context⟩ : Base K)
  typeFamily := fun symbol => match symbol with
    | .object object => objectMeaning object
    | .source type => sourceMeaning type
  termParameters := fun symbol => match symbol with
    | .ordinary arrow => objectScope arrow.source
    | .source (context := context) _ => objectScope (⟨context⟩ : Base K)
    | .forget type => sourceScope type
  termType := fun symbol => match symbol with
    | .ordinary arrow => RepresentableDeclarations.arrowMeaning arrow
    | .source (type := type) _ => sourceMeaning type
    | .forget type => forgetType type
  termValue := fun symbol => match symbol with
    | .ordinary arrow => RepresentableDeclarations.arrowValue arrow
    | .source term => sourceValue term
    | .forget type => forgetValue type
  predicateParameters := fun symbol => objectScope symbol.down.domain
  predicateValue := fun symbol => symbol.down.predicate.preimage (objectName symbol.down.domain)

theorem object_read (object : Base K) {n : Nat} (scope : Scope (Base K) n) :
    (model K).evaluateType scope (objectType object n) =
      some ((objectMeaning object).reindex ((NativeModel (Base K)).toEmpty scope.1)) :=
  (model K).evaluate_family scope (.object object) Fin.elim0 ((NativeModel (Base K)).toEmpty scope.1)
    (fun position => Fin.elim0 position)

set_option backward.isDefEq.respectTransparency false in
theorem object_empty_read (object : Base K) :
    (model K).evaluateType emptyScope (objectType object 0) = some (objectMeaning object) := by
  have read := object_read object emptyScope
  have identity : (NativeModel (Base K)).toEmpty emptyScope.1 =
      (NativeModel (Base K)).toCwf.idS emptyScope.1 :=
    ((NativeModel (Base K)).toEmpty_unique _ _).symm
  change (model K).evaluateType emptyScope (objectType object 0) =
    some ((NativeModel (Base K)).toCwf.tySub (objectMeaning object)
      ((NativeModel (Base K)).toEmpty emptyScope.1)) at read
  rw [identity, (NativeModel (Base K)).toCwf.tySub_id] at read
  exact read

theorem object_context_read (object : Base K) :
    (model K).evaluateContext (objectContext object) = some (objectScope object) :=
  (model K).evaluateContext_snoc .nil (objectType object 0) emptyScope
    (objectMeaning object) rfl (object_empty_read object)

theorem variable_identity (object : Base K) :
    (model K).evaluateTerm (objectScope object) (.var 0) =
      some (((objectScope object).2.lookup 0).substitute
        ((NativeModel (Base K)).toCwf.idS (objectScope object).1)) := by
  rw [Value.substitute_identity]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem source_type_read {context : K.Ctx} (type : K.Ty context) :
    (model K).evaluateType (objectScope (⟨context⟩ : Base K)) (sourceType type (.var 0)) =
      some (sourceMeaning type) := by
  have read := (model K).evaluate_family (objectScope (⟨context⟩ : Base K)) (.source type)
    (singletonArgument (.var 0)) (𝟙 (objectScope (⟨context⟩ : Base K)).1) (by
      intro position
      cases position using Fin.cases with
      | zero => exact variable_identity (⟨context⟩ : Base K)
      | succ impossible => exact Fin.elim0 impossible)
  change (model K).evaluateType (objectScope (⟨context⟩ : Base K)) (sourceType type (.var 0)) =
    some ((NativeModel (Base K)).toCwf.tySub (sourceMeaning type)
      ((NativeModel (Base K)).toCwf.idS (objectScope (⟨context⟩ : Base K)).1)) at read
  rw [(NativeModel (Base K)).toCwf.tySub_id] at read
  exact read

theorem source_context_read {context : K.Ctx} (type : K.Ty context) :
    (model K).evaluateContext (sourceContext type) = some (sourceScope type) :=
  (model K).evaluateContext_snoc (objectContext (⟨context⟩ : Base K)) (sourceType type (.var 0))
    (objectScope (⟨context⟩ : Base K)) (sourceMeaning type)
    (object_context_read (⟨context⟩ : Base K)) (source_type_read type)

set_option backward.isDefEq.respectTransparency false in
theorem ordinary_result_read (arrow : ArrowSymbol K) :
    (model K).evaluateType (objectScope arrow.source) (objectType arrow.target 1) =
      some (RepresentableDeclarations.arrowMeaning arrow) := by
  have read := object_read arrow.target (objectScope arrow.source)
  have projection : (NativeModel (Base K)).toEmpty (objectScope arrow.source).1 =
      (NativeModel (Base K)).toCwf.wk (objectMeaning arrow.source) :=
    ((NativeModel (Base K)).toEmpty_unique _ _).symm
  rw [projection] at read
  exact read

/-- Declaration admission follows actual raw evaluation. -/
theorem realization (K : Cwf.{u, u, w, w'}) : SignatureRealization (model K) (signature K) where
  typeHeader := by
    intro symbol
    cases symbol with
    | object => rfl
    | source => exact object_context_read _
  termHeader := by
    intro symbol
    cases symbol with
    | ordinary => exact object_context_read _
    | source => exact object_context_read _
    | forget type => exact source_context_read type
  termResult := by
    intro symbol
    cases symbol with
    | ordinary arrow => exact ordinary_result_read arrow
    | source => exact source_type_read _
    | forget type => exact object_read _ (sourceScope type)
  predicateHeader := fun symbol => object_context_read symbol.down.domain

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfDeclarations
