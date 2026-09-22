import Mettapedia.OSLF.Framework.WMCalculusNativeCapabilityTransport
import Mettapedia.OSLF.Framework.WMCalculusReadingCategory

/-!
# Functorial supported-query capabilities

A specialized WM backend is a lawful reading together with a supported-query
predicate. Its arrows preserve the WM signature and carry supported requests
to supported requests. The supported-request context and dependent answer
graph are functors, naturally isomorphic over this category. This relative
isomorphism does not imply that an unsupported request has an answer.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusCapabilityCategory

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusNativeCapability
open Mettapedia.OSLF.Framework.WMCalculusNativeCapabilityTransport
open Mettapedia.OSLF.Framework.WMCalculusReadingCategory

private abbrev wmLanguage : LanguageDef :=
  wmExtVertexLanguageDefWithCong wmExtVertexMinimal

/-- A lawful WM backend with an observationally coherent supported-query
capability. The underlying reading laws are not replaced. -/
structure LawfulCapability where
  model : LawfulReading
  capability : WMCapability model.reading

/-- Backend maps must preserve admitted requests as additional data. -/
structure CapabilityHom (source target : LawfulCapability) where
  readingMap : source.model ⟶ target.model
  support_forward : ∀ state query,
    source.capability.supports state query →
      target.capability.supports
        (readingMap.mapState state) (readingMap.mapQuery query)

instance : Category LawfulCapability where
  Hom := CapabilityHom
  id model := {
    readingMap := 𝟙 model.model
    support_forward := by intro state query supported; exact supported }
  comp f g := {
    readingMap := f.readingMap ≫ g.readingMap
    support_forward := by
      intro state query supported
      exact g.support_forward _ _
        (f.support_forward state query supported) }
  id_comp := by
    intro source target hom
    cases hom
    rfl
  comp_id := by
    intro source target hom
    cases hom
    rfl
  assoc := by
    intro first second third fourth f g h
    cases f
    cases g
    cases h
    rfl

/-- Supported state-query contexts vary functorially over capability
backends. -/
def supportFunctor : LawfulCapability ⥤ languagePresheafObj wmLanguage where
  obj model := (supportPredicate model.capability).toFunctor
  map hom := supportMap hom.readingMap _ _ hom.support_forward
  map_id := by
    intro model
    ext X request
    apply Subtype.ext
    rfl
  map_comp := by
    intro first second third f g
    ext X request
    apply Subtype.ext
    rfl

/-- The supported dependent answer graph is also functorial. -/
def supportedAnswerFunctor : LawfulCapability ⥤
    languagePresheafObj wmLanguage where
  obj model := (supportedGraph model.capability).toFunctor
  map hom := supportedGraphMap hom.readingMap _ _ hom.support_forward
  map_id := by
    intro model
    ext X answer
    apply Subtype.ext
    rfl
  map_comp := by
    intro first second third f g
    ext X answer
    apply Subtype.ext
    rfl

/-- Forgetting an answer is natural under support-preserving backend maps. -/
def projectionNatTrans : supportedAnswerFunctor ⟶ supportFunctor where
  app model := graphToSupport model.capability
  naturality := by
    intro first second hom
    exact supportedGraphMap_projection hom.readingMap _ _ hom.support_forward

/-- Extraction is a natural section on the supported context. -/
def sectionNatTrans : supportFunctor ⟶ supportedAnswerFunctor where
  app model := supportAnswerSection model.capability
  naturality := by
    intro first second hom
    exact supportedGraphMap_section hom.readingMap _ _ hom.support_forward

/-- Partial capability answers are naturally total relative to their
support context, but not necessarily over all state-query requests. -/
def supportedAnswerNaturalIso :
    supportedAnswerFunctor ≅ supportFunctor where
  hom := projectionNatTrans
  inv := sectionNatTrans
  hom_inv_id := by
    ext model X answer
    exact congrFun (congrArg (fun f => f.app X)
      (supportAnswerSection_rightInverse model.capability)) answer
  inv_hom_id := by
    ext model X request
    exact congrFun (congrArg (fun f => f.app X)
      (supportAnswerSection_leftInverse model.capability)) request

end Mettapedia.OSLF.Framework.WMCalculusCapabilityCategory
