import Mettapedia.OSLF.Framework.WMCalculusReadingCategory

/-!
# Functorial dependent answers across WM backends

Lawful WM readings and their morphisms form a category. The native
state-query context and the dependent extraction graph are functors from
that category into the presheaf category of the authored WM language.
For total extraction, the graph projection and extraction section are
natural, inverse transformations. The partial supported-query graph does
not have this total section unless every request is supported.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusAnswerFunctor

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusNativeAnswers
open Mettapedia.OSLF.Framework.WMCalculusReadingMorphism
open Mettapedia.OSLF.Framework.WMCalculusReadingCategory

private abbrev wmLanguage : LanguageDef :=
  wmExtVertexLanguageDefWithCong wmExtVertexMinimal

/-- The native context of state-query requests is natural in a lawful
reading and its operation-preserving maps. -/
def stateQueryFunctor : LawfulReading ⥤ languagePresheafObj wmLanguage where
  obj model := stateQueryObj model.State model.Query
  map hom := hom.stateQueryMap
  map_id := by
    intro model
    ext X pair
    rfl
  map_comp := by
    intro first second third f g
    ext X pair
    rfl

/-- The dependent answer graph is functorial under reading morphisms. Its
map is the existing graph map, which preserves extracted evidence. -/
def answerGraphFunctor : LawfulReading ⥤ languagePresheafObj wmLanguage where
  obj model := (evidenceGraph model.reading).toFunctor
  map hom := hom.answerGraphMap
  map_id := by
    intro model
    exact ReadingMorphism.answerGraphMap_id model.reading
  map_comp := by
    intro first second third f g
    exact ReadingMorphism.answerGraphMap_comp f g

/-- Forgetting answer evidence commutes with backend substitution. -/
def projectionNatTrans : answerGraphFunctor ⟶ stateQueryFunctor where
  app model := graphToStateQuery model.reading
  naturality := by
    intro first second hom
    exact hom.answerGraphMap_projection

/-- Extracting the unique total answer is also natural in the backend. -/
def sectionNatTrans : stateQueryFunctor ⟶ answerGraphFunctor where
  app model := answerSection model.reading
  naturality := by
    intro first second hom
    exact hom.answerGraphMap_section

/-- Total extraction makes the dependent answer graph naturally
isomorphic to the state-query context. Partial capabilities deliberately
break this totality when some requests are unsupported. -/
def answerGraphNaturalIso : answerGraphFunctor ≅ stateQueryFunctor where
  hom := projectionNatTrans
  inv := sectionNatTrans
  hom_inv_id := by
    ext model X answer
    exact congrFun (congrArg (fun f => (f.app X))
      (answerSection_rightInverse model.reading)) answer
  inv_hom_id := by
    ext model X pair
    exact congrFun (congrArg (fun f => (f.app X))
      (answerSection_leftInverse model.reading)) pair

end Mettapedia.OSLF.Framework.WMCalculusAnswerFunctor
