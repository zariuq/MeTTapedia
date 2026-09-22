import Mettapedia.OSLF.Framework.WMCalculusNativeObservation

/-!
# The dependent query/answer family of a WM reading

The semantic extraction operation is presented in the existing full presheaf
predicate fibration as its graph over state-query pairs. Its comprehension
has a canonical section, is total over the state-query base, and determines a
unique evidence answer. This is dependent data: the admissible evidence value
is indexed by both the state and the query. No probability or computation
strategy is built into the graph.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusNativeAnswers

open _root_.CategoryTheory
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.PresheafNativeType
open Mettapedia.GSLT.Topos

private abbrev wmLanguage : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef :=
  wmExtVertexLanguageDefWithCong wmExtVertexMinimal

/-- State-query pairs in the same constructor-indexed presheaf category as
the authored WM language. -/
def stateQueryObj (State Query : Type) : languagePresheafObj wmLanguage :=
  (Functor.const (Opposite (ConstructorObj wmLanguage))).obj (State × Query)

/-- A candidate state-query-evidence triple. -/
def answerTripleObj (State Query V : Type) : languagePresheafObj wmLanguage :=
  (Functor.const (Opposite (ConstructorObj wmLanguage))).obj ((State × Query) × V)

/-- The evidence graph is a native dependent predicate: one admissible
answer for each state-query pair. -/
def evidenceGraph {State Query V : Type} (R : WMReading State Query V) :
    Subfunctor (answerTripleObj State Query V) where
  obj X := { triple | R.extract triple.1.1 triple.1.2 = triple.2 }
  map := by
    intro X Y f triple h
    exact h

/-- The graph predicates precisely the extraction equation at each stage. -/
theorem evidenceGraph_mem_iff {State Query V : Type}
    (R : WMReading State Query V)
    (X : Opposite (ConstructorObj wmLanguage))
    (state : State) (query : Query) (value : V) :
    ((state, query), value) ∈ (evidenceGraph R).obj X ↔
      R.extract state query = value :=
  Iff.rfl

/-- Wrong evidence is not silently admitted as an answer. -/
theorem wrongEvidence_not_mem {State Query V : Type}
    (R : WMReading State Query V)
    (X : Opposite (ConstructorObj wmLanguage))
    (state : State) (query : Query) (value : V)
    (wrong : R.extract state query ≠ value) :
    ((state, query), value) ∉ (evidenceGraph R).obj X := by
  simpa only [evidenceGraph_mem_iff] using wrong

/-- The interpreted WM syntax lands in the same dependent answer graph:
`Extract` denotes exactly the graph-selected evidence value. -/
theorem denote_extract_mem_graph {State Query V : Type}
    (R : WMReading State Query V)
    (X : Opposite (ConstructorObj wmLanguage))
    (worldTerm : WMTerm .state) (queryTerm : WMTerm .query) :
    ((R.denote worldTerm, R.denote queryTerm),
      R.denote (.extract worldTerm queryTerm)) ∈ (evidenceGraph R).obj X := by
  exact (evidenceGraph_mem_iff R X _ _ _).2 rfl

/-- Forget the evidence coordinate of a candidate answer. -/
def answerProjection (State Query V : Type) :
    answerTripleObj State Query V ⟶ stateQueryObj State Query where
  app X := TypeCat.ofHom (fun triple => triple.1)
  naturality := by
    intro X Y f
    rfl

/-- The answer family as an object of the full presheaf predicate category. -/
def answerNativeType {State Query V : Type} (R : WMReading State Query V) :
    FullPresheafGrothendieckObj wmLanguage where
  base := Opposite.op (answerTripleObj State Query V)
  fiber := evidenceGraph R

/-- The graph's inclusion followed by projection is the dependent context
map from admissible answers to state-query pairs. -/
def graphToStateQuery {State Query V : Type} (R : WMReading State Query V) :
    (evidenceGraph R).toFunctor ⟶ stateQueryObj State Query :=
  (evidenceGraph R).ι ≫ answerProjection State Query V

/-- Extraction gives a section of the dependent answer graph. -/
def answerSection {State Query V : Type} (R : WMReading State Query V) :
    stateQueryObj State Query ⟶ (evidenceGraph R).toFunctor where
  app X := TypeCat.ofHom (fun pair =>
    ⟨(pair, R.extract pair.1 pair.2), rfl⟩)
  naturality := by
    intro X Y f
    rfl

/-- The dependent section returns the state-query pair it was given. -/
theorem answerSection_leftInverse {State Query V : Type}
    (R : WMReading State Query V) :
    answerSection R ≫ graphToStateQuery R = 𝟙 (stateQueryObj State Query) := by
  ext X pair
  rfl

/-- Any admissible answer is the extracted one, so the section is also a
right inverse. -/
theorem answerSection_rightInverse {State Query V : Type}
    (R : WMReading State Query V) :
    graphToStateQuery R ≫ answerSection R = 𝟙 (evidenceGraph R).toFunctor := by
  ext X triple
  cases triple with
  | mk triple h =>
    cases triple with
    | mk pair evidence =>
      apply Subtype.ext
      change (pair, R.extract pair.1 pair.2) = (pair, evidence)
      exact congrArg (Prod.mk pair) h

/-- The graph comprehension is canonically isomorphic to the context of
state-query pairs, with extraction as its section. -/
def answerGraphIso {State Query V : Type} (R : WMReading State Query V) :
    (evidenceGraph R).toFunctor ≅ stateQueryObj State Query where
  hom := graphToStateQuery R
  inv := answerSection R
  hom_inv_id := answerSection_rightInverse R
  inv_hom_id := answerSection_leftInverse R

/-- The Σ-image of admissible answers covers the whole state-query base;
every question has an evidence value in a WM reading. -/
theorem evidenceGraph_sigma_total {State Query V : Type}
    (R : WMReading State Query V) :
    (presheafChangeOfBase (ConstructorObj wmLanguage)).directImage
      (answerProjection State Query V) (evidenceGraph R) = ⊤ := by
  change Subfunctor.image (evidenceGraph R) (answerProjection State Query V) = ⊤
  ext X pair
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨(pair, R.extract pair.1 pair.2), rfl, rfl⟩

end Mettapedia.OSLF.Framework.WMCalculusNativeAnswers
