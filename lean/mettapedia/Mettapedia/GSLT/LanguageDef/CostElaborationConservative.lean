import Mettapedia.GSLT.LanguageDef.CostElaborationReindex

/-!
# Conservative arrows for proof-relevant Cost elaborations

A general continued morphism preserves every authored Cost declaration, but
its target may add reflective quotation boundaries or new collection typing
candidates.  Either change can alter the constructor of a proof-relevant
region tree.  This file isolates the two exact reflection laws under which
the structural reindexing action exists.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Generated quotation classification is reflected as well as preserved.
The equality is stated on the complete generated Cost namespace because
region trees distinguish ordinary and quoted applications. -/
def CostQuoteClassificationNatural {source target : CIGSLT}
    (morphism : source.Morphism target) : Prop :=
  ∀ constructor,
    ReflectiveContextSupport.isQuoteConstructor
        target.costWholeReflectionProfile
        ((costPresentationSymbols
          morphism.underlying.structural.structural.symbols).constructor
          constructor) =
      ReflectiveContextSupport.isQuoteConstructor
        source.costWholeReflectionProfile constructor

/-- A target extension may not turn a rejected static collection fibre into
an admitted one after reindexing.  Positive witnesses need no extra law:
continued morphisms already map every selected source witness. -/
def CostCollectionRejectionPreserving {source target : CIGSLT}
    (morphism : source.Morphism target) : Prop :=
  ∀ (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext)
    (targetBound : List TypeExpr)
    (collectionType : CollType) (elements : List Pattern)
    (sourceType : TypeExpr),
    costStaticCollectionTypingChoices source color targetFree targetBound
        collectionType elements
        (mapTypeExpr (color.symbols source) sourceType) = [] →
      costStaticCollectionTypingChoices target color
        (targetFree.map morphism.costWholeStructural.symbols)
        (targetBound.map
          (mapTypeExpr morphism.costWholeStructural.symbols))
        collectionType
        (elements.map (mapPattern morphism.costWholeStructural.symbols))
        (mapTypeExpr (color.symbols target)
          (mapTypeExpr
            morphism.underlying.structural.structural.symbols sourceType)) = []

/-- The property-only admission bundle for reindexing exact Cost region
trees.  It stores no tree action and therefore cannot conceal a second
semantic authority. -/
structure CostElaborationReindexLaws {source target : CIGSLT}
    (morphism : source.Morphism target) : Prop where
  quoteClassificationNatural : CostQuoteClassificationNatural morphism
  collectionRejectionPreserving :
    CostCollectionRejectionPreserving morphism

namespace CostElaborationReindexLaws

/-- Exact generated quotation reflection specializes to either authored
static colour. -/
theorem quoteStatic_natural {source target : CIGSLT}
    {morphism : source.Morphism target}
    (laws : CostElaborationReindexLaws morphism)
    (color : CostStaticColor) (constructor : String) :
    ReflectiveContextSupport.isQuoteConstructor target.reflection.1
        (morphism.underlying.structural.structural.symbols.constructor
          constructor) =
      ReflectiveContextSupport.isQuoteConstructor source.reflection.1
        constructor := by
  have generated := laws.quoteClassificationNatural
    ((color.symbols source).constructor constructor)
  rw [morphism.mapConstructor_costStatic_natural] at generated
  simpa only [reflectiveIsQuoteConstructor_mapCostStatic] using generated

/-- Identity preserves both decomposition decisions. -/
def id (source : CIGSLT) :
    CostElaborationReindexLaws (CIGSLT.Morphism.id source) where
  quoteClassificationNatural := by
    intro constructor
    change ReflectiveContextSupport.isQuoteConstructor
        source.costWholeReflectionProfile
        ((costPresentationSymbols PresentationSymbols.id).constructor
          constructor) = _
    rw [costPresentationSymbols_id]
    rfl
  collectionRejectionPreserving := by
    intro color targetFree targetBound collectionType elements sourceType
      rejected
    change costStaticCollectionTypingChoices source color
        (targetFree.map
          (costPresentationSymbols PresentationSymbols.id))
        (targetBound.map
          (mapTypeExpr (costPresentationSymbols PresentationSymbols.id)))
        collectionType
        (elements.map
          (mapPattern (costPresentationSymbols PresentationSymbols.id)))
        (mapTypeExpr (color.symbols source)
          (mapTypeExpr PresentationSymbols.id sourceType)) = []
    rw [costPresentationSymbols_id,
      WellSorted.FreeTypeContext.map_id]
    have boundIdentity :
        targetBound.map (mapTypeExpr PresentationSymbols.id) =
          targetBound := by
      calc
        targetBound.map (mapTypeExpr PresentationSymbols.id) =
            targetBound.map _root_.id :=
          List.map_congr_left fun type _ => mapTypeExpr_id type
        _ = targetBound := List.map_id targetBound
    have elementsIdentity :
        elements.map (mapPattern PresentationSymbols.id) = elements := by
      calc
        elements.map (mapPattern PresentationSymbols.id) =
            elements.map _root_.id :=
          List.map_congr_left fun pattern _ => mapPattern_id pattern
        _ = elements := List.map_id elements
    rw [boundIdentity, elementsIdentity, mapTypeExpr_id]
    exact rejected

/-- Conservative decomposition admission is closed under composition. -/
def comp {first second third : CIGSLT}
    {left : first.Morphism second} {right : second.Morphism third}
    (leftLaws : CostElaborationReindexLaws left)
    (rightLaws : CostElaborationReindexLaws right) :
    CostElaborationReindexLaws (CIGSLT.Morphism.comp left right) where
  quoteClassificationNatural := by
    intro constructor
    change ReflectiveContextSupport.isQuoteConstructor
        third.costWholeReflectionProfile
        ((costPresentationSymbols
          (left.underlying.structural.structural.symbols.comp
            right.underlying.structural.structural.symbols)).constructor
          constructor) = _
    rw [costPresentationSymbols_comp]
    exact (rightLaws.quoteClassificationNatural _).trans
      (leftLaws.quoteClassificationNatural constructor)
  collectionRejectionPreserving := by
    intro color targetFree targetBound collectionType elements sourceType
      rejected
    have middleRejected :=
      leftLaws.collectionRejectionPreserving color targetFree targetBound
        collectionType elements sourceType rejected
    have targetRejected :=
      rightLaws.collectionRejectionPreserving color
        (targetFree.map left.costWholeStructural.symbols)
        (targetBound.map
          (mapTypeExpr left.costWholeStructural.symbols))
        collectionType
        (elements.map (mapPattern left.costWholeStructural.symbols))
        (mapTypeExpr
          left.underlying.structural.structural.symbols sourceType)
        middleRejected
    have generatedSymbolsComp :
        (CIGSLT.Morphism.comp left right).costWholeStructural.symbols =
          left.costWholeStructural.symbols.comp
            right.costWholeStructural.symbols := by
      exact costPresentationSymbols_comp
        left.underlying.structural.structural.symbols
        right.underlying.structural.structural.symbols
    rw [generatedSymbolsComp]
    have boundComposite :
        targetBound.map (mapTypeExpr
          (left.costWholeStructural.symbols.comp
            right.costWholeStructural.symbols)) =
          (targetBound.map
            (mapTypeExpr left.costWholeStructural.symbols)).map
            (mapTypeExpr right.costWholeStructural.symbols) := by
      rw [List.map_map]
      exact List.map_congr_left fun type _ =>
        mapTypeExpr_comp left.costWholeStructural.symbols
          right.costWholeStructural.symbols type
    have elementsComposite :
        elements.map (mapPattern
          (left.costWholeStructural.symbols.comp
            right.costWholeStructural.symbols)) =
          (elements.map
            (mapPattern left.costWholeStructural.symbols)).map
            (mapPattern right.costWholeStructural.symbols) := by
      rw [List.map_map]
      exact List.map_congr_left fun pattern _ =>
        mapPattern_comp left.costWholeStructural.symbols
          right.costWholeStructural.symbols pattern
    have sourceSymbolsComp :
        (CIGSLT.Morphism.comp left right).underlying.structural.structural.symbols =
          left.underlying.structural.structural.symbols.comp
            right.underlying.structural.structural.symbols := rfl
    rw [WellSorted.FreeTypeContext.map_comp, boundComposite,
      elementsComposite, sourceSymbolsComp, mapTypeExpr_comp]
    exact targetRejected

end CostElaborationReindexLaws

/-! ## The conservative base category

Proof-relevant region decompositions are functorial only along Cost₁ arrows
that reflect the two decomposition decisions above.  We therefore keep the
ordinary Cost₁ category unchanged and form a separate, arrow-restricted base
for the indexed elaboration family. -/

/-- A Cost₁ object viewed in the base over which exact elaborations reindex.
The wrapper permits a stricter morphism class without installing a competing
category instance on `CostOneDomainObject`. -/
structure CostElaborationBase where
  toCostOne : CostOneDomainObject

namespace CostElaborationBase

/-- A Cost₁ arrow together with exactly the reflection laws needed to map its
proof-relevant region decompositions structurally. -/
structure Morphism (source target : CostElaborationBase) where
  underlying : CostOneMorphism source.toCostOne target.toCostOne
  reindexLaws : CostElaborationReindexLaws
    underlying.underlying.underlying

namespace Morphism

/-- Conservative elaboration arrows are determined by their Cost₁ arrow;
the reindexing admission fields are propositions. -/
@[ext]
theorem ext {source target : CostElaborationBase}
    {first second : Morphism source target}
    (underlying : first.underlying = second.underlying) : first = second := by
  cases first
  cases second
  cases underlying
  rfl

/-- Identity reflects every decomposition decision. -/
def id (source : CostElaborationBase) : Morphism source source where
  underlying := CostOneMorphism.id source.toCostOne
  reindexLaws := CostElaborationReindexLaws.id
    source.toCostOne.source.toCIGSLT

/-- Conservative decomposition transport is closed under composition. -/
def comp {first second third : CostElaborationBase}
    (left : Morphism first second) (right : Morphism second third) :
    Morphism first third where
  underlying := CostOneMorphism.comp left.underlying right.underlying
  reindexLaws := CostElaborationReindexLaws.comp left.reindexLaws
    right.reindexLaws

end Morphism

/-- Exact proof-relevant Cost reindexing has its own conservative base
category.  It forgets to the broader Cost₁ category below. -/
instance : CategoryTheory.Category CostElaborationBase where
  Hom := Morphism
  id := Morphism.id
  comp := Morphism.comp
  id_comp morphism := by
    apply Morphism.ext
    apply CostOneMorphism.ext
    apply OrderedCIGSLT.Morphism.ext
    apply CIGSLT.Morphism.ext <;> rfl
  comp_id morphism := by
    apply Morphism.ext
    apply CostOneMorphism.ext
    apply OrderedCIGSLT.Morphism.ext
    apply CIGSLT.Morphism.ext <;> rfl
  assoc first second third := by
    apply Morphism.ext
    apply CostOneMorphism.ext
    apply OrderedCIGSLT.Morphism.ext
    apply CIGSLT.Morphism.ext <;> rfl

/-- Forget decomposition reflection while retaining the selected normalizer,
Cost₁ laws, and underlying ordered continued arrow. -/
def forget : CategoryTheory.Functor CostElaborationBase CostOneDomainObject where
  obj source := source.toCostOne
  map morphism := morphism.underlying
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Compact one-step Cost restricted to arrows that also transport exact
decomposition evidence.  Its codomain remains `OrderedCIGSLT`; no compact
Cost² closure is asserted. -/
def compactCostOneFunctor :
    CategoryTheory.Functor CostElaborationBase OrderedCIGSLT :=
  forget.comp Mettapedia.GSLT.LanguageDef.compactCostOneFunctor

end CostElaborationBase

end Mettapedia.GSLT.LanguageDef
