import Mettapedia.GSLT.LanguageDef.ElaboratedSection
import Mettapedia.GSLT.LanguageDef.CostRegionNormalization

/-!
# The proof-relevant Cost carrier and compact factorization boundary

`CostElabTerm` is the semantic carrier selected by proof-relevant region
decomposition.  Reflection-certified `Pattern` remains its checked compact
execution format.  This module packages that relationship without imposing
compact faithfulness.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory

/-- The complete typed-open index of one proof-relevant Cost term.  Bundling
all three dependent indices is what permits the elaboration family to be a
single ordinary `Type`-valued functor. -/
structure CostElaborationIndex (source : CIGSLT) where
  targetFree : WellSorted.FreeTypeContext
  targetBound : List TypeExpr
  targetSort : LangSort source.costWholeLanguage

/-- The exact proof-relevant fibre over one Cost authority.  Its payload is
the checked compact term together with its retained `CostRegionTree`; no
normalizer, restoration theorem, or independently selected kernel is stored
again in the fibre. -/
abbrev CostElaborationFiber (source : CIGSLT) :=
  Σ index : CostElaborationIndex source,
    CostElabTerm source index.targetFree index.targetBound index.targetSort

namespace CIGSLT

/-- The complete Cost region elaboration as a proof-relevant carrier over the
generated authored presentation. -/
def costOpenElaborationCarrier (source : CIGSLT) :
    ReflectiveOpenElaborationCarrier source.costIGSLT
      source.costWholeAdmittedReflection where
  Carrier := CostElabTerm source
  erase := CostOpenElaboration.erase
  compile := CostOpenElaboration.compileTerm source
  erase_compile := CostOpenElaboration.erase_compileTerm source

@[simp]
theorem costOpenElaborationCarrier_erase_compile
    (source : CIGSLT)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage
        free bound sort) :
    source.costOpenElaborationCarrier.erase
        (source.costOpenElaborationCarrier.compile term) = term :=
  source.costOpenElaborationCarrier.erase_compile term

/-- Compact Cost observation is exactly the generic pullback of the authored
open equation setoid along proof-relevant erasure. -/
theorem costCompactObservationSetoid_eq_pullback
    (source : CIGSLT)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (sort : LangSort source.costWholeLanguage) :
    CostOpenElaboration.costCompactObservationSetoid source free bound sort =
      source.costOpenElaborationCarrier.compactObservationSetoid
        free bound sort :=
  rfl

/-- Compact erasure is faithful when it never identifies two elaborated Cost
terms in the same typed open fiber. -/
def CostCompactErasureFaithful (source : CIGSLT) : Prop :=
  ∀ (targetFree : WellSorted.FreeTypeContext) (targetBound : List TypeExpr)
    (targetSort : LangSort source.costWholeLanguage),
    Function.Injective
      (source.costOpenElaborationCarrier.erase :
        CostElabTerm source targetFree targetBound targetSort →
          ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
            source.costWholeLanguage targetFree targetBound targetSort)

/-- Every compact term has at most one proof-relevant Cost elaboration.

The compiler already supplies an inhabitant, so this says each fiber of the
erasure projection is contractible rather than merely inhabited. -/
def CostElaborationFibersSubsingleton (source : CIGSLT) : Prop :=
  ∀ (targetFree : WellSorted.FreeTypeContext) (targetBound : List TypeExpr)
    (targetSort : LangSort source.costWholeLanguage)
    (term : ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage targetFree targetBound targetSort),
    Subsingleton (CostOpenElaboration source term)

/-- Faithfulness of compact erasure is exactly subsingletonness of every
proof-relevant elaboration fiber. -/
theorem costCompactErasureFaithful_iff_fibersSubsingleton
    (source : CIGSLT) :
    source.CostCompactErasureFaithful ↔
      source.CostElaborationFibersSubsingleton := by
  constructor
  · intro faithful targetFree targetBound targetSort term
    refine ⟨?_⟩
    intro first second
    have equal :
        (⟨term, first⟩ : CostElabTerm source targetFree targetBound targetSort) =
          ⟨term, second⟩ :=
      faithful targetFree targetBound targetSort rfl
    cases equal
    rfl
  · intro subsingleton targetFree targetBound targetSort left right erased
    cases left with
    | mk leftTerm leftElaboration =>
      cases right with
      | mk rightTerm rightElaboration =>
        dsimp only [costOpenElaborationCarrier,
          CostOpenElaboration.erase] at erased
        subst rightTerm
        have elaborationEquality : leftElaboration = rightElaboration :=
          (subsingleton targetFree targetBound targetSort leftTerm).elim _ _
        subst rightElaboration
        rfl

/-- Faithful erasure is a sufficient condition for exact normalization to
factor through compact syntax.  The converse is intentionally not claimed:
distinct elaborations may normalize to the same compact representative. -/
theorem compactNormalizationCoherent_of_erasureFaithful
    (source : CIGSLT) (faithful : source.CostCompactErasureFaithful) :
    CompactCostNormalizationCoherent source := by
  intro targetFree targetBound targetSort term first second
  have equal :
      (⟨term, first⟩ : CostElabTerm source targetFree targetBound targetSort) =
        ⟨term, second⟩ :=
    faithful targetFree targetBound targetSort rfl
  exact congrArg (fun elaboration => elaboration.2.normalizeErasure) equal

/-- Exact semantic normalization factors through compact syntax when one raw
normalizer reproduces the normalized erasure of every elaboration.

This is stronger than unary authored equivalence.  It says proof-relevant
choices are unobservable after normalization, precisely the property that
fails at the rho Cost² overlap. -/
def CostNormalizationFactorsThroughCompactErasure (source : CIGSLT) : Prop :=
  ∃ normalize : ∀ {free bound sort},
      ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
          source.costWholeLanguage free bound sort →
        ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
          source.costWholeLanguage free bound sort,
    ∀ {free bound sort}
      (term : ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
        source.costWholeLanguage free bound sort)
      (elaboration : CostOpenElaboration source term),
      elaboration.normalizeErasure = normalize term

/-- Compact factorization is equivalent to exact normalized-erasure
coherence.  This theorem prevents a non-faithful compact backend from being
silently promoted to the semantic carrier. -/
theorem costNormalizationFactorsThroughCompactErasure_iff
    (source : CIGSLT) :
    source.CostNormalizationFactorsThroughCompactErasure ↔
      CompactCostNormalizationCoherent source := by
  constructor
  · rintro ⟨normalize, factors⟩
    intro free bound sort term first second
    exact (factors term first).trans (factors term second).symm
  · intro coherent
    refine ⟨fun term => source.costNormalizeOpen term, ?_⟩
    intro free bound sort term elaboration
    exact elaboration.normalizeErasure_eq_costNormalizeOpen coherent

/-- Failure of compact coherence is exactly failure of any normalization
factorization through compact erasure. -/
theorem not_costNormalizationFactorsThroughCompactErasure_iff
    (source : CIGSLT) :
    ¬ source.CostNormalizationFactorsThroughCompactErasure ↔
      ¬ CompactCostNormalizationCoherent source := by
  rw [source.costNormalizationFactorsThroughCompactErasure_iff]

end CIGSLT

end Mettapedia.GSLT.LanguageDef
