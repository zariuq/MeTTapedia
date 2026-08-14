import Mettapedia.GSLT.LanguageDef.CostElaborationTransportSound

/-!
# Exact sections on proof-relevant Cost syntax

This module states the executable data required for an exact canonical section
on the proof-relevant Cost carrier.  Its semantic relation is generated only
by transported edges of the authored Cost presentation.  Compact execution is
a separate agreement law: it may erase distinct semantic fibres to the same
raw normal form without identifying those fibres upstairs.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory

/-- A chosen exact normalizer for one proof-relevant Cost semantics.

The static lift is the canonical maximal relation of fully witnessed
`CostStaticPlanEdge`s; an object cannot substitute a hidden permissive edge
family.  The two proof fields are precisely the local obligations used by the
generic least-equivalence construction: every term reaches its normal form,
and one proof-relevant structural edge receives equal normal forms. -/
structure CostElaboratedSectionData (source : CIGSLT) where
  transportSound :
    source.CostStructuralTransportSound source.costStaticPlanLift
  normalize : ∀ {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage},
    CostElabTerm source targetFree targetBound targetSort →
      CostElabTerm source targetFree targetBound targetSort
  normalizationPath : ∀ {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : CostElabTerm source targetFree targetBound targetSort),
    (source.costStructuralSemantics source.costStaticPlanLift
      transportSound).relation
      targetFree targetBound targetSort (normalize term) term
  transportInvariant : ∀ {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : CostElabTerm source targetFree targetBound targetSort},
    CostRegionTreeTransport source source.costStaticPlanLift targetFree
        left.2.tree right.2.tree →
      normalize left = normalize right

/-- The independently defined child-first Cost normalizer reaches the input
through the lawful occurrence semantics.  This is the substantive transport
obligation: recompiling the normalized compact pattern must not silently
change retained colour, declaration, collection, or boundary fibres. -/
def CostElaborationNormalizationPath (source : CIGSLT)
    (sound : source.CostStructuralTransportSound
      source.costStaticPlanLift) : Prop :=
  ∀ {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : CostElabTerm source targetFree targetBound targetSort),
    (source.costStructuralSemantics source.costStaticPlanLift sound).relation
      targetFree targetBound targetSort
        (CostOpenElaboration.normalizeTerm source term) term

/-- One lawful proof-relevant structural transport receives equal normalized
elaborated outputs.  The conclusion is stated first at normalized erasure,
before deterministic checked recompilation packages the evidence again. -/
def CostElaborationTransportInvariant (source : CIGSLT) : Prop :=
  ∀ {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : CostElabTerm source targetFree targetBound targetSort},
    CostRegionTreeTransport source source.costStaticPlanLift targetFree
        left.2.tree right.2.tree →
      left.2.normalizeErasure = right.2.normalizeErasure

/-- Exact laws for the fixed, independently defined proof-relevant Cost
normalizer.  Unlike `CostElaboratedSectionData`, this bundle does not permit
an object to choose an arbitrary normalizer. -/
structure CostElaboratedNormalizationLaws (source : CIGSLT) : Prop where
  transportSound :
    source.CostStructuralTransportSound source.costStaticPlanLift
  normalizationPath :
    CostElaborationNormalizationPath source transportSound
  transportInvariant : CostElaborationTransportInvariant source

namespace CostElaboratedNormalizationLaws

/-- The fixed child-first normalizer and its two local laws construct the
generic exact section data. -/
def sectionData {source : CIGSLT}
    (laws : CostElaboratedNormalizationLaws source) :
    CostElaboratedSectionData source where
  transportSound := laws.transportSound
  normalize := CostOpenElaboration.normalizeTerm source
  normalizationPath := laws.normalizationPath
  transportInvariant := by
    intro targetFree targetBound targetSort left right transport
    unfold CostOpenElaboration.normalizeTerm
    rw [laws.transportInvariant transport]

end CostElaboratedNormalizationLaws

namespace CostElaboratedSectionData

/-- The exact semantic relation selected by the transported static kernel. -/
def semantics {source : CIGSLT}
    (data : CostElaboratedSectionData source) :
    ReflectiveOpenElaborationSemantics source.costOpenElaborationCarrier :=
  source.costStructuralSemantics source.costStaticPlanLift data.transportSound

/-- The local normalization data induces an exact section on every typed open
proof-relevant Cost fibre. -/
def canonicalSection {source : CIGSLT}
    (data : CostElaboratedSectionData source) :
    ReflectiveOpenElaborationSemantics.ComputableSection data.semantics :=
  ReflectiveOpenElaborationSemantics.ComputableSection.ofPathInvariant
    (source.costStructuralPathLift source.costStaticPlanLift
      data.transportSound)
    data.normalize data.normalizationPath data.transportInvariant

/-- Elaborated equivalence is exactly equality of the selected semantic
normal forms. -/
theorem equivalent_iff_normalize_eq {source : CIGSLT}
    (data : CostElaboratedSectionData source)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (left right : CostElabTerm source targetFree targetBound targetSort) :
    (data.semantics.relation targetFree targetBound targetSort).r left right ↔
      data.normalize left = data.normalize right :=
  ReflectiveOpenElaborationSemantics.ComputableSection.equivalent_iff_normalize_eq
    data.canonicalSection left right

/-- Exact elaborated normalization remains an authored equation path after
forgetting Cost evidence. -/
theorem normalize_erases_equivalent {source : CIGSLT}
    (data : CostElaboratedSectionData source)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : CostElabTerm source targetFree targetBound targetSort) :
    (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
      source.costWholeReflectionProfile defaultBasePremises
        source.costWholeLanguage targetFree targetBound
          (.base targetSort.1)).r
      (CostOpenElaboration.erase (data.normalize term))
      (CostOpenElaboration.erase term) :=
  ReflectiveOpenElaborationSemantics.ComputableSection.normalize_erases_equivalent
    data.canonicalSection term

/-- Semantic normalization stays in the retained root fibre. -/
theorem normalize_rootIdentity_eq {source : CIGSLT}
    (data : CostElaboratedSectionData source)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : CostElabTerm source targetFree targetBound targetSort) :
    (data.normalize term).decoration.rootIdentity =
      term.decoration.rootIdentity :=
  source.costStructuralSemantics_rootIdentity_eq source.costStaticPlanLift
    data.transportSound (data.normalizationPath term)

/-- Distinct retained root identities force distinct semantic normal forms. -/
theorem normalize_ne_of_rootIdentity_ne {source : CIGSLT}
    (data : CostElaboratedSectionData source)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : CostElabTerm source targetFree targetBound targetSort}
    (different : left.decoration.rootIdentity ≠
      right.decoration.rootIdentity) :
    data.normalize left ≠ data.normalize right := by
  intro equality
  apply different
  calc
    left.decoration.rootIdentity =
        (data.normalize left).decoration.rootIdentity :=
      (data.normalize_rootIdentity_eq left).symm
    _ = (data.normalize right).decoration.rootIdentity :=
      congrArg (fun term : CostElabTerm source targetFree targetBound targetSort =>
        term.decoration.rootIdentity) equality
    _ = right.decoration.rootIdentity :=
      data.normalize_rootIdentity_eq right

end CostElaboratedSectionData

/-- Agreement between semantic normalization and one explicitly selected
compact Cost executor.

The normalizer is part of the statement.  This is essential for hereditary
Cost objects: a language may reject the reference executor while admitting
a repaired normalizer.  The law is still only an erasure theorem, not semantic
faithfulness: different elaborated normal forms may erase to the same compact
result. -/
structure CostElaboratedCompactificationFor {source : CIGSLT}
    (data : CostElaboratedSectionData source)
    (normalizeOpen : CostOpenNormalizer source) : Prop where
  erases_normalize : ∀ {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : CostElabTerm source targetFree targetBound targetSort),
    CostOpenElaboration.erase (data.normalize term) =
      normalizeOpen (CostOpenElaboration.erase term)

/-- Compatibility specialization to the original reference Cost executor.  New
Cost objects should expose their selected normalizer and use
`CostElaboratedCompactificationFor` directly. -/
abbrev CostReferenceElaboratedCompactification {source : CIGSLT}
    (data : CostElaboratedSectionData source) : Prop :=
  CostElaboratedCompactificationFor data source.costNormalizeOpen

namespace CostElaboratedCompactificationFor

/-- Equal compact inputs have equal compact normal forms for any explicitly
selected compact executor. -/
theorem normalizedErasure_eq_of_erase_eq {source : CIGSLT}
    {data : CostElaboratedSectionData source}
    {normalizeOpen : CostOpenNormalizer source}
    (compactification : CostElaboratedCompactificationFor data normalizeOpen)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : CostElabTerm source targetFree targetBound targetSort}
    (sameErasure : CostOpenElaboration.erase left =
      CostOpenElaboration.erase right) :
    CostOpenElaboration.erase (data.normalize left) =
      CostOpenElaboration.erase (data.normalize right) := by
  rw [compactification.erases_normalize,
    compactification.erases_normalize, sameErasure]

/-- The selected compactifier may intentionally merge observations without
collapsing the proof-relevant semantic fibres that produced them. -/
theorem sameCompact_but_distinctNormalForms {source : CIGSLT}
    {data : CostElaboratedSectionData source}
    {normalizeOpen : CostOpenNormalizer source}
    (compactification : CostElaboratedCompactificationFor data normalizeOpen)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {left right : CostElabTerm source targetFree targetBound targetSort}
    (sameErasure : CostOpenElaboration.erase left =
      CostOpenElaboration.erase right)
    (different : left.decoration.rootIdentity ≠
      right.decoration.rootIdentity) :
    CostOpenElaboration.erase (data.normalize left) =
        CostOpenElaboration.erase (data.normalize right) ∧
      data.normalize left ≠ data.normalize right :=
  ⟨compactification.normalizedErasure_eq_of_erase_eq sameErasure,
    data.normalize_ne_of_rootIdentity_ne different⟩

end CostElaboratedCompactificationFor

namespace CostReferenceElaboratedCompactification

/-- Exact compact normalization agreement is optional additional structure.
It follows on the compact-coherent subcategory, but is deliberately not part
of the general Cost₁ object because the rho Cost² overlap refutes it. -/
def ofCompactCoherent {source : CIGSLT}
    (laws : CostElaboratedNormalizationLaws source)
    (coherent : CompactCostNormalizationCoherent source) :
    CostReferenceElaboratedCompactification laws.sectionData where
  erases_normalize := by
    intro targetFree targetBound targetSort term
    exact term.2.normalizeErasure_eq_costNormalizeOpen coherent

/-- For the fixed child-first normalizer, a global normalization-commuting
compactifier exists exactly on the already identified compact-coherent
subcategory.  Thus the extra square cannot be hidden inside general Cost₁
closure. -/
theorem iff_compactCostNormalizationCoherent {source : CIGSLT}
    (laws : CostElaboratedNormalizationLaws source) :
    CostReferenceElaboratedCompactification laws.sectionData ↔
      CompactCostNormalizationCoherent source := by
  constructor
  · intro compactification targetFree targetBound targetSort term first second
    let firstTerm : CostElabTerm source targetFree targetBound targetSort :=
      ⟨term, first⟩
    let secondTerm : CostElabTerm source targetFree targetBound targetSort :=
      ⟨term, second⟩
    have firstAgreement := compactification.erases_normalize firstTerm
    have secondAgreement := compactification.erases_normalize secondTerm
    exact firstAgreement.trans secondAgreement.symm
  · exact ofCompactCoherent laws

end CostReferenceElaboratedCompactification

end Mettapedia.GSLT.LanguageDef
