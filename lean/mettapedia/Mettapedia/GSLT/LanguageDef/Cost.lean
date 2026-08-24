import Mettapedia.GSLT.LanguageDef.CostStaticPlanCanonicalAlignment
import Mettapedia.GSLT.LanguageDef.CostStaticPlanProvenancedReification
import Mettapedia.GSLT.LanguageDef.CostEndofunctor
import Mettapedia.GSLT.LanguageDef.QuoteBoundaryDivergence
import Mettapedia.GSLT.LanguageDef.ColourTagSeparation
import Mettapedia.GSLT.LanguageDef.TwoDepthRestorationApex
import Mettapedia.GSLT.LanguageDef.GradedLanguageDef
import Mettapedia.Algebra.WorkSpan
import Mettapedia.Algebra.WorkSpanInformationLoss
import Mettapedia.Algebra.ResourceValuations
import Mettapedia.Algebra.ReceiptSchemaAdequacy
import Mettapedia.Algebra.OccurrenceIdentity
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesProvenancedAlignment
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostIterationPolicyCorollary
-- The Cost₁ endgame: the provider and seal over the four apex-slice obligations,
-- together with the modules that reduce or refute the routes into them.
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderApexSlice
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryBichromaticClosure
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCrossColorRestoration
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryExposureBridge
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryForeignBoundaryWitness
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryLeafDichotomyProbe
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCrossColorQuadrantCanary
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCrossColorLeafHinge
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCrossColorCallbackCanary
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCrossColorProCanary
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryDescent
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryVariableLeafRoutes
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCrossColorLeafExposure
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCrossColorExposureProvider
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCollapsingPlanStopApex
import Mettapedia.GSLT.LanguageDef.CostAuthoredAtom
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryNonBoundaryPlanStop
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryQuoteParallelCells
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryBoundarySideCell
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryQuoteBoundaryAlignment
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryResidualSwitchboard
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalStopFvarAbsorption
import Mettapedia.GSLT.LanguageDef.CostRestorationFvarPairLeaf
import Mettapedia.GSLT.LanguageDef.CostSourceVariableKeyAgreement
import Mettapedia.GSLT.LanguageDef.CostBoundaryNameAgreement
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryForeignResidualSpine
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostInhabitationLedger

/-!
# The Cost production surface

One import for consumers of the Cost theory.  This is the *intended* API:
importing anything else from the lane means reaching past the surface, and
is a signal either that the surface is missing something or that the
consumer is depending on an internal.

```
  PLAN            CostStaticPlanCanonicalAlignment   (aggregator over
                                                      carriers / lockstep /
                                                      parallel-children /
                                                      producers)
  REIFICATION     CostStaticPlanProvenancedReification
  Cost₁ LAWS      CostEndofunctor                    (CostOneObjectLawsFor)
  GRADING         GradedLanguageDef                  (spend / weigh / choose)
  VALUATION       Algebra.WorkSpan                   (+ InformationLoss negatives)
  RESOURCES       Algebra.ResourceValuations         (energy/comm; allocation does NOT fit)
  REPLAY ABI      Algebra.ReceiptSchemaAdequacy      (what a receipt must record)
  OCCURRENCES     Algebra.OccurrenceIdentity         (values never determine correspondence)
  ρ PROVENANCE    CostHereditaryMatchedFramesProvenancedAlignment
  Cost² BOUNDARY  CostIterationPolicyCorollary       (rhoCostTwo_boundary_package)
  QUOTE BOUNDARY  QuoteBoundaryDivergence            (the two reset disciplines)
  COLOUR TAGS     ColourTagSeparation                (base ≠ wrapped, so the gap is live)
  APEX (2-INDEX)  TwoDepthRestorationApex            (TwoDepthApex + embedding)
```

## The two quotation disciplines

A multi-presentation profile carries two notions of "quotation boundary":
restoration resets at *any* presentation's quote, keying resets only at
*this declaration's*.  `QuoteBoundaryDivergence` proves they diverge at a
foreign quote, and that no single depth index can follow both.
`TwoDepthRestorationApex` carries them separately, with the one-index
apex embedded as its diagonal under the agreement hypothesis.

## Deliberate exclusions

`CostHereditaryCanonicalOccurrenceSupport` (4,644 lines) is **not**
imported.  It is the superseded hereditary monolith; the provenanced
alignment path replaces it.  Anything still reaching for it should be
migrated, and the file retired once no consumer remains.

The uncorrected reified-stop path (`CostStaticPlanCanonicalReifiedStop`
and its congruence) is likewise **not** re-exported: its replacement is
`CostStaticPlanProvenancedStop`, whose `sourceFVar` arm carries membership
evidence on both sides.  No compatibility alias is provided, deliberately.

## Status of the surface

Green as imported here.  The umbrella exports the unconditional,
proof-relevant `rhoHereditaryCostOneDomainObject : CostOneDomainObject`.
`CostEndofunctor` supplies the laws structure and the ρ development
supplies every terminal it needs.

The per-colour semantic-cut provider is proved from four node-local
obligations by
`rhoCanonicalStaticPairSemanticCutProviderInDomain_of_exposureA2x`, and the
domain object follows by
`rhoHereditaryCostOneDomainObject_ofExposureApexSliceObligations`.  The four
inputs are

* `RhoAlignedViewsPlanStopApexInDomain`,
* `RhoCollapsingViewsPlanStopApexInDomain`,
* `RhoCollapsingCrossColorViewsLeafExposuresInDomain`,
* `RhoCollapsingLeafExposureInDomain`,

each quantified over both colours, and all four are inhabited.  They are
stated in *apex* form on the
static branches because that is the evidence the cut constructors actually
consume: `leftStaticEnclosing` asks for a `RhoMatchedStaticFramesApex`, not
for whole-frame restoration alignment.  The exported domain object packages
the four inhabitants through the apex-slice provider.

Two routes are retained but **non-critical**, and must not be mistaken for
the live path:

* the *source-form* residual (`RhoAlignedViewsRestorationAlignedInDomain`
  and `RhoStaticNonBoundaryPlanStopSourceAligned`) is strictly stronger than
  its consumer requires, with no route back — see the note in
  `CostHereditaryAlignedRestoration`.  Its cell analysis remains useful and
  its source-variable cells are proved;
* the three-classification route to `RhoCollapsingLeafExposureInDomain` is
  **refuted**: `not_rhoCollapsingLeafClassifications` shows its hypotheses
  are jointly uninhabited, because `RhoCollapsingApplyLeafBoundary` is false
  at both colours (`not_rhoCollapsingApplyLeafBoundary`, witnessed by the
  empty parallel, whose canonical form is the declared unit — an application
  — at a node carrying no boundary at all).  The implication itself is valid
  and therefore compiles; it is nonetheless unusable, and obligation B must
  be reached through its route types with the partner's
  `rootIsStatic = false` premise retained.

On the foreign-colour arm: `QuoteBoundaryDivergence` and
`ColourTagSeparation` establish that the restoration and keying disciplines
differ at a foreign quote, and that this is live for every two-colour Cost
language.  That does **not** make the one-index apex unsatisfiable — it is
inhabited at every depth, and its foreign-quote application case is proved by
`CommonRestorationApex.of_canonicalRootAligned_languageQuoteHead`.  A second
index is required only at bare `parallel`, where the apex's index is also a
canonicalization depth; `TwoDepthRestorationApex` supplies it there.

`CommonRestorationApex.toTwoDepth` is **not** a migration route over Cost:
its `QuoteStatusAgrees` premise is refuted by `not_quoteStatusAgrees_costStatic`.
-/
