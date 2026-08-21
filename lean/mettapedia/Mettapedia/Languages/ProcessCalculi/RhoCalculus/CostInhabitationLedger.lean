import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditarySupportedEndgame
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderApexSlice
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCrossColorRestoration
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryLeafDichotomyProbe
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryForeignBoundaryWitness

/-!
# Inhabitation ledger for the rho Cost₁ chain

A conditional theorem over an empty hypothesis type compiles, reports green,
and constrains nothing.  The reference-executor object tower reached exactly
that state before it was noticed: every bundle in it was refuted at one
stroke by projecting the generator-invariance field onto the checked
counterexample.

This file keeps the distinction visible under the build.  Every entry is a
checked witness or a checked refutation; the open obligations of the live
chain appear only as the recorded hypothesis signatures of the assembly
definitions, so a rename or reshaping of an open obligation fails here
rather than silently.

Ledger, as of this file's last update:

* inhabited — `OrderedCIGSLT` (first witness: the rho theory);
* refuted for rho — every reference-executor law bundle
  (`CostReferenceOpenGeneratorInvariant`, `CostReferenceOpenSectionLaws`,
  `CostReferenceOneObjectLaws`);
* proved — the reflective-support crown: `rhoHereditaryReflectiveSupportPreserving`
  is a theorem (local static-node law by path-indexed substitution, whole-tree
  structural theorem, supported-executor context transport);
* proved — the second node-local semantic input,
  `rhoHereditaryStaticNormalizer_preservesReflectiveSupport_path`.  It is a
  closed term, so the Cost₁ assembly no longer waits on it;
* open — exactly four node-local obligations, and nothing else.  The
  per-colour semantic-cut provider is not primitive: it is proved from them by
  `rhoCanonicalStaticPairSemanticCutProviderInDomain_of_apexSliceObligations`,
  and the object and domain object follow by
  `rhoHereditaryCostOneObjectLaws_ofApexSliceObligations` /
  `…DomainObject_ofApexSliceObligations`.  The four, each over both colours:

  - `RhoAlignedViewsPlanStopApexInDomain` — aligned bridge case, apex form;
  - `RhoCollapsingViewsPlanStopApexInDomain` — same-colour collapsing arms,
    apex form, at the `+ 1` measure forced by
    `not_canonicalStopAligned_endpoints_of_collapsing`;
  - `RhoCollapsingCrossColorViewsRestorationAlignedInDomain` — cross-colour
    collapsing arms, confined to the shared `Name` fibre and *equivalent* to
    the flat `RhoCollapsingCrossColorFramesRestoreTogetherInDomain`;
  - `RhoCollapsingLeafExposureInDomain` — structural partners.

  They are apex-form on the static branches because that is what the cut
  constructors consume; each carries the provider's own recursion callback
  (`RhoPairCloseSmaller`), which is load-bearing rather than decorative —
  `RhoCollapsingLeafExposure.normalize_eq` pins the partner's normal form, so
  a callback-free exposure obligation would be mixed-pair hereditary
  normalization soundness, the statement the seal exists to establish;
* **non-critical route, retained** — the *source-form* residual
  (`RhoAlignedViewsRestorationAlignedInDomain`,
  `RhoStaticNonBoundaryPlanStopSourceAligned`).  Strictly stronger than its
  consumer requires, with no route back.  Its source-variable cells are
  proved and its cell analysis stands; it is not on the live path;
* **refuted route, retained** — the three-classification route to obligation
  B.  `not_rhoCollapsingApplyLeafBoundary` refutes
  `RhoCollapsingApplyLeafBoundary` at both colours (witness: the empty
  parallel, whose canonical form is the declared unit — an application — at a
  node whose boundary inventory is empty), and
  `not_rhoCollapsingLeafClassifications` shows the three hypotheses are
  jointly uninhabited.  `rho_collapsingLeafExposureInDomain_of_classifications`
  is therefore valid but vacuous, and must never be counted as progress on B;
  the defect was dropping the partner's `rootIsStatic = false` premise;
* proved — reflective quotation seals ambient binders
  (`certifyCostRegionBoundary?_quoteDropBVar_eq_none`), so a quote/drop over a
  bound variable is never certifiable at either colour.  With
  `isStaticRoot_or_bvar_of_rhoProcess_canonicalize_eq_bvar` this empties the
  (certified boundary, bound-variable plan) configuration;
* proved from that same provider — the exact selected-executor compact Cost²
  obstruction.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostInhabitationLedger

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- The ordered continued carrier is inhabited: rho is an object. -/
example : Nonempty OrderedCIGSLT := ⟨⟨rhoCIGSLT⟩⟩

/-- The reference-executor object bundle is refuted for rho, so nothing may
be built over it. -/
example : ¬ CIGSLT.CostReferenceOneObjectLaws rhoCIGSLT :=
  CostGeneratorInvariantCounterexample.not_rho_costReferenceOneObjectLaws

/-- The reference-executor section bundle is refuted for rho. -/
example : ¬ CostReferenceOpenSectionLaws rhoCIGSLT :=
  CostGeneratorInvariantCounterexample.not_rho_costReferenceOpenSectionLaws

/-- Signature guard: the live rho Cost₁ object assembly and its exact open
hypotheses.  If either obligation is discharged, replace the corresponding
guard with the witness. -/
example := @rhoHereditaryCostOneObjectLaws_of

/-- Signature guard: the normalizer-indexed rho domain object assembly. -/
example := @rhoHereditaryCostOneDomainObject_of

/-- Historical signature guard: the reduced two-local-law assembly.  The
second input now has a checked global producer in the support crown. -/
example := @rhoHereditaryCostOneObjectLaws_ofStaticLaw

/-- Signature guard: the reduction itself — the supported executor preserves
every caller-relative reflective support once the local static-node law
holds. -/
example := @rhoHereditaryReflectiveSupportPreserving_of

/-- Signature guard: the alignability reduction — generator tree alignability
from the per-colour semantic-cut provider alone. -/
example := @rhoCostOpenGeneratorTreeAlignable_of_provider

/-- Signature guard: the fully reduced assembly over the two node-local
semantic obligations. -/
example := @rhoHereditaryCostOneObjectLaws_ofSemanticLaws

/-- The reflective-support crown is closed: a checked witness, not a guard. -/
example : RhoHereditaryReflectiveSupportPreserving :=
  rhoHereditaryReflectiveSupportPreserving

/-- Signature guard: the final waist — the Cost₁ object from the per-colour
semantic-cut provider alone. -/
example := @rhoHereditaryCostOneObjectLaws_ofProvider

/-- The selected-executor Cost² boundary has the same sole provider input as
the Cost₁ object; no executor agreement hypothesis remains. -/
example :=
  @rhoHereditaryCostOneDomainObject_not_compactCostNormalizationCoherent_ofProvider

/-- The second node-local semantic input is closed: a checked witness, not a
guard. -/
example := @rhoHereditaryStaticNormalizer_preservesReflectiveSupport_path

/-- Signature guard: the provider is no longer primitive.  It is proved from
the four apex-slice obligations. -/
example := @rhoCanonicalStaticPairSemanticCutProviderInDomain_of_apexSliceObligations

/-- Signature guard: the seal itself over those four obligations.  When all
four are discharged this becomes a checked witness of `CostOneDomainObject`. -/
noncomputable example := @rhoHereditaryCostOneDomainObject_ofApexSliceObligations

/-- Signature guards for the four open obligations themselves.  A rename or
reshaping of any of them fails here rather than silently. -/
example := @RhoAlignedViewsPlanStopApexInDomain
example := @RhoCollapsingViewsPlanStopApexInDomain
example := @RhoCollapsingCrossColorViewsRestorationAlignedInDomain
example := @RhoCollapsingLeafExposureInDomain

/-- The cross-colour obligation is *equivalent* to its flat form, so either
may be discharged. -/
example := @rhoCollapsingCrossColorViewsRestorationAlignedInDomain_of_framesRestoreTogether
example := @rhoCollapsingCrossColorFramesRestoreTogetherInDomain_of_restorationAligned

/-- **Refuted route.**  Checked refutations, not guards: the three-classification
reduction to obligation B cannot fire, so nothing may be built over it. -/
example : ∀ color, ¬ RhoCollapsingApplyLeafBoundary color :=
  CostHereditaryLeafDichotomyProbe.not_rhoCollapsingApplyLeafBoundary
example : ∀ color, ¬ (RhoCollapsingBVarLeafDichotomy color ∧
    RhoCollapsingFVarLeafDichotomy color ∧ RhoCollapsingApplyLeafBoundary color) :=
  CostHereditaryLeafDichotomyProbe.not_rhoCollapsingLeafClassifications

/-- Quotation seals ambient binders: a checked witness, not a guard. -/
example := @CostHereditaryForeignBoundaryWitness.certifyCostRegionBoundary?_quoteDropBVar_eq_none

/-- **Non-critical route.**  Signature guard only — the source-form residual is
strictly stronger than its consumer requires and is not on the live path. -/
example := @RhoAlignedViewsRestorationAlignedInDomain
example := @RhoStaticNonBoundaryPlanStopSourceAligned

/-- Signature guard: the recursion callback every obligation carries. -/
example := @RhoPairCloseSmaller

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostInhabitationLedger
