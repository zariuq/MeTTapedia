/-!
# Taxonomy Migration Ledger

This module records completed MeTTapedia directory-taxonomy migration clusters.
It is a tracked Lean ledger rather than a Markdown ledger, so the migration
record survives normal repository checkouts.

## Cluster 1: `ConceptOntology` to `KR`

Status: completed in the working tree.

Moved paths:
- The former `ConceptOntology` aggregator below the logic attic moved to
  `Mettapedia/KR/ConceptOntology.lean`.
- The former `ConceptOntology` subdirectory below the logic attic moved to
  `Mettapedia/KR/ConceptOntology/*`.

Namespace:
- New declaration namespace: `Mettapedia.KR.ConceptOntology`

References repointed:
- 40 Lean files had old ConceptOntology namespace references repointed to
  `Mettapedia.KR.ConceptOntology`.
- 6 ZarWiki path references had old ConceptOntology file paths repointed to
  `KR/ConceptOntology`.

Facade deletion:
- The 21 old-path compatibility modules from Pass 1 were removed.
- The migration-facade marker search is expected to return zero after this
  cluster.

Verification surface:
- Build the moved room: `lake build Mettapedia.KR.ConceptOntology`
- Build representative consumers, including PLN-facing importers.
- Check no old ConceptOntology namespace/path remains outside this ledger.
- Check no migrated file gained an unfinished-proof marker or an axiom
  declaration.
- Spot-check moved crown theorem axiom footprints remain within the accepted
  project footprint.

## Cluster 2: concrete Prolog to `Languages`

Status: completed in the working tree.

Moved paths:
- The concrete Prolog implementation formerly below the logic attic moved to
  `Mettapedia/Languages/Prolog/*`.
- A new `Mettapedia/Languages/Prolog.lean` hub imports the concrete Prolog
  barrel and is imported by `Mettapedia/Languages.lean`.

Namespace:
- New declaration namespace: `Mettapedia.Languages.Prolog`
- The generic LP theory under `Mettapedia.Logic.LP` was not moved.

References repointed:
- Lean consumers, the external Prolog-formalization index, the PeTTa profile
  matrix, and the LP paper references were repointed to the new Prolog room.

Facade deletion:
- No compatibility module was left at the old Prolog path.

Verification surface:
- Build the moved room: `lake build Mettapedia.Languages.Prolog`
- Build PeTTa consumers that import or open the Prolog runtime.
- Check no old concrete Prolog namespace/path remains outside this ledger.
- Check no migrated file gained an unfinished-proof marker or an axiom
  declaration.

## Cluster 3: universal prediction and Solomonoff surfaces to `UniversalAI`

Status: completed in the working tree.

Moved paths:
- The Solomonoff prior, induction, measure, and exchangeability surfaces moved
  from the logic attic to `Mettapedia/UniversalAI/*`.
- The universal-prediction aggregator and subdirectory moved to
  `Mettapedia/UniversalAI/UniversalPrediction*`.
- The universal-hyperprior aggregator and subdirectory moved to
  `Mettapedia/UniversalAI/UniversalHyperprior*`.

Namespace:
- New declaration namespaces are under `Mettapedia.UniversalAI`.
- Markov de Finetti support modules remain in the logic attic for now; moved
  UniversalAI files qualify those still-logic support declarations explicitly.

References repointed:
- Lean imports and qualified references for the moved universal-prediction and
  Solomonoff modules were repointed to `Mettapedia.UniversalAI`.
- Papers, ZarWiki project status, and Logic-facing documentation were repointed
  away from old universal-prediction paths.

Facade deletion:
- No compatibility module was left at an old universal-prediction path.

Verification surface:
- Build the moved room and doc-text generator:
  `lake build Mettapedia.UniversalAI Mettapedia.DocText.LogicReadmeCompositional`
- Check no old universal-prediction or Solomonoff namespace/path remains outside
  this ledger.
- Check no migration facade marker remains.
- Note: the universal-hyperprior lane retains pre-existing open proof
  obligations; this migration only moved and repointed them, and did not add new
  ones.

## Cluster 4: probability, exchangeability, and conjugate-evidence bridges

Status: completed in the working tree.

Moved paths:
- Exchangeability, de Finetti, and Markov de Finetti support modules moved from
  the logic attic to `Mettapedia/ProbabilityTheory/Exchangeability/*`.
- Finite and controlled hidden-Markov-model modules moved to
  `Mettapedia/ProbabilityTheory/HiddenMarkovModels/*`.
- Walley IDM modules moved to
  `Mettapedia/ProbabilityTheory/ImpreciseProbability/*`.
- PLN conjugate-evidence and de-Finetti truth-value bridge modules moved to
  `Mettapedia/PLN/Bridges/ProbabilityTheory/*`.
- The controlled finite-HMM universal-prediction bridge moved to
  `Mettapedia/UniversalAI/ControlledFiniteHiddenMarkovUniversalPredictionBridge.lean`.

Namespace:
- Probability definitions now live under `Mettapedia.ProbabilityTheory`.
- PLN-to-probability bridge definitions now live under
  `Mettapedia.PLN.Bridges.ProbabilityTheory`.
- The universal-prediction bridge namespace remains under `Mettapedia.UniversalAI`.

References repointed:
- Lean imports and qualified references for moved probability, HMM, Walley, and
  PLN evidence-bridge modules were repointed to the new rooms.
- Papers and local project-status references for moved evidence and Markov
  de Finetti paths were repointed away from the old logic attic.
- Aggregator self-cycles were avoided by making upstream files import
  `Mettapedia.ProbabilityTheory.Exchangeability.Core` or the precise submodule
  they need rather than the room hub.

Facade deletion:
- No compatibility module was left at an old probability, HMM, Walley, evidence,
  or universal-prediction bridge path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.ProbabilityTheory.Exchangeability Mettapedia.ProbabilityTheory.HiddenMarkovModels Mettapedia.ProbabilityTheory.ImpreciseProbability Mettapedia.PLN.Bridges.ProbabilityTheory Mettapedia.UniversalAI.ControlledFiniteHiddenMarkovUniversalPredictionBridge`
- Check no old moved probability namespace/path remains outside this ledger.
- Check no migration facade marker remains.
- `git diff -G sorry` over the migrated probability surface shows no newly added
  unfinished-proof markers. Some moved Markov/HMM files retain pre-existing open
  proof obligations; this migration only moved and repointed them.

## Cluster 5: generic concept geometry and PLN ASSOC/PAT split

Status: completed in the working tree.

Moved paths:
- Generic abstract inheritance, intensional inheritance, extensional/intensional
  divergence, and empirical intensional information modules moved from the
  logic attic to `Mettapedia/KR/ConceptGeometry/*`.
- Generic-to-PLN concept-geometry bridge modules moved to
  `Mettapedia/KR/ConceptGeometry/Bridges/PLN/*`.
- Generic-to-probability and generic-to-universal-AI bridge modules moved to
  `Mettapedia/KR/ConceptGeometry/Bridges/{ProbabilityTheory,UniversalAI}/*`.
- PLN-specific ASSOC/PAT closure, typed semantic layer, and HO empirical
  ASSOC/PAT bridge modules moved to
  `Mettapedia/PLN/ConceptGeometry/AssocPat/*`.

Namespace:
- Generic concept-geometry definitions now live under
  `Mettapedia.KR.ConceptGeometry`.
- PLN ASSOC/PAT definitions now live under
  `Mettapedia.PLN.ConceptGeometry.AssocPat`.

References repointed:
- Lean imports and qualified names for the moved concept-geometry modules were
  repointed to the new KR and PLN rooms.
- Papers and local project-status references for the moved concept-geometry and
  ASSOC/PAT surfaces were repointed away from the old logic attic.

Facade deletion:
- No compatibility module was left at an old concept-geometry or ASSOC/PAT path.

Verification surface:
- Full build: `lake build Mettapedia`
- Check no old moved concept-geometry namespace/path remains outside this ledger.
- Check no migration facade marker remains.
- Spot-check moved crown theorem axiom footprints remain within the accepted
  project footprint.

## Cluster 6a: PLN evidence, truth values, and immediate bridges

Status: completed in the working tree.

Moved paths:
- Core evidence files (`EvidenceClass`, `EvidenceCounts`, `EvidenceKind`,
  `BinaryEvidence`, evidence quantales, proof-system views, crisp and joint
  evidence surfaces, and related helpers) moved to `Mettapedia/PLN/Evidence/*`.
- PLN truth-value files (`PLNWeightTV`, distributional and indefinite truth,
  confidence-weight surfaces, truth-function canaries, and WM-backed truth
  function files) moved to `Mettapedia/PLN/TruthValues/*`.
- Immediate bridge files moved to
  `Mettapedia/PLN/Bridges/{ProbabilityTheory,Languages}/*`.

Namespace:
- Evidence definitions now live under `Mettapedia.PLN.Evidence`.
- Truth-value definitions now live under `Mettapedia.PLN.TruthValues`.
- The immediate bridge definitions now live under `Mettapedia.PLN.Bridges`.

References repointed:
- Lean imports and qualified references for moved evidence, truth-value, and
  immediate bridge modules were repointed to the new PLN rooms.
- Papers and local project-status references for those moved modules were
  repointed away from the old logic attic.
- Downstream logic bridge files that intentionally remain in `Logic/` now refer
  to the moved evidence typeclass by its fully-qualified PLN namespace.

Facade deletion:
- No compatibility module was left at an old evidence, truth-value, or immediate
  bridge path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Evidence Mettapedia.PLN.TruthValues Mettapedia.PLN.Bridges`
- Full build: `lake build Mettapedia`
- Check no old moved evidence/truth-value namespace/path remains outside this
  ledger.
- Check no migration facade marker remains.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6b: PLN world-model core

Status: completed in the working tree.

Moved paths:
- Binary and generic world-model cores moved to `Mettapedia/PLN/WorldModel/*`.
- Additive, calculus, profile, preorder, ITV, institution, conservation,
  overlap, support-forgetting, and crisp-specialization world-model surfaces
  moved to `Mettapedia/PLN/WorldModel/*`.
- A new `Mettapedia/PLN/WorldModel.lean` hub imports the world-model room and is
  imported by `Mettapedia/PLN.lean`.

Namespace:
- World-model definitions now live under `Mettapedia.PLN.WorldModel`.
- Downstream logic and KR bridge files that intentionally remain outside `PLN/`
  now import or open the moved world-model namespaces explicitly.

References repointed:
- Lean imports and qualified references for moved world-model modules were
  repointed to the new PLN room.
- The root `Mettapedia.lean` aggregator now imports the moved world-model
  institution module from `Mettapedia.PLN.WorldModel`.
- Downstream bridge files were mechanically repaired where the old broad logic
  namespace had previously made short world-model names visible.

Facade deletion:
- No compatibility module was left at an old world-model path.

Verification surface:
- Targeted build: `lake build Mettapedia.PLN.WorldModel`
- Full build: `lake build Mettapedia`
- Check no old moved world-model namespace/path remains outside this ledger.
- Check no migration facade marker remains.
- The moved world-model proof-hole scan found no active unfinished-proof marker;
  the only hit was prose stating "0 sorry."
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.1: PLN first-order rule families

Status: completed in the working tree.

Moved paths:
- First-order PLN rule files moved from the logic attic to
  `Mettapedia/PLN/RuleFamilies/FirstOrder/*`.
- The moved surface includes deduction, Frechet bounds, conjunction,
  disjunction, negation, noisy-OR, revision, induction/abduction, Bayes
  inversion, Bayes-net derived rules, XI rule registry, inference-rule helpers,
  and hierarchical-rule helpers.
- New hubs `Mettapedia/PLN/RuleFamilies/FirstOrder.lean` and
  `Mettapedia/PLN/RuleFamilies.lean` import the moved room, and
  `Mettapedia/PLN.lean` imports the rule-family hub.

Namespace:
- First-order rule-family definitions now live under
  `Mettapedia.PLN.RuleFamilies.FirstOrder`.
- A few moved files intentionally still open `Mettapedia.Logic.PLN` because the
  formula/derivation core remains in the logic attic until the later PLN core
  subcluster.

References repointed:
- Lean imports and qualified references for the moved first-order rule modules
  were repointed to the new PLN rule-family room.
- Papers and local project-status references for those moved modules were
  repointed away from the old logic attic.
- Downstream canonical/API surfaces that intentionally remain in `Logic/` now
  open or qualify the moved evidence, world-model, and first-order namespaces
  explicitly.

Facade deletion:
- No compatibility module was left at an old first-order rule-family path.

Verification surface:
- Targeted build: `lake build Mettapedia.PLN.RuleFamilies.FirstOrder`
- Canonical API build: `lake build Mettapedia.Logic.PLNCanonicalAPI`
- Full build: `lake build Mettapedia`
- Check no old moved first-order rule-family namespace/path remains outside
  this ledger.
- Check no migration facade marker remains.
- The moved first-order proof-hole scan found no active unfinished-proof
  pattern; the only hits were prose comments describing the absence of such
  holes.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.2: PLN higher-order rule families and HOL bridges

Status: completed in the working tree.

Moved paths:
- Higher-order rule-family files moved from the logic attic to
  `Mettapedia/PLN/RuleFamilies/HigherOrder/*`.
- Higher-order HOL and world-model HOL bridge files moved from the logic attic
  to `Mettapedia/PLN/Bridges/HOL/*`.
- New hubs `Mettapedia/PLN/RuleFamilies/HigherOrder.lean` and
  `Mettapedia/PLN/Bridges/HOL.lean` import the moved rooms, and the existing
  PLN hubs import those aggregators.

Namespace:
- Higher-order rule-family definitions now live under
  `Mettapedia.PLN.RuleFamilies.HigherOrder`.
- Higher-order HOL bridge definitions now live under
  `Mettapedia.PLN.Bridges.HOL`.
- The moved higher-order files intentionally continue to import or open genuine
  logic/HOL namespaces where those definitions remain core logic.

References repointed:
- Lean imports and qualified references for the moved higher-order rule and HOL
  bridge modules were repointed to the new PLN rooms.
- Papers and local project-status references for those moved modules were
  repointed away from the old logic attic.
- Downstream canonical/API and concept-geometry consumers that intentionally
  remain outside the moved rooms now qualify the new higher-order PLN
  namespaces explicitly.

Facade deletion:
- No compatibility module was left at an old higher-order rule-family or HOL
  bridge path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.RuleFamilies.HigherOrder Mettapedia.PLN.Bridges.HOL`
- Canonical API build: `lake build Mettapedia.Logic.PLNCanonicalAPI`
- Full build: `lake build Mettapedia`
- Check no old moved higher-order rule/HOL bridge namespace/path remains
  outside this ledger.
- Check no migration facade marker remains.
- The moved higher-order/HOL proof-hole scan found no active unfinished-proof
  pattern.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.3: PLN quantale, measure-theoretic, and stratified rule families

Status: completed in the working tree.

Moved paths:
- PLN quantale-semantics files moved from the logic attic to
  `Mettapedia/PLN/RuleFamilies/QuantaleSemantics*`.
- Measure-theoretic PLN files moved from the logic attic to
  `Mettapedia/PLN/RuleFamilies/MeasureTheoretic/*`.
- Stratified PLN files moved from the logic attic to
  `Mettapedia/PLN/RuleFamilies/Stratified*`.
- Generic modal and temporal quantale logic stayed in `Mettapedia/Logic`.

Namespace:
- PLN quantale-semantics definitions now live under
  `Mettapedia.PLN.RuleFamilies.QuantaleSemantics`.
- Measure-theoretic PLN definitions now live under
  `Mettapedia.PLN.RuleFamilies.MeasureTheoretic`.
- Stratified PLN definitions now live under
  `Mettapedia.PLN.RuleFamilies.Stratified`.

References repointed:
- Lean imports and qualified references for moved quantale, measure-theoretic,
  and stratified PLN modules were repointed to the new PLN rule-family room.
- Downstream first-order and HOL consumers that still live outside this room now
  qualify the moved quantale-semantics namespace explicitly where the former
  short name had been used.
- Papers and local project-status references for moved modules were repointed
  away from the old logic attic.

Facade deletion:
- No compatibility module was left at an old quantale, measure-theoretic, or
  stratified PLN path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.RuleFamilies.QuantaleSemantics Mettapedia.PLN.RuleFamilies.MeasureTheoretic Mettapedia.PLN.RuleFamilies.Stratified Mettapedia.PLN.RuleFamilies`
- Canonical API build: `lake build Mettapedia.Logic.PLNCanonicalAPI`
- Full build: `lake build Mettapedia`
- Check no old moved quantale, measure-theoretic, or stratified PLN
  namespace/path remains outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.4: PLN comparisons with NARS

Status: completed in the working tree.

Moved paths:
- NARS truth-function, evidence, second-order probability, inheritance, Galois
  connection, induction-weakness, and PLN/NARS rule-correspondence files moved
  from the logic attic to `Mettapedia/PLN/Comparisons/NARS/*`.
- New hubs `Mettapedia/PLN/Comparisons/NARS.lean` and
  `Mettapedia/PLN/Comparisons.lean` import the comparison room, and the
  top-level `Mettapedia/PLN.lean` hub imports comparisons.

Namespace:
- NARS comparison definitions now live under
  `Mettapedia.PLN.Comparisons.NARS`.
- Downstream KR concept-geometry witnesses that still use the NARS inheritance
  frame now qualify that comparison namespace explicitly.

References repointed:
- Lean imports and qualified references for the moved NARS comparison modules
  were repointed to the new PLN comparison room.
- Papers and local project-status references for the moved modules were
  repointed away from the old logic attic.
- The canonical PLN API and parity/decision-tree surfaces now point at the new
  comparison namespace.

Facade deletion:
- No compatibility module was left at an old NARS comparison path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Comparisons.NARS Mettapedia.PLN.Comparisons`
- Canonical API build: `lake build Mettapedia.Logic.PLNCanonicalAPI`
- Full build: `lake build Mettapedia`
- Check no old moved NARS comparison namespace/path remains outside this
  ledger.
- Check no migration facade marker remains.
- The moved NARS comparison proof-hole scan found no active unfinished-proof
  pattern.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.5: PLN inference-control and selector-threshold surfaces

Status: completed in the working tree.

Moved paths:
- Chapter-13 inference-control core, algorithms, chainer, canary, examples, and
  regression files moved from the logic attic to
  `Mettapedia/PLN/InferenceControl/PremiseSelection/*`.
- Selector/rewrite/threshold examples and regression moved from the logic attic
  to `Mettapedia/PLN/InferenceControl/SelectorRewriteThreshold/*`.
- New hubs `Mettapedia/PLN/InferenceControl/PremiseSelection.lean`,
  `Mettapedia/PLN/InferenceControl/SelectorRewriteThreshold.lean`, and
  `Mettapedia/PLN/InferenceControl.lean` import the inference-control room, and
  the top-level `Mettapedia/PLN.lean` hub imports inference control.

Namespace:
- Inference-control definitions now live under
  `Mettapedia.PLN.InferenceControl.PremiseSelection`.
- Selector/rewrite/threshold definitions now live under
  `Mettapedia.PLN.InferenceControl.SelectorRewriteThreshold`.

References repointed:
- Lean imports and qualified references for the moved inference-control modules
  were repointed to the new PLN inference-control room.
- Papers and local project-status references for the moved modules were
  repointed away from the old logic attic.
- The canonical PLN API now points at the new inference-control namespaces.

Facade deletion:
- No compatibility module was left at an old inference-control or
  selector/rewrite/threshold path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.InferenceControl.PremiseSelection Mettapedia.PLN.InferenceControl.SelectorRewriteThreshold Mettapedia.PLN.InferenceControl`
- Canonical API build: `lake build Mettapedia.Logic.PLNCanonicalAPI`
- Full build: `lake build Mettapedia`
- Check no old moved inference-control namespace/path remains outside this
  ledger.
- Check no migration facade marker remains.
- The moved inference-control proof-hole scan found no active unfinished-proof
  pattern.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.6: PLN forced-query and ITV-selector truth-value surface

Status: completed in the working tree.

Moved paths:
- `PLNForcedQueries.lean` moved from the logic attic to
  `Mettapedia/PLN/TruthValues/PLNForcedQueries.lean`.
- The truth-value hub `Mettapedia/PLN/TruthValues.lean` now imports the moved
  forced-query surface.

Namespace:
- Forced-query and chosen ITV-selector definitions now live under
  `Mettapedia.PLN.TruthValues.PLNForcedQueries`.
- The moved file explicitly opens `Mettapedia.Logic` only for the still-genuine
  logic-side `SufficientStatisticSurface` dependency; the PLN selector/evidence
  definitions themselves live in the truth-value room.

References repointed:
- Lean imports and qualified references in the truth tower and truth-theory
  index were repointed to the new truth-value namespace.
- Papers and local project-status references for the moved module were
  repointed away from the old logic attic.

Facade deletion:
- No compatibility module was left at the old `PLNForcedQueries` path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.TruthValues.PLNForcedQueries Mettapedia.PLN.TruthValues`
- Canonical API build: `lake build Mettapedia.Logic.PLNCanonicalAPI`
- Full build: `lake build Mettapedia`
- Check no old `Mettapedia.Logic.PLNForcedQueries` namespace/path remains
  outside this ledger.
- Check no migration facade marker remains.
- The moved forced-query proof-hole scan found no active unfinished-proof
  pattern.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.7: PLN Subjective-Logic probability bridge

Status: completed in the working tree.

Moved paths:
- `PLNSubjectiveLogicBridge.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/ProbabilityTheory/PLNSubjectiveLogicBridge.lean`.
- The probability-bridge hub `Mettapedia/PLN/Bridges/ProbabilityTheory.lean`
  now imports the moved bridge.

Namespace:
- Subjective-Logic-to-EvidenceBeta dictionary definitions now live under
  `Mettapedia.PLN.Bridges.ProbabilityTheory.PLNSubjectiveLogicBridge`.
- The moved bridge still imports `Mettapedia.Logic.PLNMeTTaCore`, because the
  MeTTa/STV core has not yet been moved in this taxonomy pass; this is a
  residual dependency, not an old bridge namespace.

References repointed:
- Lean imports and qualified references in the PLN truth-theory index were
  already repointed to the new probability-bridge namespace.
- Local project-status references mention the bridge by basename only and had
  no old module path to repoint.

Facade deletion:
- No compatibility module was left at the old `PLNSubjectiveLogicBridge` path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Bridges.ProbabilityTheory.PLNSubjectiveLogicBridge Mettapedia.PLN.Bridges.ProbabilityTheory Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex`
- Canonical API build: `lake build Mettapedia.Logic.PLNCanonicalAPI`
- Full build: `lake build Mettapedia`
- Check no old `Mettapedia.Logic.PLNSubjectiveLogicBridge` or
  `Mettapedia.Logic.SubjectiveLogicBridge` namespace/path remains outside this
  ledger.
- Check no migration facade marker remains.
- The moved bridge proof-hole scan found no active unfinished-proof pattern.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.8: PLN MeTTaCore language bridge

Status: completed in the working tree.

Moved paths:
- `PLNMeTTaCore.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/Languages/PLNMeTTaCore.lean`.
- The language-bridge hub `Mettapedia/PLN/Bridges/Languages.lean` now imports
  the moved MeTTaCore bridge before its evidence wrapper.

Namespace:
- MeTTa-facing PLN semantic-evaluation definitions now live under
  `Mettapedia.PLN.Bridges.Languages.PLNMeTTaCore`.
- The moved bridge still imports several still-unmigrated PLN calculus modules
  from `Mettapedia.Logic`; those are later PLN campaign surfaces, not residual
  MeTTaCore namespace debt.

References repointed:
- Lean imports and qualified references in the language evidence bridge,
  Subjective-Logic bridge, and truth-theory index were repointed to the new
  language-bridge namespace.
- Local project-status references for this module were repointed away from the
  old logic attic namespace.

Facade deletion:
- No compatibility module was left at the old `PLNMeTTaCore` path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Bridges.Languages.PLNMeTTaCore Mettapedia.PLN.Bridges.Languages.PLNMeTTaCoreEvidence Mettapedia.PLN.Bridges.Languages Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex`
- Canonical API build: `lake build Mettapedia.Logic.PLNCanonicalAPI`
- Full build: `lake build Mettapedia`
- Check no old `Mettapedia.Logic.PLNMeTTaCore` namespace/path remains outside
  this ledger.
- Check no migration facade marker remains.
- The moved MeTTaCore bridge proof-hole scan found no active unfinished-proof
  pattern.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.9: PLN first-order calculus spine

Status: completed in the working tree.

Moved paths:
- `PLNDerivation.lean` moved from the logic attic to
  `Mettapedia/PLN/RuleFamilies/FirstOrder/PLNDerivation.lean`.
- `PLNInferenceCalculus.lean` moved from the logic attic to
  `Mettapedia/PLN/RuleFamilies/FirstOrder/PLNInferenceCalculus.lean`.
- `PLNLinkCalculus.lean` moved from the logic attic to
  `Mettapedia/PLN/RuleFamilies/FirstOrder/PLNLinkCalculus.lean`.
- `PLNLinkCalculusSoundness.lean` moved from the logic attic to
  `Mettapedia/PLN/RuleFamilies/FirstOrder/PLNLinkCalculusSoundness.lean`.
- `PLNConsistencyLemmas.lean` moved from the logic attic to
  `Mettapedia/PLN/RuleFamilies/FirstOrder/PLNConsistencyLemmas.lean`.
- The first-order rule-family hub
  `Mettapedia/PLN/RuleFamilies/FirstOrder.lean` imports all five moved
  calculus-spine modules.

Namespace:
- Deduction, induction, abduction, revision-calculus, link-calculus, and
  consistency lemmas now live under `Mettapedia.PLN.RuleFamilies.FirstOrder.*`.
- The link-calculus soundness namespace is nested under
  `Mettapedia.PLN.RuleFamilies.FirstOrder.PLNLinkCalculus.Soundness`, matching
  its calculus consumer while the file itself remains the soundness bridge.

References repointed:
- Lean imports and qualified references were repointed away from the old
  `Mettapedia.Logic.PLN*` calculus namespaces.
- `Mettapedia/Logic/PLNCanonicalAPI.lean` keeps its public canonical aliases,
  but their backing definitions now point at the relocated
  `PLNDerivation` definitions.
- `Mettapedia/Logic/PLNBNCompilation.lean` now qualifies its
  `Judgment`, `Context`, and derivation-spine references through the relocated
  `PLNLinkCalculus` namespace.
- Paper and local project-status references for these module paths were checked
  for stale old logic-attic references.

Facade deletion:
- No compatibility module was left at any old first-order calculus-spine path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation Mettapedia.PLN.RuleFamilies.FirstOrder.PLNInferenceCalculus Mettapedia.PLN.RuleFamilies.FirstOrder.PLNLinkCalculus Mettapedia.PLN.RuleFamilies.FirstOrder.PLNLinkCalculusSoundness Mettapedia.PLN.RuleFamilies.FirstOrder.PLNConsistencyLemmas Mettapedia.PLN.RuleFamilies.FirstOrder Mettapedia.PLN.Bridges.Languages.PLNMeTTaCore`
- Canonical API build: `lake build Mettapedia.Logic.PLNCanonicalAPI`
- Full build: `lake build Mettapedia`
- Check no old `Mettapedia.Logic.PLNDerivation`,
  `Mettapedia.Logic.PLNInferenceCalculus`,
  `Mettapedia.Logic.PLNLinkCalculus`,
  `Mettapedia.Logic.PLNLinkCalculusSoundness`,
  `Mettapedia.Logic.PLNConsistencyLemmas`, or old-path reference remains
  outside this ledger.
- Check no migration facade marker remains.
- The moved first-order calculus-spine proof-hole scan found no active
  unfinished-proof pattern.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.10: PLN first-order quantifier package

Status: completed in the working tree.

Moved paths:
- `PLNFirstOrder.lean` moved from the logic attic to
  `Mettapedia/PLN/RuleFamilies/FirstOrder/Quantifiers.lean`.
- The 40-file `PLNFirstOrder/` subtree moved from the logic attic to
  `Mettapedia/PLN/RuleFamilies/FirstOrder/Quantifiers/`.
- The first-order rule-family hub
  `Mettapedia/PLN/RuleFamilies/FirstOrder.lean` imports the moved
  quantifier aggregator.

Namespace:
- Finitary, infinitary, fuzzy, Choquet, Sugeno, graded-domain, and worked
  example quantifier definitions now live under
  `Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers`.
- The old `Mettapedia.Logic.PLNFirstOrder.Infinite` subnamespace became
  `Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.Infinite`.

References repointed:
- Lean imports, `open` commands, and qualified theorem/definition references
  were repointed away from `Mettapedia.Logic.PLNFirstOrder`.
- Higher-order bridge consumers and canonical-API quantifier aliases were
  repointed to the new quantifier namespace.
- Paper, generated doc-text, and local project-status build-command references
  were repointed to the new quantifier module paths.
- `Soundness.lean` had one stale old quantale-semantics qualifier mechanically
  expanded to `Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PBit.isTrue`.

Facade deletion:
- No compatibility module was left at `Logic/PLNFirstOrder.lean` or
  `Logic/PLNFirstOrder/`.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers Mettapedia.PLN.RuleFamilies.FirstOrder Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLQuantifierBridge`
- Canonical API build: `lake build Mettapedia.Logic.PLNCanonicalAPI`
- Full build: `lake build Mettapedia`
- Check no old `Mettapedia.Logic.PLNFirstOrder`, old
  `Mettapedia/Logic/PLNFirstOrder`, or old `Logic/PLNFirstOrder` path
  reference remains outside this ledger.
- Check no migration facade marker remains.
- The moved quantifier package proof-hole scan found no active unfinished-proof
  pattern.
- Spot-check quantifier theorem axiom footprints remain within the accepted
  project footprint.

## Cluster 6c.11: PLN Bayesian-network world-model and probability bridges

Status: completed in the working tree.

Moved paths:
- `PLNBayesNetWorldModel.lean` moved from the logic attic to
  `Mettapedia/PLN/WorldModel/BayesNet/PLNBayesNetWorldModel.lean`.
- `PLNBayesNetInference.lean` moved from the logic attic to
  `Mettapedia/PLN/WorldModel/BayesNet/PLNBayesNetInference.lean`.
- Bayesian-network compilation, local-Markov-package, and collider-singleton
  bridge modules moved from the logic attic to
  `Mettapedia/PLN/Bridges/ProbabilityTheory/BayesNet/*`.
- New room hubs `Mettapedia/PLN/WorldModel/BayesNet.lean` and
  `Mettapedia/PLN/Bridges/ProbabilityTheory/BayesNet.lean` import the moved
  world-model and bridge packages.

Namespace:
- Boolean CPT world-model and exact-query definitions now live under
  `Mettapedia.PLN.WorldModel.BayesNet.*`.
- PLN-to-Bayesian-network compilation and local-Markov bridge definitions now
  live under `Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.*`.

References repointed:
- Lean imports and qualified references for the moved Bayesian-network
  world-model, inference, compilation, local-Markov, and singleton-bridge
  modules were repointed away from the old `Mettapedia.Logic.PLN*` namespaces.
- The world-model and probability-bridge hubs now expose the moved packages.
- Downstream rule-family and selector-regression consumers were rebuilt through
  the moved module paths.

Facade deletion:
- No compatibility module was left at any old Bayesian-network PLN path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.WorldModel.BayesNet Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet Mettapedia.PLN.RuleFamilies.FirstOrder.PLNXiDerivedBNRules Mettapedia.PLN.InferenceControl.SelectorRewriteThreshold.PLNSelectorRewriteThresholdRegression`
- Check no old `Mettapedia.Logic.PLNBNCompilation`,
  `Mettapedia.Logic.PLNBNLocalMarkovPackages`,
  `Mettapedia.Logic.PLNBayesNetInference`,
  `Mettapedia.Logic.PLNBayesNetWorldModel`,
  `Mettapedia.Logic.PLNChainBNLocalMarkovPackage`,
  `Mettapedia.Logic.PLNColliderBNLocalMarkovPackage`,
  `Mettapedia.Logic.PLNColliderSingletonBridge`, or
  `Mettapedia.Logic.PLNForkBNLocalMarkovPackage` namespace/path reference
  remains outside this ledger.
- Check no migration facade marker remains.
- The moved Bayesian-network PLN proof-hole scan found no active
  unfinished-proof pattern.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.12: PLN world-model bridges to language runtimes

Status: completed in the working tree.

Moved paths:
- The generic runtime-to-world-model bridge moved from the logic attic to
  `Mettapedia/PLN/Bridges/Languages/WorldModel/PLNWorldModelRuntimeBridge.lean`.
- HE runtime, core-fragment, premise-core, and concrete runtime-instance
  bridges moved to `Mettapedia/PLN/Bridges/Languages/WorldModel/*`.
- PeTTa runtime, core-fragment, space-core, and concrete runtime-instance
  bridges moved to `Mettapedia/PLN/Bridges/Languages/WorldModel/*`.
- The PureKernel-to-world-model bridge moved to
  `Mettapedia/PLN/Bridges/Languages/WorldModel/PLNWorldModelPureKernelBridge.lean`.
- A new `Mettapedia/PLN/Bridges/Languages/WorldModel.lean` hub imports the
  runtime bridge package and is imported by the language-bridge room hub.

Namespace:
- Runtime-to-world-model bridge definitions now live under
  `Mettapedia.PLN.Bridges.Languages.WorldModel.*`.
- The moved files still import the language-runtime definitions from
  `Mettapedia.Languages.*`; this is the intended bridge direction.

References repointed:
- Lean imports and qualified references for the moved HE, PeTTa, PureKernel,
  and generic runtime bridge modules were repointed away from the old
  `Mettapedia.Logic.PLNWorldModel*` namespaces.
- GF and PureRuntime language consumers now import/open the moved PureKernel
  world-model bridge through the PLN language-bridge namespace.
- Paper references for the moved PureKernel bridge were repointed away from the
  old logic-attic path.

Facade deletion:
- No compatibility module was left at any old runtime world-model bridge path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Bridges.Languages.WorldModel Mettapedia.PLN.Bridges.Languages Mettapedia.Languages.GF.GFWMObligationAdapter Mettapedia.Languages.MeTTa.PureRuntimeFrontier`
- Check no old `Mettapedia.Logic.PLNWorldModelRuntimeBridge`,
  `Mettapedia.Logic.PLNWorldModelHERuntimeBridge`,
  `Mettapedia.Logic.PLNWorldModelHECoreBridge`,
  `Mettapedia.Logic.PLNWorldModelHEPremiseCoreBridge`,
  `Mettapedia.Logic.PLNWorldModelHERuntimeInstance`,
  `Mettapedia.Logic.PLNWorldModelPeTTaRuntimeBridge`,
  `Mettapedia.Logic.PLNWorldModelPeTTaCoreBridge`,
  `Mettapedia.Logic.PLNWorldModelPeTTaRuntimeInstance`,
  `Mettapedia.Logic.PLNWorldModelPeTTaSpaceCoreBridge`, or
  `Mettapedia.Logic.PLNWorldModelPureKernelBridge` namespace/path reference
  remains outside this ledger.
- Check no migration facade marker remains.
- The moved runtime world-model bridge proof-hole scan found no active
  unfinished-proof pattern.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.13: PLN world-model fixpoint closure

Status: completed in the working tree.

Moved paths:
- Least-rule-closure, finite-cascade, policy-aware closure, and SP/SPN orbit
  bridge modules moved from the logic attic to
  `Mettapedia/PLN/WorldModel/Fixpoint/*`.
- A new `Mettapedia/PLN/WorldModel/Fixpoint.lean` hub imports the moved
  fixpoint package and is imported by the PLN world-model room hub.

Namespace:
- Fixpoint-closure definitions now live under
  `Mettapedia.PLN.WorldModel.Fixpoint.*`.
- The moved SP/SPN and policy bridge modules still import Kripke-weighted and
  damped-convergence support definitions from the logic attic; those support
  surfaces are not part of this cluster.

References repointed:
- Lean imports and qualified references for the moved fixpoint, cascade,
  policy, SP/SPN bridge, and regression modules were repointed away from the
  old `Mettapedia.Logic.PLNWorldModelFixpoint*` namespaces.
- The PLN world-model hub now exposes the moved fixpoint package.
- Hyperseed, OSLF, and higher-order regime-admissibility consumers were rebuilt
  through the moved module paths; the latter no longer opens the old broad
  `Mettapedia.Logic` namespace.
- Paper and local project-status references for the moved fixpoint module paths
  were checked for stale old logic-attic references.

Facade deletion:
- No compatibility module was left at any old world-model fixpoint path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.WorldModel.Fixpoint Mettapedia.PLN.WorldModel Mettapedia.Hyperseed.Basic Mettapedia.Hyperseed.Closure Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility`
- Check no old `Mettapedia.Logic.PLNWorldModelFixpointClosure`,
  `Mettapedia.Logic.PLNWorldModelFixpointCascade`,
  `Mettapedia.Logic.PLNWorldModelFixpointClosureRegression`,
  `Mettapedia.Logic.PLNWorldModelFixpointPolicy`,
  `Mettapedia.Logic.PLNWorldModelFixpointPolicyRegression`,
  `Mettapedia.Logic.PLNWorldModelFixpointSPNBridge`, or
  `Mettapedia.Logic.PLNWorldModelFixpointSPNBridgeRegression` namespace/path
  reference remains outside this ledger.
- Check no migration facade marker remains.
- The moved fixpoint proof-hole scan found no active unfinished-proof pattern.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.14: PLN world-model order-cost and audit surfaces

Status: completed in the working tree.

Moved paths:
- Quantitative order-cost bounds, runtime audit certificates, and the
  weighted/provenance/gas policy demos moved from the logic attic to
  `Mettapedia/PLN/WorldModel/OrderCost/*`.
- Broader world-model audit wrappers moved to
  `Mettapedia/PLN/WorldModel/Audit/PLNWorldModelAudit.lean`.
- New `Mettapedia/PLN/WorldModel/OrderCost.lean` and
  `Mettapedia/PLN/WorldModel/Audit.lean` hubs import the moved packages and
  are imported by the PLN world-model room hub.

Namespace:
- Order-cost definitions now live under
  `Mettapedia.PLN.WorldModel.OrderCost.*`.
- Audit definitions now live under `Mettapedia.PLN.WorldModel.Audit.*`.
- The audit module still imports semitopology and provenance support from the
  logic attic; those support surfaces are not part of this cluster.

References repointed:
- Lean imports and qualified references for the moved order-cost bounds,
  audit-certificate, gas, provenance, weighted, and audit modules were
  repointed away from the old `Mettapedia.Logic.PLNWorldModelOrderCost*` and
  `Mettapedia.Logic.PLNWorldModelAudit` namespaces.
- `PLNCore` and `PLNCanonicalAPI` now consume the moved audit and order-cost
  modules through their PLN world-model namespaces.
- Paper references for the moved order-cost demo paths were repointed away
  from the old logic-attic paths.
- A stale ASSOC/PAT consumer was mechanically qualified to the moved PLN
  evidence and world-model namespaces after the canonical API rebuild exposed
  the old namespace shortcut.

Facade deletion:
- No compatibility module was left at any old world-model order-cost or audit
  path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.WorldModel.OrderCost Mettapedia.PLN.WorldModel.Audit Mettapedia.PLN.WorldModel Mettapedia.Logic.PLNCanonicalAPI Mettapedia.Logic.PLNCore`
- Check no old `Mettapedia.Logic.PLNWorldModelOrderCost*`,
  `Mettapedia.Logic.PLNWorldModelAudit`, or moved order-cost/audit qualified
  namespace reference remains outside this ledger.
- Check no migration facade marker remains.
- The moved order-cost and audit proof-hole scan found no active
  unfinished-proof pattern.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.15: PLN world-model bridges to logic and category-theory semantics

Status: completed in the working tree.

Moved paths:
- FOL, infinitary FOL, Kripke, Kripke-neighborhood, neighborhood, and
  set-theory world-model bridge modules moved from the logic attic to
  `Mettapedia/PLN/Bridges/Logic/WorldModel/*`.
- Hyperdoctrine and categorical world-model bridge modules moved from the
  logic attic to `Mettapedia/PLN/Bridges/CategoryTheory/WorldModel/*`.
- Historical import-only wrappers at the old `Mettapedia/Logic/PLNWorldModel*`
  paths were deleted rather than preserved as compatibility facades.
- New `Mettapedia/PLN/Bridges/Logic.lean`,
  `Mettapedia/PLN/Bridges/Logic/WorldModel.lean`,
  `Mettapedia/PLN/Bridges/CategoryTheory.lean`, and
  `Mettapedia/PLN/Bridges/CategoryTheory/WorldModel.lean` hubs import the
  moved packages and are imported by the PLN bridge room hub.

Namespace:
- Logic-semantics world-model bridge definitions now live under
  `Mettapedia.PLN.Bridges.Logic.WorldModel.*`.
- Category-theory world-model bridge definitions now live under
  `Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.*`.
- The moved category-theory bridge files qualify upstream category-theory
  names through `_root_.CategoryTheory` where needed, avoiding shadowing by the
  new `Mettapedia.PLN.Bridges.CategoryTheory` namespace segment.

References repointed:
- Lean imports and qualified references for the moved FOL, infinitary FOL,
  Kripke, Kripke-neighborhood, neighborhood, set-theory, hyperdoctrine, and
  categorical bridge modules were repointed away from their old logic-attic
  namespaces.
- `PLNCore`, `PLNCanonicalAPI`, OSLF world-model consumers, GF language
  consumers, and PLN fixpoint consumers were rebuilt through the moved bridge
  module paths.
- Paper references for the moved bridge modules were repointed away from the
  old logic-attic paths.

Facade deletion:
- No compatibility module was left at any old world-model logic-semantics or
  category-theory bridge path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Bridges.Logic.WorldModel Mettapedia.PLN.Bridges.CategoryTheory.WorldModel Mettapedia.PLN.Bridges Mettapedia.Logic.PLNCanonicalAPI Mettapedia.Logic.PLNCore Mettapedia.OSLF.Framework.WMCalculusFOLBridge Mettapedia.OSLF.Framework.WMCalculusNeighborhoodBridge Mettapedia.OSLF.Framework.OSLFNTTWMBridge Mettapedia.Languages.GF.GFToFOLSetBridge Mettapedia.Languages.GF.GFWMObligationAdapter Mettapedia.PLN.WorldModel.Fixpoint`
- Check no old `Mettapedia.Logic.WorldModelFOL`,
  `Mettapedia.Logic.WorldModelKripke`,
  `Mettapedia.Logic.WorldModelNeighborhood`,
  `Mettapedia.Logic.WorldModelHyperdoctrine`,
  `Mettapedia.Logic.WorldModelCategoricalBridge`,
  `Mettapedia.Logic.WorldModelSetTheoryBridge`, or moved
  `Mettapedia.Logic.PLNWorldModel*` bridge namespace/path reference remains
  outside this ledger.
- Check no migration facade marker remains.
- The moved logic-semantics and category-theory bridge proof-hole scan found
  no active unfinished-proof pattern.
- `git diff --check` passes on the current migration surface after normalizing
  CRLF line endings in previously touched migration files.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.16: PLN world-model experiment and Blackwell-channel surfaces

Status: completed in the working tree.

Moved paths:
- Minimal experiment-channel, Blackwell dominance, stochastic-channel,
  stochastic-discovery, and regression fixture modules moved from the logic
  attic to `Mettapedia/PLN/WorldModel/Experiment/*`.
- A new `Mettapedia/PLN/WorldModel/Experiment.lean` hub imports the moved
  experiment package and is imported by the PLN world-model room hub.

Namespace:
- Experiment and Blackwell-channel definitions now live under
  `Mettapedia.PLN.WorldModel.Experiment.*`.
- The moved stochastic experiment files continue to import probability and
  Markov-category support from their proper rooms; this cluster only changes
  the PLN world-model experiment consumers.

References repointed:
- Lean imports and qualified references for the moved experiment, stochastic,
  stochastic-discovery, and regression modules were repointed away from the old
  `Mettapedia.Logic.PLNWorldModelExperiment*` namespaces.
- The root `Mettapedia.lean` import list now imports the experiment package
  hub rather than the old logic-attic submodules.
- The fixpoint-closure regression consumer now imports and opens the moved
  experiment modules.
- Paper references for the moved experiment modules were repointed away from
  the old logic-attic paths.

Facade deletion:
- No compatibility module was left at any old world-model experiment path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.WorldModel.Experiment Mettapedia.PLN.WorldModel Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosureRegression Mettapedia`
- Check no old `Mettapedia.Logic.PLNWorldModelExperiment*` namespace/path
  reference remains outside this ledger.
- Check no migration facade marker remains.
- The moved experiment proof-hole scan found no active unfinished-proof
  pattern.
- `git diff --check` passes on the experiment migration surface.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.17: PLN world-model provenance and semitopology surfaces

Status: completed in the working tree.

Moved paths:
- Provenance support, tracked-state, scoped-tracked-state, and
  provenance-inference modules moved from the logic attic to
  `Mettapedia/PLN/WorldModel/Provenance/*`.
- Semitopology and semitopology/provenance bridge modules moved from the
  logic attic to `Mettapedia/PLN/WorldModel/Semitopology/*`.
- New hubs `Mettapedia/PLN/WorldModel/Provenance.lean` and
  `Mettapedia/PLN/WorldModel/Semitopology.lean` import the moved packages and
  are imported by the PLN world-model room hub.

Namespace:
- Provenance support and tracked-state definitions now live under
  `Mettapedia.PLN.WorldModel.Provenance.*`.
- Provenance-inference definitions live under
  `Mettapedia.PLN.WorldModel.Provenance.PLNProvenanceInference.*`.
- Semitopology core and semitopology/provenance bridge definitions now live
  under `Mettapedia.PLN.WorldModel.Semitopology.*`.
- `CoalitionTopology` lives under `Mettapedia.PLN.WorldModel.CoalitionTopology`.
  The semitopology core file deliberately uses the world-model namespace with
  an inner `Semitopology` namespace so the moved declarations do not acquire a
  duplicated `Semitopology.Semitopology` prefix.

References repointed:
- Lean imports and qualified references for provenance support, tracked-state,
  scoped-tracked-state, provenance-inference, semitopology, and
  semitopology/provenance bridge modules were repointed away from the old
  `Mettapedia.Logic.PLNProvenance*`, `Mettapedia.Logic.PLNScopedTracked*`, and
  `Mettapedia.Logic.PLNSemitopology*` namespaces.
- `PLNCore`, `PLNCanonicalAPI`, world-model audit/order-cost consumers,
  truth-value examples, derivation-tracking demos, classic examples, and
  temporal-chaining examples were rebuilt through the moved module paths.
- Paper and ZarWiki references for the moved provenance/semitopology modules
  were scanned for stale logic-attic paths.

Facade deletion:
- No compatibility module was left at any old provenance, scoped-tracked, or
  semitopology path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.WorldModel.Provenance Mettapedia.PLN.WorldModel.Semitopology Mettapedia.PLN.WorldModel Mettapedia.PLN.WorldModel.Audit Mettapedia.PLN.WorldModel.OrderCost.PLNWorldModelOrderCostProvenanceDemo Mettapedia.PLN.TruthValues.PLNClassicTruthFunctions Mettapedia.Logic.PLNCore Mettapedia.Logic.PLNCanonicalAPI Mettapedia.Logic.PLNDerivationTrackingDemoPropositional Mettapedia.Logic.WMDerivationTrackingDemo Mettapedia.Logic.PLNClassicExamples Mettapedia.Logic.TemporalChainingExample`
- Check no old provenance, scoped-tracked, or semitopology namespace/path
  reference remains outside this ledger.
- Check no migration facade marker remains.
- The moved provenance and semitopology proof-hole scan found no active
  unfinished-proof pattern.
- `git diff --check` passes on the provenance/semitopology migration surface
  after normalizing CRLF line endings in a touched truth-value consumer.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.18: PLN higher-order untrusted-oracle adapter surfaces

Status: completed in the working tree.

Moved paths:
- `PLNUntrustedOracleAdapters.lean` and
  `PLNUntrustedOracleAdapterRegression.lean` moved from the logic attic to
  `Mettapedia/PLN/RuleFamilies/HigherOrder/*`.
- The `Mettapedia/PLN/RuleFamilies/HigherOrder.lean` room hub imports both
  moved modules.

Namespace:
- Oracle adapter statuses, certified blind-adapter interfaces, calibrated
  admissibility-oracle adapters, and their regression canaries now live under
  `Mettapedia.PLN.RuleFamilies.HigherOrder.*`.
- Existing `Mettapedia.Logic.PLNCanonical` and `Mettapedia.Logic.PLNCore`
  namespaces were preserved; only their imports and public alias targets were
  repointed.

References repointed:
- `PLNCore` and `PLNCanonicalAPI` imports were repointed from the old
  logic-attic modules to the moved higher-order rule-family modules.
- `PLNCanonicalAPI` public aliases for the oracle-adapter endpoints were
  repointed to `_root_.Mettapedia.PLN.RuleFamilies.HigherOrder.*`.

Facade deletion:
- No compatibility module was left at either old untrusted-oracle adapter path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.RuleFamilies.HigherOrder.PLNUntrustedOracleAdapters Mettapedia.PLN.RuleFamilies.HigherOrder.PLNUntrustedOracleAdapterRegression Mettapedia.PLN.RuleFamilies.HigherOrder Mettapedia.Logic.PLNCore Mettapedia.Logic.PLNCanonicalAPI`
- Check no old `Mettapedia.Logic.PLNUntrustedOracle*` module path, old
  `Mettapedia.Logic.*OracleAdapter*` qualified alias, or old
  `Logic/PLNUntrustedOracle*` path reference remains outside this ledger.
- Check no migration facade marker remains.
- The moved untrusted-oracle adapter proof-hole scan found no active
  unfinished-proof pattern.
- `git diff --check` passes on the untrusted-oracle adapter migration surface.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.19: PLN probability bridge and independence-point canaries

Status: completed in the working tree.

Moved paths:
- `PLNProbabilityBridge.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/ProbabilityTheory/PLNProbabilityBridge.lean`.
- `PLNIndependencePointApproximation.lean` moved from the logic attic to
  `Mettapedia/PLN/RuleFamilies/FirstOrder/PLNIndependencePointApproximation.lean`.
- The `Mettapedia/PLN/Bridges/ProbabilityTheory.lean` and
  `Mettapedia/PLN/RuleFamilies/FirstOrder.lean` room hubs import the moved
  modules.

Namespace:
- K&S probability-semantics validation theorems now live under
  `Mettapedia.PLN.Bridges.ProbabilityTheory.PLNProbabilityBridge.*`.
- Independence-point, Frechet-gap, and effective-concentration canaries now
  live under `Mettapedia.PLN.RuleFamilies.FirstOrder.PLNIndependencePoint.*`.

References repointed:
- The higher-order PLN entrypoint import was repointed from the old
  logic-attic independence-point module to the first-order rule-family module.
- No external importer or qualified reference remained for the old probability
  bridge namespace.

Facade deletion:
- No compatibility module was left at either old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Bridges.ProbabilityTheory.PLNProbabilityBridge Mettapedia.PLN.Bridges.ProbabilityTheory Mettapedia.PLN.RuleFamilies.FirstOrder.PLNIndependencePointApproximation Mettapedia.PLN.RuleFamilies.FirstOrder Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOL`
- Check no old `Mettapedia.Logic.PLNProbabilityBridge` or
  `Mettapedia.Logic.PLNIndependencePoint` namespace/path reference remains
  outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern.
- `git diff --check` passes on the migration surface.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.20: PLN core end-to-end stable surface

Status: completed in the working tree.

Moved paths:
- `PLNEndToEnd.lean` moved from the logic attic to
  `Mettapedia/PLN/Core/PLNEndToEnd.lean`.
- `Mettapedia/PLN/Core.lean` was introduced as the PLN core room hub, and the
  top-level `Mettapedia/PLN.lean` hub imports it.

Namespace:
- The stable BN/WM/OSLF end-to-end theorem aliases and generic context-lift
  theorem now live under `Mettapedia.PLN.Core.PLNEndToEnd.*`.

References repointed:
- Higher-order proof-carrying contraction demos and the canonical API import
  the moved core module.
- The proof-carrying contraction demo opens `Mettapedia.PLN.Core` so existing
  short provenance-facing names such as `PLNEndToEnd.colliderNotExact` still
  resolve through the new room.
- Paper and ZarWiki scans found no old `Logic/PLNEndToEnd` path reference to
  repoint; existing `PLNEndToEnd.*` mentions are theorem-surface names, not
  stale module paths.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Core.PLNEndToEnd Mettapedia.PLN.Core Mettapedia.PLN Mettapedia.PLN.RuleFamilies.HigherOrder.PLNProofCarryingContractionDemo Mettapedia.Logic.PLNCanonicalAPI`
- Check no old `Mettapedia.Logic.PLNEndToEnd` namespace/path reference remains
  outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern.
- `git diff --check` passes on the migration surface.
- Spot-check end-to-end theorem/abbrev axiom footprints remain within the
  accepted project footprint.

## Cluster 6c.21: PLN proof-calculus core and Tait-calculus bridge

Status: completed in the working tree.

Moved paths:
- `PLNProofCalculus.lean` moved from the logic attic to
  `Mettapedia/PLN/Core/PLNProofCalculus.lean`.
- `PLNExperimental.lean` moved from the logic attic to
  `Mettapedia/PLN/Core/PLNExperimental.lean`.
- `PLNCalcBridge.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/Logic/PLNCalcBridge.lean`.
- The `Mettapedia/PLN/Core.lean` and
  `Mettapedia/PLN/Bridges/Logic.lean` room hubs import the moved modules.

Namespace:
- PLN weighted-sequent proof-calculus definitions and soundness statements now
  live under `Mettapedia.PLN.Core.PLNProofCalculus.*`.
- The diagnostic/experimental umbrella now lives under
  `Mettapedia.PLN.Core.PLNExperimental`.
- The conservative-extension bridge to Foundation's Tait calculus now lives
  under `Mettapedia.PLN.Bridges.Logic.PLNCalcBridge.*`.

References repointed:
- The moved files' imports were repointed to the new core and logic-bridge
  module paths.
- The move exposed old unqualified-open assumptions that had depended on the
  `Mettapedia.Logic` namespace context; those opens were made explicit as
  `Mettapedia.PLN.Evidence.EvidenceQuantale`,
  `Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction`, and
  `Mettapedia.PLN.Core.PLNProofCalculus`.

Facade deletion:
- No compatibility module was left at any old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Core.PLNProofCalculus Mettapedia.PLN.Bridges.Logic.PLNCalcBridge Mettapedia.PLN.Core.PLNExperimental Mettapedia.PLN.Core Mettapedia.PLN.Bridges.Logic Mettapedia.PLN`
- Check no old `Mettapedia.Logic.PLNProofCalculus`,
  `Mettapedia.Logic.PLNCalcBridge`, or `Mettapedia.Logic.PLNExperimental`
  namespace/path reference remains outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern; a
  diagnostic doc-comment was tightened to avoid treating proof debt as a
  feature.
- `git diff --check` passes on the migration surface.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.22: PLN K&S totality gate over BinaryEvidence

Status: completed in the working tree.

Moved paths:
- `PLN_KS_Bridge.lean` moved from the logic attic to
  `Mettapedia/PLN/Evidence/PLN_KS_Bridge.lean`.
- The `Mettapedia/PLN/Evidence.lean` room hub imports the moved module.

Namespace:
- BinaryEvidence incomparability, no faithful point-representation, and
  non-Boolean evidence theorems now live under
  `Mettapedia.PLN.Evidence.PLN_KS_Bridge.*`.

References repointed:
- Root imports, implementation checklists, OSLF/K&S sketches, semantics
  decision-tree references, hypercube evidence pointers, first-order PLN rule
  documentation, the legacy quantale archive note, and `papers/xiPLN.tex`
  were repointed from the old logic-attic path/namespace to the PLN evidence
  room.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Evidence.PLN_KS_Bridge Mettapedia.PLN.Evidence Mettapedia.Implementation.PLNParityChecklist Mettapedia.OSLF.Framework.KSUnificationSketch Mettapedia.Logic.SemanticsDecisionTree Mettapedia.ProbabilityTheory.Hypercube.PLNEvidencePointer Mettapedia.ProbabilityTheory.Hypercube.Basic`
- Check no old `Mettapedia.Logic.PLN_KS_Bridge`,
  `Mettapedia/Logic/PLN_KS_Bridge.lean`, or `Logic/PLN_KS_Bridge` reference
  remains outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern; one
  English doc-comment sentence was tightened to avoid a forbidden proof-token
  false positive.
- `git diff --check` passes on the migration surface.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.23: PLN enriched-category bridge

Status: completed in the working tree.

Moved paths:
- `PLNEnrichedCategory.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/CategoryTheory/PLNEnrichedCategory.lean`.
- The `Mettapedia/PLN/Bridges/CategoryTheory.lean` room hub imports the moved
  module.

Namespace:
- The PLN-as-enriched-category bridge now lives under
  `Mettapedia.PLN.Bridges.CategoryTheory.PLNEnrichedCategory.*`.

References repointed:
- The root `Mettapedia.lean` import was repointed from the old logic-attic
  module to the category-theory bridge room.
- No paper or ZarWiki path reference to the old module remained outside this
  ledger.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted/root build:
  `lake build Mettapedia.PLN.Bridges.CategoryTheory.PLNEnrichedCategory Mettapedia.PLN.Bridges.CategoryTheory Mettapedia`
- Check no old `Mettapedia.Logic.PLNEnrichedCategory`,
  `Mettapedia/Logic/PLNEnrichedCategory.lean`, or
  `Logic/PLNEnrichedCategory` reference remains outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern.
- `git diff --check` passes on the touched category-bridge surface. A separate
  pre-existing `WorldModelProfiles.lean` whitespace diff was not touched in
  this cluster.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.24: PLN intuitionistic-logic bridge

Status: completed in the working tree.

Moved paths:
- `PLNIntuitionisticBridge.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/Logic/PLNIntuitionisticBridge.lean`.
- The `Mettapedia/PLN/Bridges/Logic.lean` room hub imports the moved module.

Namespace:
- BinaryEvidence-as-Heyting-semantics, soundness, Dummett, diagonal embedding,
  and classical-simulation bridge theorems now live under
  `Mettapedia.PLN.Bridges.Logic.PLNIntuitionisticBridge.*`.

References repointed:
- Quantifier soundness modules and `PLNCrispEvidence` were repointed from the
  old logic-attic import/namespace to the PLN logic-bridge room.

Facade deletion:
- No compatibility module was left at the old path.

Documentation hygiene:
- A public-facing source doc-comment section that named advisory reviewers was
  removed while preserving the mathematical overview.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Bridges.Logic.PLNIntuitionisticBridge Mettapedia.PLN.Bridges.Logic Mettapedia.PLN.Evidence.PLNCrispEvidence Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.Soundness Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.InfiniteSoundness Mettapedia.PLN.Evidence`
- Check no old `Mettapedia.Logic.PLNIntuitionisticBridge`,
  `Mettapedia/Logic/PLNIntuitionisticBridge.lean`, or
  `Logic/PLNIntuitionisticBridge` reference remains outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern.
- A source scan confirmed the removed public-facing reviewer-name section no
  longer appears in the moved module.
- `git diff --check` passes on the migration surface.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.25: PLN distinction/credal truth-value width bridges

Status: completed in the working tree.

Moved paths:
- `PLNDistinctionCredalBridge.lean` moved from the logic attic to
  `Mettapedia/PLN/TruthValues/PLNDistinctionCredalBridge.lean`.
- `PLNDistinctionCredalOSLFBridge.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/Languages/PLNDistinctionCredalOSLFBridge.lean`.
- These source files were untracked at their old paths, so `git mv` history
  preservation was not applicable; they were physically moved and recorded
  here.
- The `Mettapedia/PLN/TruthValues.lean` and
  `Mettapedia/PLN/Bridges/Languages.lean` room hubs import the moved modules.

Namespace:
- Generic observation-setoid credal-width theorems now live under
  `Mettapedia.PLN.TruthValues.PLNDistinctionCredalBridge.*`.
- OSLF observational-indistinguishability specialization theorems now live under
  `Mettapedia.PLN.Bridges.Languages.PLNDistinctionCredalOSLFBridge.*`.

References repointed:
- `PLNTruthTheoryIndex` imports and qualified references were repointed from the
  old logic-attic modules to the PLN truth-values and language-bridge rooms.
- The OSLF specialization imports/opens the generic truth-values bridge at its
  new namespace.

Facade deletion:
- No compatibility module was left at either old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.TruthValues.PLNDistinctionCredalBridge Mettapedia.PLN.Bridges.Languages.PLNDistinctionCredalOSLFBridge Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex Mettapedia.PLN.TruthValues Mettapedia.PLN.Bridges.Languages`
- Check no old `Mettapedia.Logic.PLNDistinctionCredalBridge`,
  `Mettapedia.Logic.PLNDistinctionCredalOSLFBridge`,
  `Mettapedia/Logic/PLNDistinctionCredalBridge.lean`,
  `Mettapedia/Logic/PLNDistinctionCredalOSLFBridge.lean`,
  `Logic/PLNDistinctionCredalBridge`, or
  `Logic/PLNDistinctionCredalOSLFBridge` reference remains outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern.
- `git diff --check` passes on the migration surface.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.26: standalone PLN worked examples to `Examples/PLN`

Status: completed in the working tree.

Moved paths:
- `PLNMapleCourtCoalitionDemo.lean` moved from the logic attic to
  `Mettapedia/Examples/PLN/MapleCourtCoalitionDemo.lean`.
- `PLNMapleCourtOverlapDemo.lean` moved from the logic attic to
  `Mettapedia/Examples/PLN/MapleCourtOverlapDemo.lean`.
- `PLNKalmanSleepDemo.lean` moved from the logic attic to
  `Mettapedia/Examples/PLN/KalmanSleepDemo.lean`.
- A new `Mettapedia/Examples/PLN.lean` hub imports the moved examples, and the
  root `Mettapedia.lean` aggregator imports that hub.

Namespace:
- The Maple Court coalition example now lives under
  `Mettapedia.Examples.PLN.MapleCourtCoalitionDemo.*`.
- The Maple Court overlap example now lives under
  `Mettapedia.Examples.PLN.MapleCourtOverlapDemo.*`.
- The Kalman wake/sleep example now lives under
  `Mettapedia.Examples.PLN.KalmanSleepDemo.*`.

References repointed:
- The moved files' declaration namespaces and end markers were repointed from
  the old logic-attic namespaces to `Mettapedia.Examples.PLN`.
- The Maple Court examples already had their `BinEvNat` imports repointed to the
  PLN evidence room; those edits were preserved through the move.
- No external Lean, paper, or ZarWiki importer referenced these three old module
  paths.

Facade deletion:
- No compatibility module was left at any old example path.

Verification surface:
- Targeted/root build:
  `lake build Mettapedia.Examples.PLN Mettapedia`
- Check no old `Mettapedia.Logic.PLNMapleCourtCoalitionDemo`,
  `Mettapedia.Logic.PLNMapleCourtOverlapDemo`, or
  `Mettapedia.Logic.PLNKalmanSleepDemo` namespace/path reference remains outside
  this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern; old
  scanner-noisy `0 sorry` doc-comment phrases were tightened to
  "All declarations are closed."
- `git diff --check` passes on the migration surface.
- Spot-check moved example theorem axiom footprints remain within the accepted
  project footprint.

## Cluster 6c.27: classic PLN examples and proof-system showcase to `Examples/PLN`

Status: completed in the working tree.

Moved paths:
- `PLNClassicExamples.lean` moved from the logic attic to
  `Mettapedia/Examples/PLN/ClassicExamples.lean`.
- `PLNProofSystemShowcase.lean` moved from the logic attic to
  `Mettapedia/Examples/PLN/ProofSystemShowcase.lean`.
- The `Mettapedia/Examples/PLN.lean` hub imports both moved modules.

Namespace:
- Classic PLN v0.9 worked-example declarations now live under
  `Mettapedia.Examples.PLN.ClassicExamples.*`.
- The proof-system showcase index now lives under
  `Mettapedia.Examples.PLN.ProofSystemShowcase`.

References repointed:
- The showcase import of classic examples was repointed to
  `Mettapedia.Examples.PLN.ClassicExamples`.
- The showcase's `#check` references were qualified to the actual moved PLN
  evidence namespaces or to the still-logic bridge namespaces they index.
- No external Lean, paper, or ZarWiki importer referenced the old showcase
  module paths outside this pair and this ledger.

Facade deletion:
- No compatibility module was left at either old path.

Repair note:
- An initial broad namespace-rewrite attempt corrupted the moved showcase file.
  The file was restored from the old HEAD content into the new path and then
  repatched narrowly; the examples hub build caught the problem before ledgering
  or full-build certification.

Verification surface:
- Targeted build:
  `lake build Mettapedia.Examples.PLN`
- Check no old `Mettapedia.Logic.PLNClassicExamples`,
  `Mettapedia.Logic.PLNProofSystemShowcase`,
  `Mettapedia/Logic/PLNClassicExamples.lean`,
  `Mettapedia/Logic/PLNProofSystemShowcase.lean`,
  `Logic/PLNClassicExamples`, or `Logic/PLNProofSystemShowcase` reference
  remains outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern; old
  scanner-noisy `0 sorry` prose was tightened.
- `git diff --check` passes on the migration surface.
- Spot-check classic-example theorem axiom footprints remain within the
  accepted project footprint.

## Cluster 6c.28: applied PLN sensor/factory demos to `Examples/PLN`

Status: completed in the working tree.

Moved paths:
- `PLNBrokenSensorDemo.lean` moved from the logic attic to
  `Mettapedia/Examples/PLN/BrokenSensorDemo.lean`.
- `PLNWidgetFactoryDemo.lean` moved from the logic attic to
  `Mettapedia/Examples/PLN/WidgetFactoryDemo.lean`.
- The `Mettapedia/Examples/PLN.lean` hub imports both moved modules.

Namespace:
- Broken sensor hybrid discrete/continuous world-model demo declarations now
  live under `Mettapedia.Examples.PLN.BrokenSensorDemo.*`.
- Widget factory source-conditional Gaussian-mixture demo declarations now live
  under `Mettapedia.Examples.PLN.WidgetFactoryDemo.*`.

References repointed:
- `WidgetFactoryDemo`, `WMGasSensorDriftDemo`, and `WMSteelFaultDemo`
  imports/opens of `ExceedanceSpec` were repointed to
  `Mettapedia.Examples.PLN.BrokenSensorDemo`.
- The gas-policy order-cost demo continues to build through the updated
  `WMGasSensorDriftDemo` importer.
- No paper or ZarWiki path reference to either old module remained outside this
  ledger.

Facade deletion:
- No compatibility module was left at either old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.Examples.PLN Mettapedia.Logic.WMGasSensorDriftDemo Mettapedia.Logic.WMSteelFaultDemo Mettapedia.PLN.WorldModel.OrderCost.PLNWorldModelOrderCostGasPolicyDemo`
- Check no old `Mettapedia.Logic.PLNBrokenSensorDemo`,
  `Mettapedia.Logic.PLNWidgetFactoryDemo`,
  `Mettapedia/Logic/PLNBrokenSensorDemo.lean`,
  `Mettapedia/Logic/PLNWidgetFactoryDemo.lean`,
  `Logic/PLNBrokenSensorDemo`, or `Logic/PLNWidgetFactoryDemo` reference
  remains outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern; old
  scanner-noisy `0 sorry` prose was tightened.
- `git diff --check` passes on the migration surface.
- Spot-check moved demo theorem axiom footprints remain within the accepted
  project footprint.

## Cluster 6c.29: derivation-tracking PLN demo to `Examples/PLN`

Status: completed in the working tree.

Moved paths:
- `PLNDerivationTrackingDemoPropositional.lean` moved from the logic attic to
  `Mettapedia/Examples/PLN/DerivationTrackingDemoPropositional.lean`.
- The `Mettapedia/Examples/PLN.lean` hub imports the moved module.

Namespace:
- The propositional Maple Court derivation-tracking demo declarations now live
  under `Mettapedia.Examples.PLN.DerivationTrackingDemoPropositional.*`.

References repointed:
- No live Lean importer referenced the old module path.
- No paper or ZarWiki path reference to the old module remained outside this
  ledger.
- The only remaining old spelling is historical migration-ledger prose from an
  earlier build-command snapshot.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.Examples.PLN`
- Check no old `Mettapedia.Logic.PLNDerivationTrackingDemoPropositional`,
  `Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivationTrackingDemoPropositional`,
  `Mettapedia/Logic/PLNDerivationTrackingDemoPropositional.lean`,
  `Logic/PLNDerivationTrackingDemoPropositional`, or
  `PLNDerivationTrackingDemoPropositional.lean` reference remains outside this
  ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern.
- `git diff --check` passes on the migration surface.
- Spot-check derivation-tracking theorem axiom footprints remain within the
  accepted project footprint.

## Cluster 6c.30: PLN truth-function bug analysis to `PLN/TruthValues`

Status: completed in the working tree.

Moved paths:
- `PLNBugAnalysis.lean` moved from the logic attic to
  `Mettapedia/PLN/TruthValues/PLNBugAnalysis.lean`.
- The `Mettapedia/PLN/TruthValues.lean` hub imports the moved module.

Namespace:
- Historical confidence-bug and corrected truth-function diagnostics now live
  under `Mettapedia.PLN.TruthValues.PLNBugAnalysis.*`.

References repointed:
- `PLNExperimental`, `PLNErrorMagnificationGrounding`, and
  `PeTTaLibPLNFormalAnalysis` import the new module path.
- Qualified references in `PeTTaLibPLNFormalAnalysis` were repointed to
  `Mettapedia.PLN.TruthValues.PLNBugAnalysis`.
- Truth-value documentation references were updated away from the old logic
  namespace.
- No paper or ZarWiki path reference to the old module remained outside this
  ledger.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.TruthValues.PLNBugAnalysis Mettapedia.PLN.TruthValues Mettapedia.PLN.Core.PLNExperimental Mettapedia.Logic.PLNErrorMagnificationGrounding Mettapedia.Logic.PeTTaLibPLNFormalAnalysis`
- Check no old `Mettapedia.Logic.PLNBugAnalysis`,
  `import Mettapedia.Logic.PLNBugAnalysis`,
  `Mettapedia/Logic/PLNBugAnalysis.lean`, or `Logic/PLNBugAnalysis` reference
  remains outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern.
- `git diff --check` passes on the migration surface.
- Spot-check bug-analysis theorem axiom footprints remain within the accepted
  project footprint.

## Cluster 6c.31: PLN soundness diagnostics to `PLN/TruthValues`

Status: completed in the working tree.

Moved paths:
- `PLNSoundnessCounterexample.lean` moved from the logic attic to
  `Mettapedia/PLN/TruthValues/PLNSoundnessCounterexample.lean`.
- `PLNSoundnessDiagnosis.lean` moved from the logic attic to
  `Mettapedia/PLN/TruthValues/PLNSoundnessDiagnosis.lean`.
- The `Mettapedia/PLN/TruthValues.lean` hub imports both moved modules.

Namespace:
- Binary-evidence confidence-vs-error counterexamples now live under
  `Mettapedia.PLN.TruthValues.PLNSoundnessCounterexample.*`.
- The conjunction/product diagnostic endpoints now live under
  `Mettapedia.PLN.TruthValues.PLNSoundnessDiagnosis.*`.

References repointed:
- `PLNExperimental` imports both diagnostics from the truth-values room.
- `PLNSoundnessDiagnosis` imports the counterexample from its new truth-values
  path.
- No paper or ZarWiki path reference to either old module remained outside this
  ledger.

Facade deletion:
- No compatibility module was left at either old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.TruthValues.PLNSoundnessCounterexample Mettapedia.PLN.TruthValues.PLNSoundnessDiagnosis Mettapedia.PLN.TruthValues Mettapedia.PLN.Core.PLNExperimental`
- Check no old `Mettapedia.Logic.PLNSoundnessCounterexample`,
  `Mettapedia.Logic.PLNSoundnessDiagnosis`,
  `import Mettapedia.Logic.PLNSoundnessCounterexample`,
  `import Mettapedia.Logic.PLNSoundnessDiagnosis`,
  `Mettapedia/Logic/PLNSoundnessCounterexample.lean`,
  `Mettapedia/Logic/PLNSoundnessDiagnosis.lean`,
  `Logic/PLNSoundnessCounterexample`, or `Logic/PLNSoundnessDiagnosis`
  reference remains outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern.
- `git diff --check` passes on the migration surface.
- Spot-check soundness-diagnostic theorem axiom footprints remain within the
  accepted project footprint.

## Cluster 6c.32: PLN distributional dominance/convergence to `PLN/TruthValues`

Status: completed in the working tree.

Moved paths:
- `PLNDistributionalChainDominance.lean` moved from the logic attic to
  `Mettapedia/PLN/TruthValues/PLNDistributionalChainDominance.lean`.
- `PLNDistributionalConvergence.lean` moved from the logic attic to
  `Mettapedia/PLN/TruthValues/PLNDistributionalConvergence.lean`.
- The `Mettapedia/PLN/TruthValues.lean` hub imports both moved modules.

Namespace:
- The files already declared their distributional theorem namespaces under
  `Mettapedia.PLN.TruthValues.*`; the move aligns module path with the existing
  declaration home.

References repointed:
- `PLNDistributionalConvergence` already imported
  `Mettapedia.PLN.TruthValues.PLNDistributionalChainDominance`; the move makes
  that intended module path real.
- No external Lean importer, paper, or ZarWiki reference to the old logic paths
  remained outside this ledger.

Facade deletion:
- No compatibility module was left at either old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.TruthValues.PLNDistributionalChainDominance Mettapedia.PLN.TruthValues.PLNDistributionalConvergence Mettapedia.PLN.TruthValues`
- Check no old `Mettapedia.Logic.PLNDistributionalChainDominance`,
  `Mettapedia.Logic.PLNDistributionalConvergence`,
  `import Mettapedia.Logic.PLNDistributionalChainDominance`,
  `import Mettapedia.Logic.PLNDistributionalConvergence`,
  `Mettapedia/Logic/PLNDistributionalChainDominance.lean`,
  `Mettapedia/Logic/PLNDistributionalConvergence.lean`,
  `Logic/PLNDistributionalChainDominance`, or
  `Logic/PLNDistributionalConvergence` reference remains outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern.
- `git diff --check` passes on the migration surface.
- Spot-check distributional dominance/convergence theorem axiom footprints
  remain within the accepted project footprint.

## Cluster 6c.33: PLN WM/OSLF bridges to `PLN/Bridges/Languages`

Status: completed in the working tree.

Moved paths:
- `PLNWMOSLFBridge.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/Languages/PLNWMOSLFBridge.lean`.
- `PLNWMOSLFBridgeITV.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/Languages/PLNWMOSLFBridgeITV.lean`.
- The `Mettapedia/PLN/Bridges/Languages.lean` hub imports both moved modules.

Namespace:
- The untyped WM-query/OSLF evidence bridge now lives under
  `Mettapedia.PLN.Bridges.Languages.PLNWMOSLFBridge.*`.
- The typed WMΣ/OSLF bridge declarations now live under
  `Mettapedia.PLN.Bridges.Languages.PLNWMOSLFBridgeTyped.*`.
- The ITV typed WMΣ/OSLF threshold declarations now live under
  `Mettapedia.PLN.Bridges.Languages.PLNWMOSLFBridgeITVTyped.*`.

References repointed:
- First-order ξPLN registry and derived-BN rule importers use the new bridge
  paths.
- `PLNErrorMagnificationGrounding`, `PLNCanonicalAPI`, `MarkovTransitionXi`,
  `MarkovPathXi`, `PLNXiCarrierScreening`, and `OSLFNTTWMBridge` were repointed
  mechanically to the new module/namespace.
- ASSOC/PAT and selector-threshold consumers that used the short
  `PLNWMOSLFBridgeITVTyped` prefix now either open the new bridge namespace or
  name the new bridge namespace directly.
- Paper references in `xiPLN.tex` and `pln-review.tex` now cite the
  `Mettapedia/PLN/Bridges/Languages/` path.
- No paper or ZarWiki-mirror path reference to either old module remained
  outside this ledger.

Facade deletion:
- No compatibility module was left at either old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Bridges.Languages.PLNWMOSLFBridge Mettapedia.PLN.Bridges.Languages.PLNWMOSLFBridgeITV Mettapedia.PLN.Bridges.Languages Mettapedia.PLN.RuleFamilies.FirstOrder.PLNXiRuleRegistry Mettapedia.PLN.RuleFamilies.FirstOrder.PLNXiDerivedBNRules Mettapedia.OSLF.Framework.OSLFNTTWMBridge Mettapedia.Logic.PLNCanonicalAPI Mettapedia.Logic.PLNErrorMagnificationGrounding Mettapedia.PLN.InferenceControl.SelectorRewriteThreshold.PLNSelectorRewriteThresholdExamples Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalAssocPatClosure Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalCanary Mettapedia.Logic.MarkovTransitionXi Mettapedia.Logic.MarkovPathXi Mettapedia.Logic.PLNXiCarrierScreening`
- Check no old `Mettapedia.Logic.PLNWMOSLFBridge`,
  `Mettapedia.Logic.PLNWMOSLFBridgeITV`,
  `Mettapedia.Logic.PLNWMOSLFBridgeTyped`,
  `Mettapedia.Logic.PLNWMOSLFBridgeITVTyped`,
  `import Mettapedia.Logic.PLNWMOSLFBridge`,
  `import Mettapedia.Logic.PLNWMOSLFBridgeITV`,
  `Mettapedia/Logic/PLNWMOSLFBridge.lean`,
  `Mettapedia/Logic/PLNWMOSLFBridgeITV.lean`,
  `Logic/PLNWMOSLFBridge`, or `Logic/PLNWMOSLFBridgeITV` reference remains
  outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern.
- `git diff --check` passes on the migration surface.
- Spot-check WM/OSLF bridge theorem axiom footprints remain within the accepted
  project footprint.

## Cluster 6c.34: PLN error-magnification grounding to `PLN/Bridges/Languages`

Status: completed in the working tree.

Moved paths:
- `PLNErrorMagnificationGrounding.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/Languages/PLNErrorMagnificationGrounding.lean`.
- The `Mettapedia/PLN/Bridges/Languages.lean` hub imports the moved module.

Namespace:
- Confidence-threshold transport, WM query-equivalence confidence transport,
  and double-damping gap theorems now live under
  `Mettapedia.PLN.Bridges.Languages.PLNErrorMagnificationGrounding.*`.

References repointed:
- `PLNCore` and `PLNCanonicalAPI` import the moved module from
  `PLN/Bridges/Languages`.
- The canonical alias surface continues to use the short
  `PLNErrorMagnificationGrounding` prefix through the existing
  `open Mettapedia.PLN.Bridges.Languages` scope.
- Paper references in `xiPLN.tex`, `pln-review.tex`, and `wm-pln-book.tex`
  now cite the `Mettapedia/PLN/Bridges/Languages/` path.
- No ZarWiki-mirror path reference to the old module remained outside this
  ledger.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Bridges.Languages.PLNErrorMagnificationGrounding Mettapedia.PLN.Bridges.Languages Mettapedia.Logic.PLNCore Mettapedia.Logic.PLNCanonicalAPI`
- Check no old `Mettapedia.Logic.PLNErrorMagnificationGrounding`,
  `import Mettapedia.Logic.PLNErrorMagnificationGrounding`,
  `Mettapedia/Logic/PLNErrorMagnificationGrounding.lean`, or
  `Logic/PLNErrorMagnificationGrounding` reference remains outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern; broader
  consumer scans only hit pre-existing `0 sorry` prose in `PLNCore`.
- `git diff --check` passes on the migration surface.
- Spot-check error-magnification theorem axiom footprints remain within the
  accepted project footprint.

## Cluster 6c.35: PLN trail-free protocol dynamics to `PLN/InferenceControl`

Status: completed in the working tree.

Moved paths:
- `PLNTrailFreeDynamicsCounterexample.lean` moved from the logic attic to
  `Mettapedia/PLN/InferenceControl/ProtocolDynamics/PLNTrailFreeDynamicsCounterexample.lean`.
- `PLNTrailFreeDampedConvergence.lean` moved from the logic attic to
  `Mettapedia/PLN/InferenceControl/ProtocolDynamics/PLNTrailFreeDampedConvergence.lean`.
- New aggregator `Mettapedia/PLN/InferenceControl/ProtocolDynamics.lean`
  imports both modules.
- The `Mettapedia/PLN/InferenceControl.lean` hub imports the protocol-dynamics
  aggregator.

Namespace:
- The deterministic trail-free two-cycle counterexample now lives under
  `Mettapedia.PLN.InferenceControl.ProtocolDynamics.PLNTrailFreeDynamicsCounterexample.*`.
- The damped fresh-evidence stabilization counterpart now lives under
  `Mettapedia.PLN.InferenceControl.ProtocolDynamics.PLNTrailFreeDampedConvergence.*`.

References repointed:
- `PLNSelectorRewriteThresholdRegression`, `PLNCore`,
  `PLNLargeScaleInferenceCounterexamples`, and the world-model fixpoint SPN
  bridge/regression import or open the moved modules from
  `PLN/InferenceControl/ProtocolDynamics`.
- The SPN bridge's qualified `TVState` alias points at the new namespace.
- Paper references in `xiPLN.tex`, `pln-review.tex`, `wm-pln-book.tex`,
  `wm-pln-book_v3.tex`, and `wm-pln-book_v3_oruzi.tex` now cite the
  `Mettapedia/PLN/InferenceControl/ProtocolDynamics/` path.
- No ZarWiki-mirror path reference to either old module remained outside this
  ledger.

Facade deletion:
- No compatibility module was left at either old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.InferenceControl.ProtocolDynamics.PLNTrailFreeDynamicsCounterexample Mettapedia.PLN.InferenceControl.ProtocolDynamics.PLNTrailFreeDampedConvergence Mettapedia.PLN.InferenceControl.ProtocolDynamics Mettapedia.PLN.InferenceControl Mettapedia.PLN.InferenceControl.SelectorRewriteThreshold.PLNSelectorRewriteThresholdRegression Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointSPNBridge Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointSPNBridgeRegression Mettapedia.Logic.PLNLargeScaleInferenceCounterexamples Mettapedia.Logic.PLNCore`
- Check no old `Mettapedia.Logic.PLNTrailFreeDynamicsCounterexample`,
  `Mettapedia.Logic.PLNTrailFreeDampedConvergence`,
  `import Mettapedia.Logic.PLNTrailFreeDynamicsCounterexample`,
  `import Mettapedia.Logic.PLNTrailFreeDampedConvergence`,
  `Mettapedia/Logic/PLNTrailFreeDynamicsCounterexample.lean`,
  `Mettapedia/Logic/PLNTrailFreeDampedConvergence.lean`,
  `Logic/PLNTrailFreeDynamicsCounterexample`, or
  `Logic/PLNTrailFreeDampedConvergence` reference remains outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern.
- `git diff --check` passes on the migration surface.
- Spot-check protocol-dynamics theorem axiom footprints are either empty or
  remain within the accepted project footprint.

## Cluster 6c.36: PLN certified-chaining no-go theorems to `PLN/InferenceControl`

Status: completed in the working tree.

Moved paths:
- `PLNCoverageCollapseNoGo.lean` moved from the logic attic to
  `Mettapedia/PLN/InferenceControl/CertifiedChaining/PLNCoverageCollapseNoGo.lean`.
- `PLNSensitivityNoGo.lean` moved from the logic attic to
  `Mettapedia/PLN/InferenceControl/CertifiedChaining/PLNSensitivityNoGo.lean`.
- New aggregator `Mettapedia/PLN/InferenceControl/CertifiedChaining.lean`
  imports both modules.
- The `Mettapedia/PLN/InferenceControl.lean` hub imports the certified-chaining
  aggregator.

Namespace:
- Coverage-collapse chain-composition theorems now live under
  `Mettapedia.PLN.InferenceControl.CertifiedChaining.PLNCoverageCollapseNoGo.*`.
- Lipschitz sensitivity-amplification chain-composition theorems now live under
  `Mettapedia.PLN.InferenceControl.CertifiedChaining.PLNSensitivityNoGo.*`.

References repointed:
- Paper references in `wm-pln-book.tex`, `wm-pln-book_v3.tex`, and
  `wm-pln-book_v3_oruzi.tex` now cite the
  `Mettapedia/PLN/InferenceControl/CertifiedChaining/` path.
- No Lean importer or local ZarWiki-mirror reference to either old module
  remained outside this ledger.

Facade deletion:
- No compatibility module was left at either old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.InferenceControl.CertifiedChaining.PLNCoverageCollapseNoGo Mettapedia.PLN.InferenceControl.CertifiedChaining.PLNSensitivityNoGo Mettapedia.PLN.InferenceControl.CertifiedChaining Mettapedia.PLN.InferenceControl`
- Check no old `Mettapedia.Logic.PLNCoverageCollapseNoGo`,
  `Mettapedia.Logic.PLNSensitivityNoGo`,
  `Mettapedia/Logic/PLNCoverageCollapseNoGo.lean`,
  `Mettapedia/Logic/PLNSensitivityNoGo.lean`,
  `Logic/PLNCoverageCollapseNoGo`, or `Logic/PLNSensitivityNoGo` reference
  remains outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern.
- `git diff --check` passes on the migration surface.
- Spot-check certified-chaining no-go theorem axiom footprints remain within
  the accepted project footprint.

## Cluster 6c.37: PLN large-scale inference counterexample index to `PLN/InferenceControl`

Status: completed in the working tree.

Moved paths:
- `PLNLargeScaleInferenceCounterexamples.lean` moved from the logic attic to
  `Mettapedia/PLN/InferenceControl/Counterexamples/PLNLargeScaleInferenceCounterexamples.lean`.
- New aggregator `Mettapedia/PLN/InferenceControl/Counterexamples.lean`
  imports the moved module.
- The `Mettapedia/PLN/InferenceControl.lean` hub imports the counterexamples
  aggregator.

Namespace:
- Chapter-9 large-scale inference counterexample aliases now live under
  `Mettapedia.PLN.InferenceControl.Counterexamples.PLNLargeScaleInferenceCounterexamples.*`.

References repointed:
- `PLNCore` imports the moved module from
  `PLN/InferenceControl/Counterexamples`.
- Paper references in `xiPLN.tex` now cite the
  `Mettapedia/PLN/InferenceControl/Counterexamples/` path.
- No local ZarWiki-mirror path reference to the old module remained outside
  this ledger.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.InferenceControl.Counterexamples.PLNLargeScaleInferenceCounterexamples Mettapedia.PLN.InferenceControl.Counterexamples Mettapedia.PLN.InferenceControl Mettapedia.Logic.PLNCore`
- Check no old `Mettapedia.Logic.PLNLargeScaleInferenceCounterexamples`,
  `import Mettapedia.Logic.PLNLargeScaleInferenceCounterexamples`,
  `Mettapedia/Logic/PLNLargeScaleInferenceCounterexamples.lean`, or
  `Logic/PLNLargeScaleInferenceCounterexamples` reference remains outside this
  ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern.
- `git diff --check` passes on the migration surface.
- Spot-check large-scale inference counterexample theorem axiom footprints
  remain within the accepted project footprint.

## Cluster 6c.38: PLN ξ carrier screening to `PLN/Bridges/ProbabilityTheory`

Status: completed in the working tree.

Moved paths:
- `PLNXiCarrierScreening.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/ProbabilityTheory/PLNXiCarrierScreening.lean`.
- The `Mettapedia/PLN/Bridges/ProbabilityTheory.lean` hub imports the moved
  module.

Namespace:
- Carrier-family, query-indexed carrier-family, Normal-Gamma, Dirichlet, and
  Markov carrier screening declarations now live under
  `Mettapedia.PLN.Bridges.ProbabilityTheory.PLNXiCarrierScreening.*`.

References repointed:
- `PLNCanonicalAPI` imports the moved module from
  `PLN/Bridges/ProbabilityTheory`.
- The canonical carrier-family alias now qualifies the new bridge namespace
  explicitly.
- Paper references in `xiPLN.tex` and `wm-pln-book_v3.tex` now cite the
  `Mettapedia/PLN/Bridges/ProbabilityTheory/` path.
- No local ZarWiki-mirror path reference to the old module remained outside
  this ledger.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Bridges.ProbabilityTheory.PLNXiCarrierScreening Mettapedia.PLN.Bridges.ProbabilityTheory Mettapedia.Logic.PLNCanonicalAPI`
- Check no old `Mettapedia.Logic.PLNXiCarrierScreening`,
  `import Mettapedia.Logic.PLNXiCarrierScreening`,
  `Mettapedia/Logic/PLNXiCarrierScreening.lean`, or
  `Logic/PLNXiCarrierScreening` reference remains outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern.
- `git diff --check` passes on the migration surface.
- Spot-check carrier-screening theorem axiom footprints remain within the
  accepted project footprint.

## Cluster 6c.39: weighted Gaussian E/M bridge to `PLN/Bridges/ProbabilityTheory`

Status: completed in the working tree.

Moved paths:
- `WeightedNormalGammaSurface.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/ProbabilityTheory/WeightedNormalGammaSurface.lean`.
- `PLNGaussianEM.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/ProbabilityTheory/PLNGaussianEM.lean`.
- `PLNGaussianEMExtension.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/ProbabilityTheory/PLNGaussianEMExtension.lean`.
- The `Mettapedia/PLN/Bridges/ProbabilityTheory.lean` hub imports the moved
  Gaussian bridge modules.

Namespace:
- Weighted Normal-Gamma sufficient-statistic bridge declarations now live under
  `Mettapedia.PLN.Bridges.ProbabilityTheory.WeightedNormalGammaSurface.*`.
- Finite one-step Gaussian mixture E/M declarations now live under
  `Mettapedia.PLN.Bridges.ProbabilityTheory.PLNGaussianEM.*`.
- The curated Gaussian extension aliases now live directly under
  `Mettapedia.PLN.Bridges.ProbabilityTheory.*`.
- The generic `SufficientStatisticSurface` substrate remains in
  `Mettapedia.Logic.SufficientStatisticSurface`; this cluster only moved the
  weighted Normal-Gamma / Gaussian PLN bridge layer.

References repointed:
- `PLNCore` and `PLNCanonicalAPI` import the moved Gaussian extension from
  `PLN/Bridges/ProbabilityTheory`.
- Canonical advanced-Gaussian aliases now qualify the new probability-bridge
  namespaces explicitly.
- No local paper or ZarWiki path reference to the old Gaussian bridge modules
  remained outside this ledger.

Facade deletion:
- No compatibility module was left at the old paths.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Bridges.ProbabilityTheory.WeightedNormalGammaSurface Mettapedia.PLN.Bridges.ProbabilityTheory.PLNGaussianEM Mettapedia.PLN.Bridges.ProbabilityTheory.PLNGaussianEMExtension Mettapedia.PLN.Bridges.ProbabilityTheory Mettapedia.Logic.PLNCore Mettapedia.Logic.PLNCanonicalAPI`
- Check no old `Mettapedia.Logic.PLNGaussianEM`,
  `Mettapedia.Logic.WeightedNormalGammaSurface`,
  `import Mettapedia.Logic.PLNGaussianEM`,
  `import Mettapedia.Logic.WeightedNormalGammaSurface`,
  `Mettapedia/Logic/PLNGaussianEM.lean`,
  `Mettapedia/Logic/PLNGaussianEMExtension.lean`, or
  `Mettapedia/Logic/WeightedNormalGammaSurface.lean` reference remains outside
  this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern.
- `git diff --check` passes on the migration surface.
- Spot-check Gaussian E/M and weighted-surface theorem axiom footprints remain
  within the accepted project footprint.

## Cluster 6c.40: temporal PLN rule families to `PLN/RuleFamilies/Temporal`

Status: completed in the working tree.

Moved paths:
- `PLNTemporal.lean` moved from the logic attic to
  `Mettapedia/PLN/RuleFamilies/Temporal/PLNTemporal.lean`.
- `PLNProbabilisticEventCalculus.lean` moved from the logic attic to
  `Mettapedia/PLN/RuleFamilies/Temporal/PLNProbabilisticEventCalculus.lean`.
- `PLNTemporalCausalInference.lean` moved from the logic attic to
  `Mettapedia/PLN/RuleFamilies/Temporal/PLNTemporalCausalInference.lean`.
- New aggregator `Mettapedia/PLN/RuleFamilies/Temporal.lean` imports the
  temporal rule-family room and is imported by `Mettapedia/PLN/RuleFamilies.lean`.

Namespace:
- Temporal predicate operators, notation, predictive implication, and temporal
  transitivity now live under `Mettapedia.PLN.RuleFamilies.Temporal.*`.
- BinaryEvidence-valued event-calculus declarations now live under
  `Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.*`.
- Chapter-14 temporal/causal inference declarations now live under
  `Mettapedia.PLN.RuleFamilies.Temporal.PLNTemporalCausalInference.*`.

References repointed:
- `PLNCore`, `PLNCanonicalAPI`, `ModalQueryEncoder`, and
  `TemporalDeonticBridge` now import or open the moved temporal PLN modules from
  `PLN/RuleFamilies/Temporal`.
- Paper path references in the WM-PLN, xiPLN, and review papers now cite the
  `Mettapedia/PLN/RuleFamilies/Temporal/` paths.
- Conceptual logic-side notes that mention the temporal PLN surface now name the
  new namespace/path without importing the moved modules where they intentionally
  avoid notation conflicts.

Facade deletion:
- No compatibility module was left at the old paths.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.RuleFamilies.Temporal.PLNTemporal Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus Mettapedia.PLN.RuleFamilies.Temporal.PLNTemporalCausalInference Mettapedia.PLN.RuleFamilies.Temporal Mettapedia.PLN.RuleFamilies Mettapedia.Logic.ModalQueryEncoder Mettapedia.Logic.TemporalDeonticBridge Mettapedia.Logic.PLNCore Mettapedia.Logic.PLNCanonicalAPI`
- Check no old `Mettapedia.Logic.PLNTemporal`,
  `Mettapedia.Logic.PLNProbabilisticEventCalculus`,
  `Mettapedia.Logic.PLNTemporalCausalInference`,
  `import Mettapedia.Logic.PLNTemporal`,
  `import Mettapedia.Logic.PLNProbabilisticEventCalculus`,
  `import Mettapedia.Logic.PLNTemporalCausalInference`, or corresponding old
  file-path reference remains outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern.
- `git diff --check` passes on the migration surface.
- Spot-check temporal PLN theorem axiom footprints remain within the accepted
  project footprint.

## Cluster 6c.41: PLN worked application examples to `Examples/PLN`

Status: completed in the working tree.

Moved paths:
- `PLNBioHypothesisGeneration.lean` moved from the logic attic to
  `Mettapedia/Examples/PLN/BioHypothesisGeneration.lean`.
- `PLNBioIncrementalHyperseed.lean` moved from the logic attic to
  `Mettapedia/Examples/PLN/BioIncrementalHyperseed.lean`.
- `PLNMapleCourtDemo.lean` moved from the logic attic to
  `Mettapedia/Examples/PLN/MapleCourtDemo.lean`.
- The `Mettapedia/Examples/PLN.lean` hub imports the moved application
  examples.

Namespace:
- The rejuve-bio noisy-OR benchmark declarations now live under
  `Mettapedia.Examples.PLN.BioHypothesisGeneration.*`.
- The incremental bio Hyperseed fixture declarations now live under
  `Mettapedia.Examples.PLN.BioIncrementalHyperseed.*`.
- The Maple Court running-example declarations now live under
  `Mettapedia.Examples.PLN.MapleCourtDemo.*`.

References repointed:
- `ProbLogCompilation` imports and opens the moved bio hypothesis example from
  `Examples/PLN`.
- Maple Court conformance files now import, open, and qualify the moved running
  example under `Mettapedia.Examples.PLN.MapleCourtDemo`.
- Paper and conformance documentation references now cite the
  `Mettapedia/Examples/PLN/` paths.

Facade deletion:
- No compatibility module was left at the old paths.

Verification surface:
- Targeted build:
  `lake build Mettapedia.Examples.PLN.BioHypothesisGeneration Mettapedia.Examples.PLN.BioIncrementalHyperseed Mettapedia.Examples.PLN.MapleCourtDemo Mettapedia.Examples.PLN Mettapedia.Logic.ProbLogCompilation Mettapedia.Conformance.MapleCourtConformance Mettapedia.Conformance.MapleCourtEvidenceConformance`
- Check no old `Mettapedia.Logic.PLNBioHypothesisGeneration`,
  `Mettapedia.Logic.PLNBioIncrementalHyperseed`,
  `Mettapedia.Logic.PLNMapleCourtDemo`, corresponding old imports, or old
  file-path references remain outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern.
- `git diff --check` passes on the migration surface.
- Spot-check moved application-example theorem axiom footprints remain within
  the accepted project footprint.

## Cluster 6c.42: PLN public core and canonical API to `PLN/Core`

Status: completed in the working tree.

Moved paths:
- `PLNCore.lean` moved from the logic attic to
  `Mettapedia/PLN/Core/PLNCore.lean`.
- `PLNCanonicalAPI.lean` moved from the logic attic to
  `Mettapedia/PLN/Core/PLNCanonicalAPI.lean`.
- `PLNCOMPLETE.lean` moved from the logic attic to
  `Mettapedia/PLN/Core/PLNCOMPLETE.lean`.
- The `Mettapedia/PLN/Core.lean` hub imports the moved public entrypoints.

Namespace:
- The curated core entrypoint namespace now lives under
  `Mettapedia.PLN.Core.PLNCore`.
- The canonical public API namespace now lives under
  `Mettapedia.PLN.Core.PLNCanonical`.
- The compatibility-complete entrypoint namespace now lives under
  `Mettapedia.PLN.Core.PLNCOMPLETE`.

References repointed:
- PLN concept-geometry and selector-threshold consumers now import the canonical
  API from `Mettapedia.PLN.Core.PLNCanonicalAPI` and open/qualify
  `Mettapedia.PLN.Core.PLNCanonical`.
- Paper, generated-doc, and local ZarWiki references that named the old logic
  attic paths now cite `Mettapedia/PLN/Core/PLNCanonicalAPI.lean` or
  `Mettapedia/PLN/Core/PLNCore.lean`.

Facade deletion:
- No compatibility module was left at the old paths.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Core.PLNCanonicalAPI Mettapedia.PLN.Core.PLNCore Mettapedia.PLN.Core.PLNCOMPLETE Mettapedia.PLN.Core Mettapedia.PLN Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalAssocPatClosure Mettapedia.PLN.InferenceControl.SelectorRewriteThreshold.PLNSelectorRewriteThresholdExamples`
- Check no old `Mettapedia.Logic.PLNCanonicalAPI`,
  `Mettapedia.Logic.PLNCore`, `Mettapedia.Logic.PLNCOMPLETE`,
  `Mettapedia.Logic.PLNCanonical`, corresponding old imports, or old file-path
  references remain outside this ledger.
- Check no root-level `Mettapedia/Logic/PLN*.lean` file remains.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern.
- `git diff --check` passes on the migration surface, paper references, and
  local ZarWiki references.
- Spot-check canonical API theorem-handle axiom footprints remain within the
  accepted project footprint.

## Cluster 6c.43: exact PLN core and WM calculus surfaces

Status: completed in the working tree.

Moved paths:
- `CompletePLN.lean` moved from the logic attic to
  `Mettapedia/PLN/Core/CompletePLN.lean`.
- `SufficientStatisticSurface.lean` moved from the logic attic to
  `Mettapedia/PLN/WorldModel/SufficientStatisticSurface.lean`.
- `WMCalculusSoundness.lean` moved from the logic attic to
  `Mettapedia/PLN/WorldModel/WMCalculusSoundness.lean`.
- The `Mettapedia/PLN/Core.lean` and `Mettapedia/PLN/WorldModel.lean` hubs
  import the moved modules.

Namespace:
- Exact Bayesian PLN now lives under `Mettapedia.PLN.Core.CompletePLN`.
- The sufficient-statistic surface now lives under
  `Mettapedia.PLN.WorldModel.SufficientStatisticSurface`.
- The world-model calculus soundness interface now lives under
  `Mettapedia.PLN.WorldModel.WMCalculusSoundness`.

References repointed:
- PLN evidence, truth-value, bridge, Hyperseed, KR concept-ontology, Markov, and
  example consumers now import, open, and qualify the moved modules from
  `PLN/Core` and `PLN/WorldModel`.
- Paper references that named the old `Logic/WMCalculusSoundness.lean` path now
  cite `Mettapedia/PLN/WorldModel/WMCalculusSoundness.lean`.
- Stale `open Mettapedia.Logic` lines in already-moved non-Logic rooms were
  removed when the precise imports stopped providing that attic namespace as a
  side effect.

Facade deletion:
- No compatibility module was left at the old paths.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Core.CompletePLN Mettapedia.PLN.WorldModel.SufficientStatisticSurface Mettapedia.PLN.WorldModel.WMCalculusSoundness Mettapedia.PLN.Core Mettapedia.PLN.WorldModel Mettapedia.PLN.Core.PLNCore Mettapedia.PLN.Core.PLNCanonicalAPI Mettapedia.Logic.ProbLogCompilation Mettapedia.Examples.PLN.BioHypothesisGeneration Mettapedia.Examples.PLN.ProofSystemShowcase Mettapedia.Hyperseed.Basic Mettapedia.PLN.Bridges.ProbabilityTheory.PLNGaussianEM Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex`
- Check no old `Mettapedia.Logic.CompletePLN`,
  `Mettapedia.Logic.SufficientStatisticSurface`,
  `Mettapedia.Logic.WMCalculusSoundness`, corresponding old imports, or old
  file-path references remain outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern.
- Spot-check moved core/world-model theorem axiom footprints remain within the
  accepted project footprint.

## Cluster 6c.44: PLN evidence, first-order residual, and universal WM support

Status: completed in the working tree.

Moved paths:
- `SourceReliability.lean` moved from the logic attic to
  `Mettapedia/PLN/Evidence/SourceReliability.lean`.
- `ResidualDeductionFormula.lean` moved from the logic attic to
  `Mettapedia/PLN/RuleFamilies/FirstOrder/ResidualDeductionFormula.lean`.
- `UniversalEnsembleWM.lean` moved from the logic attic to
  `Mettapedia/PLN/WorldModel/UniversalEnsembleWM.lean`.
- The `Mettapedia/PLN/Evidence.lean`,
  `Mettapedia/PLN/RuleFamilies/FirstOrder.lean`, and
  `Mettapedia/PLN/WorldModel.lean` hubs import the moved modules.

Namespace:
- Source reliability now lives under
  `Mettapedia.PLN.Evidence.SourceReliability`.
- Residual deduction formulas now live under
  `Mettapedia.PLN.RuleFamilies.FirstOrder.ResidualDeductionFormula`.
- Universal ensemble world-model theorems now live under
  `Mettapedia.PLN.WorldModel.UniversalEnsembleWM`.

References repointed:
- PLN proof-system showcase checks now refer to the moved source-reliability
  and universal-ensemble theorem handles from their PLN rooms.
- Paper references that named the old logic attic paths now cite the
  corresponding `Mettapedia/PLN/...` module paths.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the three moved modules.

Facade deletion:
- No compatibility module was left at the old paths.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Evidence.SourceReliability Mettapedia.PLN.RuleFamilies.FirstOrder.ResidualDeductionFormula Mettapedia.PLN.WorldModel.UniversalEnsembleWM Mettapedia.PLN.Evidence Mettapedia.PLN.RuleFamilies.FirstOrder Mettapedia.PLN.WorldModel Mettapedia.Examples.PLN.ProofSystemShowcase`
- Check no old `Mettapedia.Logic.SourceReliability`,
  `Mettapedia.Logic.ResidualDeductionFormula`,
  `Mettapedia.Logic.UniversalEnsembleWM`, corresponding old imports, or old
  file-path references remain outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern.
- Spot-check moved evidence, residual-deduction, and universal-world-model
  theorem axiom footprints remain within the accepted project footprint.

## Cluster 6c.45: WM-PLN worked examples

Status: completed in the working tree.

Moved paths:
- `TemporalChainingExample.lean` moved from the logic attic to
  `Mettapedia/Examples/PLN/TemporalChainingExample.lean`.
- `WMDemandDemo.lean` moved from the logic attic to
  `Mettapedia/Examples/PLN/WMDemandDemo.lean`.
- `WMForkDemandDemo.lean` moved from the logic attic to
  `Mettapedia/Examples/PLN/WMForkDemandDemo.lean`.
- `WMDerivationTrackingDemo.lean` moved from the logic attic to
  `Mettapedia/Examples/PLN/WMDerivationTrackingDemo.lean`.
- `WMGasSensorDriftDemo.lean` moved from the logic attic to
  `Mettapedia/Examples/PLN/WMGasSensorDriftDemo.lean`.
- `WMSteelFaultDemo.lean` moved from the logic attic to
  `Mettapedia/Examples/PLN/WMSteelFaultDemo.lean`.
- `WMNABSleepDemo.lean` moved from the logic attic to
  `Mettapedia/Examples/PLN/WMNABSleepDemo.lean`.
- `WMUWCSEGateDemo.lean` moved from the logic attic to
  `Mettapedia/Examples/PLN/WMUWCSEGateDemo.lean`.
- The `Mettapedia/Examples/PLN.lean` hub imports the moved demos.

Namespace:
- The worked examples now live under their corresponding
  `Mettapedia.Examples.PLN.*` namespaces.

References repointed:
- The order-cost gas-policy consumer now imports and opens
  `Mettapedia.Examples.PLN.WMGasSensorDriftDemo`.
- Paper references that named the old logic attic paths now cite the
  corresponding `Mettapedia/Examples/PLN/...` module paths.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the eight moved examples.

Facade deletion:
- No compatibility module was left at the old paths.

Verification surface:
- Targeted build:
  `lake build Mettapedia.Examples.PLN.TemporalChainingExample Mettapedia.Examples.PLN.WMDemandDemo Mettapedia.Examples.PLN.WMForkDemandDemo Mettapedia.Examples.PLN.WMDerivationTrackingDemo Mettapedia.Examples.PLN.WMGasSensorDriftDemo Mettapedia.Examples.PLN.WMSteelFaultDemo Mettapedia.Examples.PLN.WMNABSleepDemo Mettapedia.Examples.PLN.WMUWCSEGateDemo Mettapedia.Examples.PLN Mettapedia.PLN.WorldModel.OrderCost.PLNWorldModelOrderCostGasPolicyDemo`
- Check no old `Mettapedia.Logic.*` namespace, corresponding old import, or old
  file-path reference remains for the moved example modules outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern.
- Spot-check moved example headline theorem axiom footprints remain within the
  accepted project footprint.

## Cluster 6c.46: applied evidence-ledger PLN demos

Status: completed in the working tree.

Moved paths:
- `AIOutcomesDemo.lean` moved from the logic attic to
  `Mettapedia/Examples/PLN/AIOutcomesDemo.lean`.
- `GJPForecastDemo.lean` moved from the logic attic to
  `Mettapedia/Examples/PLN/GJPForecastDemo.lean`.
- The `Mettapedia/Examples/PLN.lean` hub imports the moved demos.

Namespace:
- The applied evidence-ledger demos now live under their corresponding
  `Mettapedia.Examples.PLN.*` namespaces.

References repointed:
- Internal Lean imports and qualified references now use the
  `Mettapedia.Examples.PLN.*` module paths.
- Paper and ZarWiki references that named the old logic attic paths now cite the
  corresponding `Mettapedia/Examples/PLN/...` module paths.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the two moved demos.

Facade deletion:
- No compatibility module was left at the old paths.

Verification surface:
- Targeted build:
  `lake build Mettapedia.Examples.PLN.AIOutcomesDemo Mettapedia.Examples.PLN.GJPForecastDemo Mettapedia.Examples.PLN`
- Check no old `Mettapedia.Logic.AIOutcomesDemo` or
  `Mettapedia.Logic.GJPForecastDemo`, corresponding old imports, or old
  file-path references remain outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern.
- Spot-check moved demo theorem axiom footprints remain within the accepted
  project footprint.

## Cluster 6c.47: Raven induction and abduction rule-family theory

Status: completed in the working tree.

Moved paths:
- `RavenAbduction.lean` moved from the logic attic to
  `Mettapedia/PLN/RuleFamilies/FirstOrder/RavenAbduction.lean`.
- `RavenAsymmetricInduction.lean` moved from the logic attic to
  `Mettapedia/PLN/RuleFamilies/FirstOrder/RavenAsymmetricInduction.lean`.
- The `Mettapedia/PLN/RuleFamilies/FirstOrder.lean` hub imports the moved
  rule-family examples explicitly.

Namespace:
- Raven abduction now lives under
  `Mettapedia.PLN.RuleFamilies.FirstOrder.RavenAbduction`.
- Raven asymmetric induction now lives under
  `Mettapedia.PLN.RuleFamilies.FirstOrder.RavenAsymmetricInduction`.

References repointed:
- The Raven bridge consumers now import and open the moved modules from the
  first-order PLN rule-family room.
- Paper and ZarWiki references that named the old logic attic paths now cite the
  corresponding `Mettapedia/PLN/RuleFamilies/FirstOrder/...` module paths.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the two moved Raven modules.

Facade deletion:
- No compatibility module was left at the old paths.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.RuleFamilies.FirstOrder.RavenAbduction Mettapedia.PLN.RuleFamilies.FirstOrder.RavenAsymmetricInduction Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRavenAbductionBridge Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRavenInductionBridge Mettapedia.PLN.RuleFamilies.FirstOrder Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOL`
- Check no old `Mettapedia.Logic.RavenAbduction` or
  `Mettapedia.Logic.RavenAsymmetricInduction`, corresponding old imports, or
  file-path references remain outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern.
- Spot-check Raven induction/abduction theorem axiom footprints remain within
  the accepted project footprint.

## Cluster 6c.48: Bayesian-network topology regression for first-order PLN rules

Status: completed in the working tree.

Moved paths:
- `BNTopologyRegression.lean` moved from the logic attic to
  `Mettapedia/PLN/RuleFamilies/FirstOrder/BNTopologyRegression.lean`.
- The `Mettapedia/PLN/RuleFamilies/FirstOrder.lean` hub imports the moved
  regression module explicitly.

Namespace:
- The BN topology regression handles now live under
  `Mettapedia.PLN.RuleFamilies.FirstOrder.BNTopologyRegression`.

References repointed:
- No external Lean, paper, or ZarWiki reference still names the old logic attic
  module path for this regression module.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.RuleFamilies.FirstOrder.BNTopologyRegression Mettapedia.PLN.RuleFamilies.FirstOrder.PLNXiDerivedBNRules Mettapedia.PLN.RuleFamilies.FirstOrder`
- Check no old `Mettapedia.Logic.BNTopologyRegression`, corresponding old
  import, or file-path reference remains outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern.
- Spot-check BN topology regression handle axiom footprints remain within the
  accepted project footprint.

## Cluster 6c.49: WM-PLN distributional worked examples

Status: completed in the working tree.

Moved paths:
- `WMPLNDistributionalExamples.lean` moved from the logic attic to
  `Mettapedia/Examples/PLN/WMPLNDistributionalExamples.lean`.
- The `Mettapedia/Examples/PLN.lean` hub imports the moved worked-example
  module explicitly.

Namespace:
- The distributional worked examples now live under
  `Mettapedia.Examples.PLN.WMPLNDistributionalExamples`.

References repointed:
- The implementation parity checklist and distributional truth-function
  discussion now name the moved example module from `Examples/PLN`.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the moved distributional example module.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.Examples.PLN.WMPLNDistributionalExamples Mettapedia.Examples.PLN Mettapedia.Implementation.PLNParityChecklist Mettapedia.PLN.TruthValues.WMPLNDistributionalTruthFunctions`
- Check no old `Mettapedia.Logic.WMPLNDistributionalExamples`, corresponding
  old import, or file-path reference remains outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern.
- Spot-check distributional example theorem axiom footprints remain within the
  accepted project footprint.

## Cluster 6c.50: PLN premise-selection inference-control substrate

Status: completed in the working tree.

Moved paths:
- The former root-level `PremiseSelection*` files moved from the logic attic to
  `Mettapedia/PLN/InferenceControl/PremiseSelection/*`.
- Redundant leaf prefixes were removed at the new home, e.g.
  `PremiseSelectionCoverage.lean` is now
  `Mettapedia/PLN/InferenceControl/PremiseSelection/Coverage.lean`.
- The `Mettapedia/PLN/InferenceControl/PremiseSelection.lean` hub now imports
  the selector substrate modules as well as the existing Chapter-13 regression
  and chainer surfaces.

Namespace:
- The main selector definitions now live under
  `Mettapedia.PLN.InferenceControl.PremiseSelection`.
- The ranking/optimality definitions now live under
  `Mettapedia.PLN.InferenceControl.PremiseSelection.Optimality`.

References repointed:
- PLN core/API consumers, OSLF selector semantics, Chapter-13 inference-control
  modules, DocText surfaces, papers, and local project-status references were
  repointed away from the old logic attic paths and namespaces.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the moved premise-selection modules.

Facade deletion:
- No compatibility module was left at the old paths.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.InferenceControl.PremiseSelection Mettapedia.PLN.Core.PLNCore Mettapedia.PLN.Core.PLNCanonicalAPI Mettapedia.OSLF.Framework.PLNSelectorGSLT Mettapedia.OSLF.Framework.PLNSelectorLanguageDef Mettapedia.DocText.LogicReadmeCompositional`
- Check no old `Mettapedia.Logic.PremiseSelection`, corresponding old imports,
  or old file-path references remain outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern; the only
  broad-text hit was prose using the word "admits".
- Spot-check Chapter-13 selector theorem axiom footprints remain within the
  accepted project footprint.

## Cluster 6c.51: PLN soundness/completeness core analysis

Status: completed in the working tree.

Moved paths:
- `SoundnessCompleteness.lean` moved from the logic attic to
  `Mettapedia/PLN/Core/SoundnessCompleteness.lean`.
- The `Mettapedia/PLN/Core.lean` hub imports the moved PLN core analysis.

Namespace:
- The soundness/completeness analysis now lives under
  `Mettapedia.PLN.Core.SoundnessCompleteness`.

References repointed:
- PLN core consumers and xiPLN paper references now cite the moved PLN core
  module.
- Stale paper and DocText references to the already-moved
  `PLNXiDerivedBNRules` module were repointed to
  `Mettapedia/PLN/RuleFamilies/FirstOrder/PLNXiDerivedBNRules.lean`.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the moved soundness/completeness module.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Core.SoundnessCompleteness Mettapedia.PLN.Core.PLNCore Mettapedia.PLN.Core Mettapedia.DocText.LogicReadmeCompositional`
- Check no old `Mettapedia.Logic.SoundnessCompleteness`, corresponding old
  import, or file-path reference remains outside this ledger.
- Check no stale `Mettapedia/Logic/PLNXiDerivedBNRules.lean` reference remains
  outside this ledger.
- Check no migration facade marker remains.
- The moved proof-hole scan found no active unfinished-proof pattern.
- Spot-check soundness/completeness theorem axiom footprints remain within the
  accepted project footprint.

## Cluster 6c.52: moment and finite-exchangeability probability theory

Status: completed in the working tree.

Moved paths:
- `MomentSequences.lean` moved from the logic attic to
  `Mettapedia/ProbabilityTheory/Moments/MomentSequences.lean`.
- `HausdorffMoment.lean` moved from the logic attic to
  `Mettapedia/ProbabilityTheory/Moments/HausdorffMoment.lean`.
- `DiaconisFreedmanFinite.lean` moved from the logic attic to
  `Mettapedia/ProbabilityTheory/Exchangeability/DiaconisFreedmanFinite.lean`.
- `CategoricalMixture.lean` moved from the logic attic to
  `Mettapedia/ProbabilityTheory/Exchangeability/CategoricalMixture.lean`.
- The new `Mettapedia/ProbabilityTheory/Moments.lean` hub imports the moment
  modules, and the exchangeability hub imports the finite-exchangeability and
  categorical-mixture modules.

Namespace:
- Moment-sequence definitions now live under
  `Mettapedia.ProbabilityTheory.Moments.MomentSequences`.
- Hausdorff-moment definitions now live under
  `Mettapedia.ProbabilityTheory.Moments.HausdorffMoment`.
- Diaconis-Freedman finite L1 lemmas now live under
  `Mettapedia.ProbabilityTheory.Exchangeability.DiaconisFreedmanFinite`.
- Categorical-mixture/de-Finetti definitions now live under
  `Mettapedia.ProbabilityTheory.Exchangeability.CategoricalDeFinetti`.

References repointed:
- De Finetti, Hausdorff bridge, categorical higher-order-probability, and PLN
  local-mixture consumers now import or qualify the moved probability modules.
- README/paper references that named the old logic-attic categorical-mixture
  path now cite the new exchangeability path.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the moved moment and categorical-mixture modules.

Facade deletion:
- No compatibility module was left at the old paths.

Verification surface:
- Targeted build:
  `lake build Mettapedia.ProbabilityTheory.Moments Mettapedia.ProbabilityTheory.Exchangeability.CategoricalMixture Mettapedia.ProbabilityTheory.Exchangeability.DiaconisFreedmanFinite Mettapedia.ProbabilityTheory.Exchangeability Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti Mettapedia.ProbabilityTheory.HigherOrderProbability.CategoricalConnection Mettapedia.PLN.InferenceControl.PremiseSelection.LocalMixtureBridge Mettapedia.CategoryTheory.DeFinettiHausdorffBridge`
- Check no old `Mettapedia.Logic.{MomentSequences,HausdorffMoment,DiaconisFreedmanFinite,CategoricalMixture,CategoricalDeFinetti}`,
  corresponding old imports, or old file-path references remain outside this
  ledger.
- Check no `Mettapedia.Logic` namespace remains in the moved files.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted`; the broad triviality scan only hit a local
  `Set.univ` membership proof.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.53: PLN confidence bridges and PeTTa comparison analysis

Status: completed in the working tree.

Moved paths:
- `NuPLNEvidenceBridge.lean` moved from the logic attic to
  `Mettapedia/PLN/Evidence/NuEvidenceQuantaleBridge.lean`.
- `ConfidenceCompoundingTheorem.lean` moved from the logic attic to
  `Mettapedia/PLN/Evidence/ConfidenceCompoundingTheorem.lean`.
- `PeTTaLibPLNFormalAnalysis.lean` moved from the logic attic to
  `Mettapedia/PLN/Comparisons/PeTTa/PeTTaLibPLNFormalAnalysis.lean`.
- The `Mettapedia/PLN/Evidence.lean` hub imports the evidence bridge and
  confidence-compounding theorem.
- The new `Mettapedia/PLN/Comparisons/PeTTa.lean` hub imports the PeTTa
  comparison surface, and `Mettapedia/PLN/Comparisons.lean` imports that hub.

Namespace:
- The BinaryEvidence/MeTTa truth-value bridge now lives under
  `Mettapedia.PLN.Evidence.NuEvidenceQuantaleBridge`.
- The tensor/confidence-compounding theorems now live under
  `Mettapedia.PLN.Evidence.ConfidenceCompoundingTheorem`.
- The PeTTa `lib_pln.metta` comparison analysis now lives under
  `Mettapedia.PLN.Comparisons.PeTTa.PeTTaLibPLNFormalAnalysis`.

References repointed:
- WM-backed truth-value consumers now import and qualify the moved
  `NuEvidenceQuantaleBridge` module from `PLN/Evidence`.
- Unified probability consumers now import and open
  `PLN/Evidence/ConfidenceCompoundingTheorem`.
- The implementation parity checklist now imports and cites the moved PeTTa
  comparison surface.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the moved confidence/comparison modules.

Facade deletion:
- No compatibility module was left at the old paths.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Evidence.NuEvidenceQuantaleBridge Mettapedia.PLN.Evidence.ConfidenceCompoundingTheorem Mettapedia.PLN.Comparisons.PeTTa.PeTTaLibPLNFormalAnalysis Mettapedia.PLN.Comparisons.PeTTa Mettapedia.PLN.Evidence Mettapedia.PLN.Comparisons Mettapedia.PLN.TruthValues.WMPLNJustifiedTruthFunctions Mettapedia.ProbabilityTheory.UnifiedProbabilityBridge Mettapedia.Implementation.PLNParityChecklist`
- Check no old `Mettapedia.Logic.{NuPLNEvidenceBridge,NuEvidenceQuantaleBridge,ConfidenceCompoundingTheorem,PeTTaLibPLNFormalAnalysis}`,
  corresponding old imports, or old file-path references remain outside this
  ledger.
- Check no `Mettapedia.Logic` namespace remains in the moved files.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved files.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.54: ProbLog distribution-semantics PLN bridge

Status: completed in the working tree.

Moved paths:
- `ProbLogDistributionSemantics.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/Languages/ProbLog/DistributionSemantics.lean`.
- `ProbLogCompilation.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/Languages/ProbLog/Compilation.lean`.
- `ProbLogInfinite.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/Languages/ProbLog/Infinite.lean`.
- `ProbLogSpec.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/Languages/ProbLog/Spec.lean`.
- The new `Mettapedia/PLN/Bridges/Languages/ProbLog.lean` hub imports the
  moved ProbLog bridge modules, and `Mettapedia/PLN/Bridges/Languages.lean`
  imports that hub.

Namespace:
- Finite ProbLog distribution-semantics definitions now live under
  `Mettapedia.PLN.Bridges.Languages.ProbLog.DistributionSemantics`.
- ProbLog compilation and noisy-OR bridge definitions now live under
  `Mettapedia.PLN.Bridges.Languages.ProbLog.Compilation`.
- Infinite-product ProbLog distribution-semantics definitions now live under
  `Mettapedia.PLN.Bridges.Languages.ProbLog.Infinite`.
- The ProbLog specification surface now lives under
  `Mettapedia.PLN.Bridges.Languages.ProbLog.Spec`.

References repointed:
- BDD, LP grounding/stratification, and PLN example consumers now import the
  moved ProbLog bridge modules from `PLN/Bridges/Languages/ProbLog`.
- Old source-path prose references were repointed to the new bridge paths.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the moved ProbLog bridge modules.

Facade deletion:
- No compatibility module was left at the old paths.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Bridges.Languages.ProbLog.DistributionSemantics Mettapedia.PLN.Bridges.Languages.ProbLog.Compilation Mettapedia.PLN.Bridges.Languages.ProbLog.Infinite Mettapedia.PLN.Bridges.Languages.ProbLog.Spec Mettapedia.PLN.Bridges.Languages.ProbLog Mettapedia.PLN.Bridges.Languages Mettapedia.Logic.BDD.Compilation Mettapedia.Logic.BDD.ProbMeTTaBridge Mettapedia.Logic.BDD.WMPLNBridge Mettapedia.Examples.PLN.BioHypothesisGeneration Mettapedia.Examples.PLN.BioIncrementalHyperseed Mettapedia.Logic.LP.NormalGrounding Mettapedia.Logic.LP.Stratification`
- Check no old `Mettapedia.Logic.{ProbLogDistributionSemantics,ProbLogCompilation,ProbLogInfinite,ProbLogSpec}`,
  corresponding old imports, or old file-path references remain outside this
  ledger.
- Check no `Mettapedia.Logic.ProbLog` namespace or import remains in the
  moved files.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved files.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.55: OSLF image-finiteness framework wrappers

Status: completed in the working tree.

Moved paths:
- `OSLFImageFinite.lean` moved from the logic attic to
  `Mettapedia/OSLF/Framework/ImageFinite.lean`.

Namespace:
- Image-finiteness and Hennessy-Milner wrapper theorems for OSLF `LanguageDef`
  reductions now live under `Mettapedia.OSLF.Framework.ImageFinite`.

References repointed:
- OSLF core, spec-index, predecessor-finiteness, and π→ρ canonical bridge
  consumers now import and qualify the moved framework module.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the moved image-finiteness module.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.OSLF.Framework.ImageFinite Mettapedia.OSLF.Framework.PredFiniteSufficient Mettapedia.OSLF.Framework.PiRhoCanonicalBridge Mettapedia.OSLF.CoreMain Mettapedia.OSLF.SpecIndex`
- Check no old `Mettapedia.Logic.OSLFImageFinite`, corresponding old import,
  or old file-path reference remains outside this ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved file.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.56: OSLF Foundation Kripke bridge

Status: completed in the working tree.

Moved paths:
- `OSLFKripkeBridge.lean` moved from the logic attic to
  `Mettapedia/OSLF/Bridges/Foundation/Kripke.lean`.
- New bridge hubs `Mettapedia/OSLF/Bridges.lean` and
  `Mettapedia/OSLF/Bridges/Foundation.lean` expose the bridge room.

Namespace:
- The OSLF-to-Foundation Kripke correspondence, frame construction, and modal
  frame-condition bridge theorems now live under
  `Mettapedia.OSLF.Bridges.Foundation.Kripke`.

References repointed:
- OSLF main/core hubs and the π→ρ canonical bridge now import and qualify the
  moved bridge module from `Mettapedia.OSLF.Bridges.Foundation.Kripke`.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the moved OSLF Kripke bridge module.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.OSLF.Bridges.Foundation.Kripke Mettapedia.OSLF.Bridges.Foundation Mettapedia.OSLF.Bridges Mettapedia.OSLF.Framework.PiRhoCanonicalBridge Mettapedia.OSLF.CoreMain Mettapedia.OSLF.Main Mettapedia.OSLF`
- Check no old `Mettapedia.Logic.OSLFKripkeBridge`, corresponding old import,
  or old file-path reference remains outside this ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved bridge file.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.57: OSLF CategoryTheory open-map bridge

Status: completed in the working tree.

Moved paths:
- `OSLFOpenMapBridge.lean` moved from the logic attic to
  `Mettapedia/OSLF/Bridges/CategoryTheory/OpenMap.lean`.
- New hub `Mettapedia/OSLF/Bridges/CategoryTheory.lean` exposes the
  category-theory bridge room, and `Mettapedia/OSLF/Bridges.lean` imports it.

Namespace:
- The OSLF generalized-open-map instantiation, path-bisimulation bridge, and
  full-open-witness distinction-graph compatibility theorems now live under
  `Mettapedia.OSLF.Bridges.CategoryTheory.OpenMap`.

References repointed:
- The mixed open-map regression surface now imports and opens the moved OSLF
  bridge module from `Mettapedia.OSLF.Bridges.CategoryTheory.OpenMap`.
- Logic and CategoryTheory README references to the old OSLF open-map bridge
  path now cite the new OSLF bridge path.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the moved OSLF open-map bridge module.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.OSLF.Bridges.CategoryTheory.OpenMap Mettapedia.OSLF.Bridges.CategoryTheory Mettapedia.OSLF.Bridges Mettapedia.Logic.OpenMapBridgeRegression Mettapedia.OSLF`
- Check no old `Mettapedia.Logic.OSLFOpenMapBridge`, corresponding old import,
  or old file-path reference remains outside this ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved bridge file.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.58: categorical νPLN probability bridge

Status: completed in the working tree.

Moved paths:
- `CategoricalNuPLNBridge.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/ProbabilityTheory/CategoricalNuPLNBridge.lean`.

Namespace:
- The categorical finite-mixture to νPLN evidence compatibility bridge now
  lives under
  `Mettapedia.PLN.Bridges.ProbabilityTheory.CategoricalNuPLNBridge`.

References repointed:
- `Mettapedia/CategoryTheory/DeFinettiExports.lean` now imports and qualifies
  the bridge through the PLN/ProbabilityTheory bridge namespace.
- `Mettapedia/PLN/Bridges/ProbabilityTheory.lean` now exports the bridge.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the moved categorical νPLN bridge module.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Bridges.ProbabilityTheory.CategoricalNuPLNBridge Mettapedia.PLN.Bridges.ProbabilityTheory Mettapedia.CategoryTheory.DeFinettiExports`
- Check no old `Mettapedia.Logic.CategoricalNuPLNBridge`, corresponding old
  import, or old file-path reference remains outside this ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved bridge file.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.59: terminal measure-valued PLN world model

Status: completed in the working tree.

Moved paths:
- `TerminalMeasureWorldModel.lean` moved from the logic attic to
  `Mettapedia/PLN/WorldModel/TerminalMeasureWorldModel.lean`.

Namespace:
- The finite/countable evidence-to-measure world-model construction now lives
  under `Mettapedia.PLN.WorldModel.TerminalMeasureWorldModel`.

References repointed:
- `Mettapedia/PLN/Evidence/KSEvidenceMeasureBridge.lean` now imports the
  terminal measure world-model construction from the PLN world-model room.
- `Mettapedia/PLN/WorldModel.lean` now exports the module.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the moved terminal measure world-model module.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.WorldModel.TerminalMeasureWorldModel Mettapedia.PLN.WorldModel Mettapedia.PLN.Evidence.KSEvidenceMeasureBridge`
- Check no old `Mettapedia.Logic.TerminalMeasureWorldModel`, corresponding old
  import, or old file-path reference remains outside this ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved world-model file.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.60: PLN world-model hypercube classification

Status: completed in the working tree.

Moved paths:
- `WMHypercubeClassification.lean` moved from the logic attic to
  `Mettapedia/PLN/WorldModel/WMHypercubeClassification.lean`.

Namespace:
- The KS-hypercube classification of PLN world-model regimes now lives under
  `Mettapedia.PLN.WorldModel.WMHypercubeClassification`.

References repointed:
- `Mettapedia/Logic/GSLTWeightMapBridge.lean` and
  `Mettapedia/Logic/ModalProbabilityBridge.lean` now import/open the moved
  PLN world-model classifier.
- `Mettapedia/Examples/PLN/ProofSystemShowcase.lean` now checks the moved
  classifier through the PLN world-model namespace.
- `Mettapedia/PLN/WorldModel.lean` now exports the module.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the moved world-model hypercube classifier.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.WorldModel.WMHypercubeClassification Mettapedia.PLN.WorldModel Mettapedia.Logic.GSLTWeightMapBridge Mettapedia.Logic.ModalProbabilityBridge Mettapedia.Examples.PLN.ProofSystemShowcase`
- Check no old `Mettapedia.Logic.WMHypercubeClassification`, corresponding
  old import, or old file-path reference remains outside this ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved world-model classifier file.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.61: PLN modal-probability hypercube bridge

Status: completed in the working tree.

Moved paths:
- `ModalProbabilityBridge.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/ProbabilityTheory/ModalProbabilityBridge.lean`.

Namespace:
- The bridge from PLN world-model regimes to probability-hypercube vertices
  now lives under
  `Mettapedia.PLN.Bridges.ProbabilityTheory.ModalProbabilityBridge`.

References repointed:
- `Mettapedia/Examples/PLN/ProofSystemShowcase.lean` now imports/checks the
  modal-probability bridge through the PLN/ProbabilityTheory bridge namespace.
- `Mettapedia/PLN/Bridges/ProbabilityTheory.lean` now exports the bridge.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the moved modal-probability bridge module.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Bridges.ProbabilityTheory.ModalProbabilityBridge Mettapedia.PLN.Bridges.ProbabilityTheory Mettapedia.Examples.PLN.ProofSystemShowcase`
- Check no old `Mettapedia.Logic.ModalProbabilityBridge`, corresponding old
  import, or old file-path reference remains outside this ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved modal-probability bridge file.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.
- Full build after the move:
  `lake build Mettapedia`
  completed successfully (9939 jobs).

## Cluster 6c.62: temporal quantale algebra

Status: completed in the working tree.

Moved paths:
- `TemporalQuantale.lean` moved from the logic attic to
  `Mettapedia/Algebra/TemporalQuantale.lean`.

Namespace:
- No `Mettapedia.Logic.TemporalQuantale` declaration namespace existed in the
  source file; the definitions were already in the global `TemporalQuantale`
  namespace/class.  The migration therefore changes the module path only, not
  theorem statements or declaration names.

References repointed:
- `Mettapedia/Logic/ModalQuantaleSemantics.lean` now imports the algebraic
  temporal-quantale module through `Mettapedia.Algebra.TemporalQuantale`.
- `Mettapedia.lean` now imports the temporal-quantale module in the Algebra
  section and no longer imports it from `Mettapedia.Logic`.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the moved temporal-quantale module.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.Algebra.TemporalQuantale Mettapedia.Logic.ModalQuantaleSemantics`
- Check no old `Mettapedia.Logic.TemporalQuantale`, corresponding old import,
  or old file-path reference remains outside this ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved temporal-quantale file.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint:
  `TemporalQuantale.shift_residuate`,
  `TemporalQuantale.temporal_transitivity`,
  `TemporalQuantale.temporal_modus_ponens`,
  `TemporalQuantale.shift_predImpl`, and
  `TemporalQuantale.shift_injective`.
- Full build after the move:
  `lake build Mettapedia`
  completed successfully (9939 jobs).

## Cluster 6c.63: PLN/NARS semantics decision tree

Status: completed in the working tree.

Moved paths:
- `SemanticsDecisionTree.lean` moved from the logic attic to
  `Mettapedia/PLN/Comparisons/NARS/SemanticsDecisionTree.lean`.

Namespace:
- The decision-tree module now lives under
  `Mettapedia.PLN.Comparisons.NARS.SemanticsDecisionTree`.

References repointed:
- `Mettapedia/PLN/Core/PLNCore.lean` now imports the decision tree through
  the PLN/NARS comparison namespace.
- `Mettapedia/PLN/Comparisons/NARS.lean` now exports the decision tree.
- The DocText compositional source and generated GF runtime claim now cite the
  new path.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the moved semantics decision-tree module.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Comparisons.NARS.SemanticsDecisionTree Mettapedia.PLN.Comparisons.NARS Mettapedia.PLN.Core.PLNCore Mettapedia.DocText.LogicReadmeCompositional`
- Check no old `Mettapedia.Logic.SemanticsDecisionTree`, corresponding old
  import, or old file-path reference remains outside this ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved semantics decision-tree file.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint:
  `gate_example_knuthSkilling`,
  `gate_example_dempsterShafer`,
  `evidence_blocks_faithful_scalarization`,
  `ks_has_standard_inference`,
  `weaker_than_ks_interval_quantale`,
  `weaker_than_ks_interval_inference`, and
  `nars_revision_has_clamps`.
- Full build after the move:
  `lake build Mettapedia`
  completed successfully (9939 jobs).

## Cluster 6c.64: PLN/GSLT weight-map bridge

Status: completed in the working tree.

Moved paths:
- `GSLTWeightMapBridge.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/GSLT/WeightMapBridge.lean`.
- `Mettapedia/PLN/Bridges/GSLT.lean` was added as the bridge-room
  aggregator.

Namespace:
- The bridge from GSLT-style weight maps to PLN world-model extraction now
  lives under `Mettapedia.PLN.Bridges.GSLT.WeightMapBridge`.

References repointed:
- `Mettapedia/Examples/PLN/ProofSystemShowcase.lean` now imports/checks the
  bridge through the PLN/GSLT bridge namespace and uses the shortened active
  leaf label `GSLT/WeightMapBridge`.
- `Mettapedia/PLN/Bridges.lean` now exports the GSLT bridge room.
- The related modal-probability bridge comment now names the new namespace.
- No old import path, qualified namespace, active source label, or old source
  path remains outside this ledger for the moved GSLT weight-map bridge.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Bridges.GSLT.WeightMapBridge Mettapedia.PLN.Bridges.GSLT Mettapedia.PLN.Bridges Mettapedia.Examples.PLN.ProofSystemShowcase Mettapedia.PLN.Bridges.ProbabilityTheory.ModalProbabilityBridge`
- Check no old `Mettapedia.Logic.GSLTWeightMapBridge`, corresponding old
  import, active old label, or old file-path reference remains outside this
  ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved GSLT bridge file.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint:
  `weight_satisfies_extract_add`,
  `weight_satisfies_extract_zero`,
  `additive_strongest`,
  `trustgated_weakest_nonadd`, and
  `full_picture_summary`.
- Full build after the move:
  `lake build Mettapedia`
  completed successfully (9939 jobs).

## Cluster 6c.65: HardBEST quantitative-checker adapter

Status: completed in the working tree.

Moved paths:
- `HardBESTQuantitativeAdapter.lean` moved from the logic attic to
  `Mettapedia/Algorithms/HardBESTQuantitativeAdapter.lean`.

Namespace:
- The certified quantitative-checker transport adapter now lives under
  `Mettapedia.Algorithms.HardBEST`.

References repointed:
- No external imports or qualified references used the old module/namespace.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the moved HardBEST quantitative adapter.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.Algorithms.HardBESTQuantitativeAdapter`
- Check no old `Mettapedia.Logic.HardBEST`, corresponding old import, or old
  file-path reference remains outside this ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved HardBEST quantitative adapter file.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint:
  `sum_abs_wr_wor_patternMass_toReal_le_of_surrogate`,
  `hq_wor_of_certificate`,
  `sum_abs_wr_wor_patternMass_toReal_le_of_surrogate_certified`,
  `sum_abs_wr_wor_patternMass_toReal_le_of_surrogate_certified_family`,
  `wr_wor_patternRate_of_certified_surrogate`,
  `largeR_wr_wor_patternRate_of_canonicalWRSurrogate_largeR_certified`,
  `demo_real_obligation_discharged`,
  `demo_guard_checker_false`, and
  `demo_guard_rejects_bad_rate_claim`.
- Full build after the move:
  `lake build Mettapedia`
  completed successfully (9939 jobs).

## Cluster 6c.66: PLN evidential ledger

Status: completed in the working tree.

Moved paths:
- `EvidentialLedger.lean` moved from the logic attic to
  `Mettapedia/PLN/Evidence/EvidentialLedger.lean`.

Namespace:
- The multi-source evidence aggregation and additive-world-model embedding
  framework now lives under `Mettapedia.PLN.Evidence.EvidentialLedger`.

References repointed:
- PLN worked examples now import/open the ledger through
  `Mettapedia.PLN.Evidence.EvidentialLedger`.
- `Mettapedia/PLN/WorldModel/WMCalculusSoundness.lean` and the runtime
  soundness bridge now import the ledger from the PLN evidence room.
- GF/SUMO evidence modules no longer open the old logic namespace for ledger
  definitions.
- `Mettapedia/PLN/Evidence.lean` now exports the evidential-ledger module.
- No old import path, qualified namespace, broad ledger-era logic open, or old
  source path remains outside this ledger for the moved evidential ledger.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Evidence.EvidentialLedger Mettapedia.PLN.Evidence Mettapedia.Examples.PLN.GJPForecastDemo Mettapedia.Examples.PLN.AIOutcomesDemo Mettapedia.Examples.PLN.WMUWCSEGateDemo Mettapedia.PLN.WorldModel.WMCalculusSoundness Mettapedia.Logic.RuntimeSoundnessBridge Mettapedia.Languages.GF.SUMO.EvidenceModel Mettapedia.Languages.GF.SUMO.PainEvidenceWM`
- Check no old `Mettapedia.Logic.EvidentialLedger`, corresponding old import,
  broad stale ledger-era `open Mettapedia.Logic`, or old file-path reference
  remains outside this ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved evidential-ledger file.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint:
  `toState_append`,
  `weightedToState_append`,
  `compress_append`, and
  `DataBackedState.revise_compressed`.
- Full build after the move:
  `lake build Mettapedia`
  completed successfully (9939 jobs).

## Cluster 6c.67: PLN language-runtime soundness bridge

Status: completed in the working tree.

Moved paths:
- `RuntimeSoundnessBridge.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/Languages/RuntimeSoundnessBridge.lean`.

Namespace:
- The runtime-certification bridge for PLN evidence/world-model algebra now
  lives under `Mettapedia.PLN.Bridges.Languages.RuntimeSoundnessBridge`.

References repointed:
- `Mettapedia/PLN/Bridges/Languages.lean` now exports the runtime-soundness
  bridge.
- No active external imports or qualified references used the old module.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the moved runtime-soundness bridge.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Bridges.Languages.RuntimeSoundnessBridge Mettapedia.PLN.Bridges.Languages`
- Check no old `Mettapedia.Logic.RuntimeSoundnessBridge`, corresponding old
  import, or old file-path reference remains outside this ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved runtime-soundness bridge file.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint:
  `sound_runtime_extract_add`,
  `sound_runtime_sequential`,
  `sound_runtime_revise_zero_left`, and
  `soundness_guarantees`.
- Full build after the move:
  `lake build Mettapedia`
  completed successfully (9939 jobs).

## Cluster 6c.68: HOL-to-PLN worked example ladder

Status: completed in the working tree.

Moved paths:
- `HOLExampleLadder.lean` moved from the logic attic to
  `Mettapedia/Examples/PLN/HOLExampleLadder.lean`.
- `HOLProbPLNExampleDemo.lean` moved from the logic attic to
  `Mettapedia/Examples/PLN/HOLProbPLNExampleDemo.lean`.

Namespace:
- The example ladder now lives under
  `Mettapedia.Examples.PLN.HOLExampleLadder`.
- The packaged HOL-to-world-model-to-probabilistic-to-planner demo now lives
  under `Mettapedia.Examples.PLN.HOLProbPLNExampleDemo`.

References repointed:
- The packaged demo imports the ladder through the Examples/PLN room.
- `Mettapedia/Examples/PLN.lean` now exports both moved example modules.
- Planner-shadow theorem references in the moved examples now point at their
  current PLN rule-family namespace rather than the old logic-attic namespace.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the moved HOL/PLN example pair.

Facade deletion:
- No compatibility module was left at either old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.Examples.PLN.HOLExampleLadder Mettapedia.Examples.PLN.HOLProbPLNExampleDemo Mettapedia.Examples.PLN`
- Check no old `Mettapedia.Logic.HOLExampleLadder`,
  `Mettapedia.Logic.HOLProbPLNExampleDemo`, stale
  `Mettapedia.Logic.benchmarkPlannerShadow*`, corresponding old imports, or
  old file-path references remain outside this ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved HOL/PLN example files.
- Spot-check moved example alias axiom footprints remain within the accepted
  project footprint:
  `closedTheoremSoundnessExample`,
  `worldModelSingletonConsequenceExample`,
  `benchmarkBeliefTracksHierarchicalProbExample`,
  `plannerShadowTracksHierarchicalProbExample`,
  `plannerShadowNotGlobalOracleExample`,
  `wmConsequenceSchemaRung`,
  `plannerCarriedValueRung`,
  `plannerTrackingRung`, and
  `plannerNotGlobalOracleRung`.
- Full build after the move:
  `lake build Mettapedia`
  completed successfully (9968 jobs).

## Cluster 6c.69: OSLF evidence semantics and distinction-graph framework

Status: completed in the working tree.

Moved paths:
- `OSLFEvidenceSemantics.lean` moved from the logic attic to
  `Mettapedia/OSLF/Framework/EvidenceSemantics.lean`.
- `OSLFKSUnificationSketch.lean` moved from the logic attic to
  `Mettapedia/OSLF/Framework/KSUnificationSketch.lean`.
- `OSLFDistinctionGraph.lean` moved from the logic attic to
  `Mettapedia/OSLF/Framework/DistinctionGraph.lean`.
- `OSLFDistinctionGraphWeighted.lean` moved from the logic attic to
  `Mettapedia/OSLF/Framework/DistinctionGraph/Weighted.lean`.
- `OSLFDistinctionGraphWM.lean` moved from the logic attic to
  `Mettapedia/OSLF/Framework/DistinctionGraph/WorldModel.lean`.
- `OSLFDistinctionGraphEntropy.lean` moved from the logic attic to
  `Mettapedia/OSLF/Framework/DistinctionGraph/Entropy.lean`.

Namespace:
- OSLF evidence semantics definitions now live under
  `Mettapedia.OSLF.Framework.EvidenceSemantics`.
- K&S unification sketch definitions now live under
  `Mettapedia.OSLF.Framework.KSUnificationSketch`.
- Distinction-graph definitions now live under
  `Mettapedia.OSLF.Framework.DistinctionGraph` and its
  `Weighted`, `WorldModel`, and `Entropy` subnamespaces.

References repointed:
- `Mettapedia/OSLF/Main.lean` and `Mettapedia/OSLF/CoreMain.lean` now import
  the moved framework modules through their OSLF room paths.
- OSLF quantified-formula consumers now import and open the moved distinction
  graph modules through `Mettapedia.OSLF.Framework`.
- Paper and local project-status references for the moved OSLF module paths
  were repointed away from the old logic attic.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the moved OSLF evidence/distinction-graph cluster.

Facade deletion:
- No compatibility module was left at any old OSLF evidence or
  distinction-graph path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.OSLF.Framework.EvidenceSemantics Mettapedia.OSLF.Framework.KSUnificationSketch Mettapedia.OSLF.Framework.DistinctionGraph Mettapedia.OSLF.Framework.DistinctionGraph.Weighted Mettapedia.OSLF.Framework.DistinctionGraph.WorldModel Mettapedia.OSLF.Framework.DistinctionGraph.Entropy Mettapedia.OSLF.Main Mettapedia.OSLF.CoreMain Mettapedia.OSLF.QuantifiedFormula Mettapedia.OSLF.QuantifiedFormula2`
- Check no old `Mettapedia.Logic.OSLFEvidenceSemantics`,
  `Mettapedia.Logic.OSLFKSUnificationSketch`,
  `Mettapedia.Logic.OSLFDistinctionGraph`,
  `Mettapedia.Logic.OSLFDistinctionGraphWeighted`,
  `Mettapedia.Logic.OSLFDistinctionGraphWM`,
  `Mettapedia.Logic.OSLFDistinctionGraphEntropy`, corresponding old imports, or
  old file-path references remain outside this ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved OSLF files; old scanner-noisy prose was
  tightened to avoid false positives.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint:
  `semE_imp_mp`,
  `threshold_dia_fails`,
  `bisimulation_invariant_sem`,
  `hm_converse_schema`,
  `indistObs_equivalence`,
  `indist_iff_fullBisim_imageFinite`,
  `indistWeightE_self_top`,
  `gate_theorem`,
  `wmAtomSem_revision`,
  `oslf_ks_wm_graph_unification`, and
  `graphtropy_crispWeight_eq_repeatProb`.
- Full build after the move:
  `lake build Mettapedia`
  completed successfully (9968 jobs).

## Cluster 6c.70: weighted generalized-open-map bridge and OSLF regression

Status: completed in the working tree.

Moved paths:
- `WeightedOpenMaps.lean` moved from the logic attic to
  `Mettapedia/CategoryTheory/GeneralizedOpenMaps/Weighted.lean`.
- `OpenMapBridgeRegression.lean` moved from the logic attic to
  `Mettapedia/OSLF/Bridges/CategoryTheory/OpenMapRegression.lean`.

Namespace:
- Weighted/probabilistic generalized-open-map definitions now live under
  `Mettapedia.CategoryTheory.GeneralizedOpenMaps.Weighted`.
- The OSLF/category-theory open-map regression checks now live under
  `Mettapedia.OSLF.Bridges.CategoryTheory.OpenMapRegression`.

References repointed:
- The root `Mettapedia.lean` aggregator now imports the moved weighted
  generalized-open-map bridge and OSLF regression through their new rooms.
- `Mettapedia/OSLF/Bridges/CategoryTheory.lean` now exports the moved
  regression through the OSLF bridge hub.
- CategoryTheory and Logic README references were repointed away from the old
  logic-attic file paths.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the moved weighted/open-map regression cluster.

Facade deletion:
- No compatibility module was left at either old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.CategoryTheory.GeneralizedOpenMaps.Weighted Mettapedia.OSLF.Bridges.CategoryTheory.OpenMapRegression Mettapedia.OSLF.Bridges.CategoryTheory Mettapedia.OSLF.Bridges`
- Check no old `Mettapedia.Logic.WeightedOpenMaps`,
  `Mettapedia.Logic.OpenMapBridgeRegression`, corresponding old imports, or old
  file-path references remain outside this ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved weighted/open-map regression files.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint:
  `weightedBisim_iff_gopen_span`,
  `weighted_equiv_regression`,
  `pathBisim_to_bisimilar_regression`,
  `fullOpenWitness_obsEq_regression`, and
  `fullOpenWitness_not_distinguished_regression`.
- Full build after the move:
  `lake build Mettapedia`
  completed successfully (9968 jobs).

## Cluster 6c.71: PLN/KR concept-closure fixpoint bridges

Status: completed in the working tree.

Moved paths:
- `FormedConceptFixpointClosureBridge.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/KR/ConceptClosure/FormedConceptFixpointClosureBridge.lean`.
- `CredalConceptFixpointClosureBridge.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/KR/ConceptClosure/CredalConceptFixpointClosureBridge.lean`.
- `CredalConceptFullInheritanceClosureBridge.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/KR/ConceptClosure/CredalConceptFullInheritanceClosureBridge.lean`.

Namespace:
- The formed-concept fixpoint bridge now lives under
  `Mettapedia.PLN.Bridges.KR.ConceptClosure.FormedConceptFixpointClosureBridge`.
- The credal concept fixpoint bridge now lives under
  `Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFixpointClosureBridge`.
- The credal full-inheritance closure bridge now lives under
  `Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge`.

References repointed:
- New bridge hubs were added at `Mettapedia/PLN/Bridges/KR.lean` and
  `Mettapedia/PLN/Bridges/KR/ConceptClosure.lean`, and the existing PLN bridge
  hub imports the KR bridge hub.
- The root `Mettapedia.lean` aggregator imports the PLN/KR bridge hub so the
  moved modules remain part of the top-level build surface.
- `Mettapedia/PLN/Core/PLNCanonicalAPI.lean` imports and `_root_` aliases now
  point at the moved modules.
- The still-deferred ontology-growth bridges in `Logic/` import the moved
  concept-closure bridge modules and open the new concept-closure namespace.
- ZarWiki WM-PLN references to the old formed-concept fixpoint bridge path were
  repointed to the new PLN/KR bridge path.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the three moved concept-closure bridge files.

Facade deletion:
- No compatibility module was left at any old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Bridges.KR.ConceptClosure Mettapedia.PLN.Bridges.KR Mettapedia.PLN.Bridges Mettapedia.Logic.FormedConceptOntologyGrowthBridge Mettapedia.Logic.CredalConceptOntologyGrowthBridge Mettapedia.PLN.Core.PLNCanonicalAPI`
- Check no old `Mettapedia.Logic.FormedConceptFixpointClosureBridge`,
  `Mettapedia.Logic.CredalConceptFixpointClosureBridge`,
  `Mettapedia.Logic.CredalConceptFullInheritanceClosureBridge`,
  corresponding old imports, or old file-path references remain outside this
  ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved concept-closure bridge files.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint:
  `mem_formedConceptQuerySet_iff`,
  `leastRuleClosure_thresholdValid_of_exactTableStrength`,
  `availableRegionAt_subset_wmAdmissibleRegionAt_of_exactTableStrength`,
  `wmAdmissibleRegionAt_eq_availableRegionAt_of_exactTableStrength`,
  `mem_lowerFormedConceptQuerySet_iff`, and
  `leastRuleClosure_thresholdValid_of_exactFullInheritanceStrength`.
- Full build after the move:
  `lake build Mettapedia`
  completed successfully (9974 jobs).

## Cluster 6c.72: Boolean-to-Heyting PLN evidence bridge

Status: completed in the working tree.

Moved path:
- `BooleanHeytingBridge.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/Logic/BooleanHeytingBridge.lean`.

Namespace:
- The Boolean-event / Heyting-evidence bridge now lives under
  `Mettapedia.PLN.Bridges.Logic.BooleanHeytingBridge`.

References repointed:
- `Mettapedia/PLN/Bridges/Logic.lean` now exports the moved bridge through the
  PLN logic-bridge hub.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the moved Boolean-to-Heyting bridge.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Bridges.Logic.BooleanHeytingBridge Mettapedia.PLN.Bridges.Logic Mettapedia.PLN.Bridges`
- Check no old `Mettapedia.Logic.BooleanHeytingBridge`, corresponding old
  import, or old file-path reference remains outside this ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved Boolean-to-Heyting bridge file.
- The local `push_neg` deprecation warning in the moved file was removed during
  the migration.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint:
  `counts_incomparable`,
  `counts_not_total`,
  `countsOfList_eq_countsOfList'`, and
  `countsOfList_permutation`.

## Cluster 6c.73: PLN evidence convergence

Status: completed in the working tree.

Moved paths:
- `Convergence/ConfidenceConvergence.lean` moved from the logic attic to
  `Mettapedia/PLN/Evidence/Convergence/ConfidenceConvergence.lean`.
- `Convergence/IIDBernoulli.lean` moved from the logic attic to
  `Mettapedia/PLN/Evidence/Convergence/IIDBernoulli.lean`.
- `Convergence/LawOfLargeNumbers.lean` moved from the logic attic to
  `Mettapedia/PLN/Evidence/Convergence/LawOfLargeNumbers.lean`.
- `Convergence/RateOfConvergence.lean` moved from the logic attic to
  `Mettapedia/PLN/Evidence/Convergence/RateOfConvergence.lean`.

Namespace:
- PLN confidence, Bernoulli-evidence, law-of-large-numbers, and rate
  theorems now live under `Mettapedia.PLN.Evidence.Convergence`.

References repointed:
- A new hub `Mettapedia/PLN/Evidence/Convergence.lean` imports the moved
  convergence modules.
- `Mettapedia/PLN/Evidence.lean` imports the convergence hub.
- `Mettapedia/Logic/Comparison/OptimalityTheorems.lean` imports and opens the
  moved convergence namespace.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the moved convergence cluster.

Facade deletion:
- No compatibility module was left at any old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Evidence.Convergence Mettapedia.PLN.Evidence Mettapedia.Logic.Comparison.OptimalityTheorems`
- Check no old `Mettapedia.Logic.Convergence`, corresponding old import, or
  old file-path reference remains outside this ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved convergence files.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint:
  `confidence_tendsto_one`,
  `confidence_gap_rate`,
  `observationsToEvidence_strength`, and
  `pln_eventually_accurate`.

## Cluster 6c.74: PLN comparison and optimality surfaces

Status: completed in the working tree.

Moved paths:
- `Comparison/ErrorCharacterization.lean` moved from the logic attic to
  `Mettapedia/PLN/Comparisons/ErrorCharacterization.lean`.
- `Comparison/OptimalityTheorems.lean` moved from the logic attic to
  `Mettapedia/PLN/Comparisons/OptimalityTheorems.lean`.
- `Comparison/StructuralAdvantages.lean` moved from the logic attic to
  `Mettapedia/PLN/Comparisons/StructuralAdvantages.lean`.

Namespace:
- PLN approximation-error theorems now live under
  `Mettapedia.PLN.Comparisons.ErrorCharacterization`.
- PLN optimality and structural-comparison theorems now live under
  `Mettapedia.PLN.Comparisons`.

References repointed:
- `Mettapedia/PLN/Comparisons.lean` imports the three moved comparison modules.
- `Mettapedia/PLN/Core/SoundnessCompleteness.lean` imports the moved structural
  advantages module.
- `Mettapedia/PLN/RuleFamilies/HigherOrder/PLNProbGuardedAdmissibility.lean`
  imports the moved error-characterization module.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the moved comparison cluster.

Facade deletion:
- No compatibility module was left at any old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Comparisons.ErrorCharacterization Mettapedia.PLN.Comparisons.OptimalityTheorems Mettapedia.PLN.Comparisons.StructuralAdvantages Mettapedia.PLN.Comparisons Mettapedia.PLN.Core.SoundnessCompleteness Mettapedia.PLN.RuleFamilies.HigherOrder.PLNProbGuardedAdmissibility`
- Check no old `Mettapedia.Logic.Comparison`, corresponding old import, or old
  file-path reference remains outside this ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved comparison files.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint:
  `independent_implies_exact`,
  `cmi_zero_implies_exact`,
  `exact_regime_bounded`,
  `pln_bayes_optimal_for_binary_evidence`,
  `pln_revision_definetti_family_true_lower_envelope_greatest_scalar_lower_bound`,
  `pln_represents_contradiction`, and
  `pln_advantages_summary`.

## Cluster 6c.75: PLN Kyburg probability bridge

Status: completed in the working tree.

Moved path:
- `HigherOrder/PLNKyburgReduction.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/ProbabilityTheory/PLNKyburgReduction.lean`.

Namespace:
- The distributional/Kyburg PLN reduction bridge now lives under
  `Mettapedia.PLN.Bridges.ProbabilityTheory.PLNKyburgReduction`.

References repointed:
- `Mettapedia/PLN/Bridges/ProbabilityTheory.lean` imports the moved bridge.
- `Mettapedia/PLN/Core/PLNCore.lean` and
  `Mettapedia/PLN/Core/PLNCanonicalAPI.lean` import and alias the moved bridge.
- `Mettapedia/PLN/TruthValues/PLNIndefiniteTruth.lean` keeps its inactive
  TODO import comment pointed at the new bridge path.
- Probability-theory higher-order README/comment references and the WM-PLN
  ZarWiki status references were repointed to the new PLN/probability bridge
  path.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the moved Kyburg bridge.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Bridges.ProbabilityTheory.PLNKyburgReduction Mettapedia.PLN.Bridges.ProbabilityTheory Mettapedia.PLN.Core.PLNCore Mettapedia.PLN.Core.PLNCanonicalAPI`
- Check no old `Mettapedia.Logic.HigherOrder.PLNKyburgReduction`,
  `Mettapedia.Logic.PLNKyburgReduction`, corresponding old import, or old
  file-path reference remains outside this ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved Kyburg bridge file.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint:
  `strengthWith_eq_beta_posterior_meanENN`,
  `evidence_encodes_beta_parameters`,
  `chapter7_worked_example_strength_uniform_3_1`, and
  `chapter7_distributional_kyburg_bridge_available`.

## Cluster 6c.76: Higher-order-to-PLN inference-rule bridge

Status: completed in the working tree.

Moved path:
- `HigherOrder/InferenceRuleBridge.lean` moved from the logic attic to
  `Mettapedia/PLN/Bridges/Logic/HigherOrderInferenceRuleBridge.lean`.

Namespace:
- The PLN-facing bridge from the generic higher-order reduction substrate to
  existing PLN inference rules now lives under
  `Mettapedia.PLN.Bridges.Logic.HigherOrderInferenceRuleBridge`.
- At this bridge-only cluster, the generic higher-order reduction substrate
  still remained under `Mettapedia.Logic.HigherOrder`; Cluster 6c.79 later
  relocates that substrate itself into the PLN higher-order rule-family room.

References repointed:
- `Mettapedia/Logic/HigherOrder.lean` no longer imports the PLN-facing bridge;
  it now documents that PLN-facing bridges live under `Mettapedia.PLN.Bridges.Logic`.
- `Mettapedia/PLN/Bridges/Logic.lean` imports the moved higher-order bridge.
- `Mettapedia/Logic/HigherOrder/HigherOrderReduction.lean` now imports
  `Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PBit` directly and names
  `PBit.isTrue` through its real namespace in local proof scripts. This removes
  a hidden transitive dependency that the migration exposed.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the moved higher-order inference-rule bridge.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Bridges.Logic.HigherOrderInferenceRuleBridge Mettapedia.PLN.Bridges.Logic Mettapedia.Logic.HigherOrder`
- Check no old `Mettapedia.Logic.HigherOrder.InferenceRuleBridge`,
  corresponding old import, or old file-path reference remains outside this
  ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved higher-order bridge file.
- Spot-check theorem axiom footprints remain within the accepted project
  footprint:
  `member_is_pred`,
  `inheritance_uses_conditional_prob_structure`,
  `ch10_context_hyp_fixture_mismatch_not_sound`, and
  `forAll_himp_not_equal_inheritance_ratio_unconditional`.

## Cluster 6c.77: Checker-reflection facade deletion

Status: completed in the working tree.

Removed facade:
- `Bridges/CheckerReflection.lean` was a one-line compatibility import from the
  logic attic to `Mettapedia.Algorithms.CheckerReflection`; it contained no
  declarations.

References repointed:
- `Mettapedia/Algorithms/FortiniFiniteCheckers.lean` now imports
  `Mettapedia.Algorithms.CheckerReflection` directly.
- The same consumer also opens
  `Mettapedia.ProbabilityTheory.Exchangeability.MarkovDeFinettiHard` so the
  existing Fortini prefix-carrier definitions from its direct import are in
  scope without relying on the removed compatibility surface.
- No old import path or old source path remains outside this ledger for the
  checker-reflection facade.

Facade deletion:
- The compatibility module was deleted; no replacement facade was left behind.

Verification surface:
- Targeted build:
  `lake build Mettapedia.Algorithms.FortiniFiniteCheckers Mettapedia.Algorithms.CheckerReflection`
- Check no old `Mettapedia.Logic.Bridges.CheckerReflection`, corresponding old
  import, or old file-path reference remains outside this ledger.
- Check no migration facade marker remains.
- No `#print axioms` spot-check is applicable because the deleted facade had no
  declarations and the consumer change is an import-only repoint.

## Cluster 6c.78: Retired Datalog facade deletion

Status: completed in the working tree.

Removed facade:
- `Datalog.lean` was a retired one-line import wrapper around
  `Mettapedia.Logic.LP`; it contained no declarations. The live
  logic-programming core remains under `Mettapedia.Logic.LP`, with Datalog
  represented as the function-free LP fragment.

References repointed:
- `Mettapedia/external/prolog-formalization/INDEX.lean` now points readers to
  `Mettapedia/Logic/LP/` instead of the old standalone Datalog directory.

Facade deletion:
- The compatibility module was deleted; no replacement facade was left behind.

Verification surface:
- Check no import or qualified reference to `Mettapedia.Logic.Datalog` remains.
- Check no stale `Mettapedia/Logic/Datalog/` source-path reference remains.
- Build `Mettapedia.Logic.LP` and the full `Mettapedia` target.

## Cluster 6c.79: Higher-order PLN reduction surface

Status: completed in the working tree.

Moved paths:
- `HigherOrder.lean` moved from the logic attic to
  `Mettapedia/PLN/RuleFamilies/HigherOrder/Reduction.lean`.
- `HigherOrder/Basic.lean`, `HigherOrder/HigherOrderReduction.lean`, and
  `HigherOrder/PredCode/Basic.lean` moved to
  `Mettapedia/PLN/RuleFamilies/HigherOrder/Reduction/`.

Namespace:
- The PLN-book HOI-to-FOI reduction surface now lives under
  `Mettapedia.PLN.RuleFamilies.HigherOrder.Reduction`.

Rationale:
- The moved surface defines the PLN-book higher-order-to-first-order
  reduction over PLN quantifiers, PLN evidence, and quantale-weakness
  semantics. It is therefore a PLN higher-order rule-family surface, not a
  generic higher-order logic kernel.

References repointed:
- `Mettapedia/PLN/RuleFamilies/HigherOrder.lean` imports the moved reduction
  aggregator.
- `Mettapedia/PLN/Bridges/Logic/HigherOrderInferenceRuleBridge.lean` imports
  and opens the moved reduction namespace.
- `Mettapedia/PLN/Bridges/HOL/PLNWorldModelPredCode.lean` and
  `Mettapedia/PLN/Bridges/HOL/PLNWorldModelPredCodeConsequence.lean` now name
  the moved predicate-code namespace.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the moved higher-order reduction surface.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.RuleFamilies.HigherOrder.Reduction
  Mettapedia.PLN.RuleFamilies.HigherOrder
  Mettapedia.PLN.Bridges.Logic.HigherOrderInferenceRuleBridge
  Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCode
  Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCodeConsequence
  Mettapedia.TaxonomyMigrationLedger`
- Check no old `Mettapedia.Logic.HigherOrder`, corresponding old import, or
  old file-path reference remains outside this ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved higher-order reduction files.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint:
  `member_eq_evaluation`,
  `extensional_implication_reduces_to_subset`,
  `ch10_context_hyp_fixture_mismatch_not_sound`,
  `forAll_himp_not_equal_inheritance_ratio_unconditional`,
  and `similarity_symmetric`.

## Cluster 6c.80: HOL world-model PLN bridge core

Status: completed in the working tree.

Moved paths:
- `HOL/WorldModel.lean` moved from the logic room to
  `Mettapedia/PLN/Bridges/HOL/PLNWorldModelHOLCore.lean`.
- `HOL/WorldModelCompleteness.lean` moved from the logic room to
  `Mettapedia/PLN/Bridges/HOL/PLNWorldModelHOLCompletenessCore.lean`.

Namespace:
- The core Henkin-HOL world-model bridge now lives under
  `Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCore`.
- The consequence/completeness wrapper core now lives under
  `Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCompletenessCore`.

Rationale:
- These files instantiate PLN `BinaryWorldModel` and world-model consequence
  surfaces on Church/Henkin HOL semantics. Their definitions are bridge
  definitions between HOL and PLN world-model infrastructure, not standalone
  HOL proof/model theory. The existing public
  `Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOL*` alias surfaces now point at
  the moved bridge cores instead of a logic-room implementation.

References repointed:
- `Mettapedia/PLN/Bridges/HOL.lean` imports the moved core modules.
- `Mettapedia/PLN/Bridges/HOL/PLNWorldModelHOL.lean` and
  `Mettapedia/PLN/Bridges/HOL/PLNWorldModelHOLCompleteness.lean` now alias the
  moved core namespaces.
- Downstream HOL probabilistic/logical-induction consumers, PLN HOL bridges,
  category-theory regression canaries, and PLN examples now reference the moved
  core namespaces directly.
- `Mettapedia/Logic/ProbHOL.lean` keeps the boundary note pointed at the new
  PLN/HOL bridge-core path.
- No old import path, qualified namespace, or old source path remains outside
  this ledger for the moved HOL world-model bridge cores.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCore
  Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCompletenessCore
  Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOL
  Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCompleteness
  Mettapedia.PLN.Bridges.HOL Mettapedia.Examples.PLN.HOLExampleLadder
  Mettapedia.Examples.PLN.HOLProbPLNExampleDemo
  Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCategoricalRegression`
- Check no old `Mettapedia.Logic.HOL.WorldModel`,
  `Mettapedia.Logic.HOL.WorldModelCompleteness`, corresponding old import, or
  old file-path reference remains outside this ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved HOL world-model bridge-core files.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint:
  `singleton_adequacy_strength_one`,
  `pointwiseImplies_iff_singletonStrengthLE`,
  `queryStrength_le_of_pointwise`,
  `pointwiseIff_iff_queryEq`, and
  `multiset_strength_le_of_pointwise`.

## Boundary audit after Cluster 6c.80

Status: clean gate boundary after the HOL world-model PLN bridge core
relocation.

Remaining high-confidence keep-set:
- The HOL, LP/Datalog, modal μ-calculus, modal
  quantale semantics, and ProbHOL surfaces remain in the logic room because
  their definitions are still formal-system, proof/model-theoretic, or
  logic-programming infrastructure.

Remaining explicit defer-set:
- The Markov and WMMarkov surface, BDD surface, governance/DDLPlus surface,
  metaphysics/gunk surface, and ontology-growth bridges remain below the
  migration confidence threshold for this run.
- `ModalQueryEncoder.lean` and `TemporalDeonticBridge.lean` are bridge
  surfaces whose clean home depends on a broader temporal/deontic/PLN policy
  decision, so they are not moved by filename alone.
- `Bridges/RhoTemporal.lean` was left in place at this boundary, then
  re-inspected and moved in Cluster 6c.86 after its definitions were found to
  be ρ-calculus temporal-reachability bridge material rather than PLN theorem
  infrastructure.
- `Archive/PLNQuantaleConnectionLegacy.lean` is an archived implementation
  referenced only as historical source material by the live PLN compatibility
  module. At this boundary, relocating archived material was treated as an
  archival-policy decision rather than a theorem-surface taxonomy move. It was
  later re-inspected and moved in Cluster 6c.85.

Verification surface for the boundary:
- `find Mettapedia/Logic -type f -name '*.lean'` shows the remaining logic
  room is dominated by the genuine logic keep-set plus the explicit defer-set.
- No old checker-reflection, Datalog, higher-order reduction, or HOL
  world-model bridge path remains outside this ledger.
- No facade marker remains.
- `lake build Mettapedia.Algorithms.FortiniFiniteCheckers
  Mettapedia.Algorithms.CheckerReflection`, `lake build
  Mettapedia.Logic.LP`, `lake build
  Mettapedia.PLN.RuleFamilies.HigherOrder.Reduction`, `lake build
  Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCore`, `lake build
  Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCompletenessCore`, `lake build
  Mettapedia.TaxonomyMigrationLedger`, and full `lake build Mettapedia` pass
  at this boundary.

## Cluster 6c.81: ProbHOL world-model PLN bridge

Status: completed in the working tree.

Moved path:
- `HOL/Probabilistic/WorldModelBridge.lean` moved from the logic room to
  `Mettapedia/PLN/Bridges/HOL/ProbHOLWorldModelBridge.lean`.

Namespace:
- The bridge now lives under
  `Mettapedia.PLN.Bridges.HOL.ProbHOLWorldModelBridge`.

Rationale:
- The moved file is the thin PLN-facing lens from ProbHOL sentence
  probabilities to `BinaryEvidence` and WM-style query strength. The
  semantic ProbHOL definitions remain under `Mettapedia.Logic.HOL.Probabilistic`;
  only the PLN evidence/strength view moved to the PLN/HOL bridge room.

References repointed:
- `Mettapedia/Logic/HOL/Probabilistic.lean` and
  `Mettapedia/Logic/HOL/Probabilistic/EmpiricalSpecialCase.lean` now import
  the moved bridge module.
- ProbHOL regression and belief-bridge consumers now open the moved bridge
  namespace for the already-existing unqualified bridge names.
- `Mettapedia/PLN/Core/PLNCanonicalAPI.lean` now exports the moved bridge
  definitions from their new PLN bridge namespace.
- `Mettapedia/PLN/Bridges/HOL.lean` now imports the moved bridge module.
- No old import path, qualified namespace for the moved declarations, or old
  source path remains outside this ledger.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Bridges.HOL.ProbHOLWorldModelBridge
  Mettapedia.Logic.HOL.Probabilistic
  Mettapedia.Logic.HOL.Probabilistic.EmpiricalSpecialCase
  Mettapedia.Logic.HOL.Probabilistic.BeliefBridge
  Mettapedia.Logic.HOL.Probabilistic.BenchmarkBeliefBridge
  Mettapedia.Logic.HOL.Probabilistic.Regression
  Mettapedia.Logic.HOL.Probabilistic.BeliefRegression
  Mettapedia.PLN.Core.PLNCanonicalAPI Mettapedia.PLN.Bridges.HOL`
- Check no old `Mettapedia.Logic.HOL.Probabilistic.WorldModelBridge`,
  corresponding old import, moved qualified declaration namespace, or old file
  path remains outside this ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved ProbHOL world-model bridge file.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint:
  `probEvidence_total_one`,
  `probQueryStrength_eq_sentenceProb`,
  `probQueryStrength_mono_of_pointwiseImplies`, and
  `probQueryStrength_eq_of_pointwiseIff`.

## Boundary audit after Cluster 6c.81

Status: clean gate boundary after the ProbHOL world-model PLN bridge
relocation.

Remaining high-confidence keep-set:
- The core ProbHOL semantic, flattening, hierarchical-state, belief-process,
  and regression surfaces remain in the logic/HOL room because their
  definitions are semantic or logical-induction comparison infrastructure,
  not standalone PLN evidence lenses.
- The HOL, LP/Datalog, modal μ-calculus, and modal quantale semantics surfaces
  remain in the logic room because their definitions are formal-system,
  proof/model-theoretic, or logic-programming infrastructure.

Remaining explicit defer-set:
- The Markov and WMMarkov surface, BDD surface, governance/DDLPlus surface,
  metaphysics/gunk surface, and ontology-growth bridges remain below the
  migration confidence threshold for this run.
- The remaining temporal/deontic/modal/OSLF bridge surfaces require a broader
  bridge-placement policy decision or decomposition before any safe move.

Verification surface for the boundary:
- `find Mettapedia/Logic -type f -name '*.lean'` reports 212 files remaining
  in the logic room; `find Mettapedia/Logic -maxdepth 1 -type f -name '*.lean'`
  reports 80 root files.
- No old checker-reflection, Datalog, higher-order reduction, HOL world-model
  bridge, or ProbHOL world-model bridge path remains outside this ledger.
- No facade marker remains.
- The targeted bridge build for Cluster 6c.81 passes at this boundary.

## Cluster 6c.82: Logical-induction belief-day PLN bridge

Status: completed in the working tree.

Moved path:
- `HOL/LogicalInduction/WorldModelBridge.lean` moved from the logic room to
  `Mettapedia/PLN/Bridges/HOL/LogicalInductionWorldModelBridge.lean`.

Namespace:
- The bridge now lives under
  `Mettapedia.PLN.Bridges.HOL.LogicalInductionWorldModelBridge`.

Rationale:
- The moved file is the thin PLN-facing evidence/strength view of a single
  logical-induction belief day. The logical-induction coding, market,
  criterion, conditioning, calibration, empirical examples, and regressions
  remain under `Mettapedia.Logic.HOL.LogicalInduction`; only the
  `BinaryEvidence`/WM-style strength lens moved to the PLN/HOL bridge room.

References repointed:
- `Mettapedia/Logic/HOL/LogicalInduction.lean` and
  `Mettapedia/Logic/HOL/LogicalInduction/EmpiricalSpecialCase.lean` now import
  the moved bridge module.
- Logical-induction and ProbHOL consumers now open the moved bridge namespace
  where they use the existing unqualified belief-evidence/day-strength names.
- `Mettapedia/PLN/Core/PLNCanonicalAPI.lean` now exports the moved bridge
  definitions from their new PLN bridge namespace.
- `Mettapedia/PLN/Bridges/HOL.lean` now imports the moved bridge module.
- No old import path, qualified namespace for the moved declarations, or old
  source path remains outside this ledger.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Bridges.HOL.LogicalInductionWorldModelBridge
  Mettapedia.Logic.HOL.LogicalInduction
  Mettapedia.Logic.HOL.LogicalInduction.EmpiricalSpecialCase
  Mettapedia.Logic.HOL.LogicalInduction.Regression
  Mettapedia.Logic.HOL.Probabilistic.BeliefBridge
  Mettapedia.Logic.HOL.Probabilistic.BenchmarkBeliefBridge
  Mettapedia.Logic.HOL.Probabilistic.BeliefRegression
  Mettapedia.PLN.Core.PLNCanonicalAPI Mettapedia.PLN.Bridges.HOL`
- Check no old `Mettapedia.Logic.HOL.LogicalInduction.WorldModelBridge`,
  corresponding old import, moved qualified declaration namespace, or old file
  path remains outside this ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved logical-induction world-model bridge file.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint:
  `beliefEvidence_total_one`,
  `dayQueryStrength_eq_priceMass`,
  `dayQueryStrength_eq_price`,
  `dayQueryStrength_ext`, and
  `dayQueryStrength_independent_of_henkin_truth`.

## Boundary audit after Cluster 6c.82

Status: clean gate boundary after the logical-induction belief-day PLN bridge
relocation.

Remaining high-confidence keep-set:
- The core logical-induction syntax, market, criterion, conditioning,
  calibration, empirical, and regression surfaces remain in the logic/HOL room
  because their definitions are logical-induction infrastructure rather than
  the PLN evidence lens.
- The core ProbHOL semantic, flattening, hierarchical-state, belief-process,
  and regression surfaces remain in the logic/HOL room for the same semantic
  infrastructure reason.

Remaining explicit defer-set:
- The Markov and WMMarkov surface, BDD surface, governance/DDLPlus surface,
  metaphysics/gunk surface, and ontology-growth bridges remain below the
  migration confidence threshold for this run.
- The remaining temporal/deontic/modal/OSLF bridge surfaces require a broader
  bridge-placement policy decision or decomposition before any safe move.

Verification surface for the boundary:
- `find Mettapedia/Logic -type f -name '*.lean'` reports 211 files remaining
  in the logic room; `find Mettapedia/Logic -maxdepth 1 -type f -name '*.lean'`
  reports 80 root files.
- No old checker-reflection, Datalog, higher-order reduction, HOL world-model
  bridge, ProbHOL world-model bridge, or logical-induction belief-day bridge
  path remains outside this ledger.
- No facade marker remains.
- The targeted bridge build for Cluster 6c.82 passes at this boundary.

## Cluster 6c.83: LP world-model PLN bridge

Status: completed in the working tree.

Moved path:
- `LP/WorldModelBridge.lean` moved from the logic room to
  `Mettapedia/PLN/Bridges/Logic/LPWorldModelBridge.lean`.

Namespace:
- The bridge now lives under
  `Mettapedia.PLN.Bridges.Logic.LPWorldModelBridge`.

Rationale:
- The moved file is the thin PLN-facing evidence/world-model lens from an LP
  least Herbrand model to `BinaryEvidence` and monotone evidence counts.
  Generic LP syntax, semantics, SLD, provenance, PathMap, OSLF, and
  range-restriction definitions remain under `Mettapedia.Logic.LP`.
- The `Mettapedia.Logic.LP` barrel no longer imports this PLN-facing bridge,
  so the logic-programming kernel does not export PLN evidence readouts.

References repointed:
- `Mettapedia/PLN/Bridges/Logic.lean` now imports the moved bridge module.
- `Mettapedia/OSLF/SpecIndex.lean` now imports the moved bridge module and
  checks the LP evidence bridge declarations at their new PLN bridge
  namespace.
- No old import path, qualified namespace for the moved declarations, or old
  source path remains outside this ledger.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Bridges.Logic.LPWorldModelBridge
  Mettapedia.PLN.Bridges.Logic Mettapedia.Logic.LP
  Mettapedia.OSLF.SpecIndex`
- Check no old `Mettapedia.Logic.LP.WorldModelBridge`, corresponding old
  import, moved qualified declaration namespace, or old file path remains
  outside this ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved LP world-model bridge file.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint:
  `lpLeastModelEvidence`, `lpEvidence_monotone`, and `lpEDB_posEvidence`.

## Cluster 6c.84: PeTTa function-free LP bridge

Status: completed in the working tree.

Moved path:
- `LP/FunctionFreePeTTa.lean` moved from the logic room to
  `Mettapedia/Languages/MeTTa/PeTTa/FunctionFreeLPBridge.lean`.

Namespace:
- The bridge now lives under
  `Mettapedia.Languages.MeTTa.PeTTa.FunctionFreeLPBridge`.

Rationale:
- The moved file is a concrete PeTTa-language bridge: it compiles a fully
  ground PeTTa fragment to a function-free LP/Datalog knowledge base and
  proves the evaluation/LHM correspondence. Generic function-free LP
  semantics remain under `Mettapedia.Logic.LP`.
- The PeTTa barrel now imports the bridge; the LP README no longer lists it
  as an LP-local module.

References repointed:
- `Mettapedia/Languages/MeTTa/PeTTa.lean` imports the moved bridge module.
- `Mettapedia/Logic/LP/README.md` no longer links to the old LP-local path.
- No old import path, qualified namespace, or old source path remains outside
  this ledger.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.Languages.MeTTa.PeTTa.FunctionFreeLPBridge
  Mettapedia.Languages.MeTTa.PeTTa Mettapedia.TaxonomyMigrationLedger`
- Check no old `Mettapedia.Logic.LP.FunctionFreePeTTa`, corresponding old
  import, moved qualified declaration namespace, or old file path remains
  outside this ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved PeTTa function-free LP bridge file.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint:
  `pettaEval_ruleApp_sound`, `pettaEval_ruleApp_complete'`, and
  `pettaEval_ground_iff_lhm`.

## Cluster 6c.85: legacy PLN quantale connection

Status: completed in the working tree.

Moved path:
- `Archive/PLNQuantaleConnectionLegacy.lean` moved from the logic room to
  `Mettapedia/PLN/RuleFamilies/QuantaleSemantics/PLNQuantaleConnectionLegacy.lean`.

Namespace:
- The archived implementation now lives under
  `Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PLNQuantaleConnectionLegacy`.

Rationale:
- The moved file is an exploratory PLN strength-level quantale packaging. Its
  definitions are PLN rule-family/quantale-semantics material, not logic
  infrastructure.
- The active compatibility shim remains
  `Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PLNQuantaleConnection`, so
  this archived implementation no longer shares declarations with the active
  shim and can be built directly without namespace collisions.

References repointed:
- The active `PLNQuantaleConnection` shim now points to the new archived module
  path in its explanatory note.
- Category-theory and first-order PLN explanatory references no longer point
  at the old logic-archive path.
- No old logic-archive import path, qualified namespace, or old source path
  remains outside this ledger.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PLNQuantaleConnectionLegacy
  Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PLNQuantaleConnection
  Mettapedia.TaxonomyMigrationLedger`
- Check no old `Mettapedia.Logic.Archive.PLNQuantaleConnectionLegacy`, old
  source path, or old logic-archive reference remains outside this ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved legacy PLN quantale file.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint:
  `pln_enriched_composition_law`, `pln_is_quantale_transitivity`, and
  `unit_interval_transitivity`.

## Cluster 6c.86: ρ-calculus temporal bridge

Status: completed in the working tree.

Moved path:
- `Bridges/RhoTemporal.lean` moved from the logic room to
  `Mettapedia/Languages/ProcessCalculi/RhoCalculus/Bridges/TemporalLogic.lean`.

Namespace:
- The bridge now lives under
  `Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TemporalLogic`.

Rationale:
- The moved file imports only ρ-calculus spice/multistep machinery and proves
  temporal-reachability facts for ρ-calculus processes: present moment,
  n-step temporal shift, future decomposition, and past/future predicate
  readouts.
- Although its documentation relates these constructions to PLN temporal
  intuitions, the definitions themselves are process-calculus language
  infrastructure, not PLN theorem surfaces and not core logic.

References repointed:
- `Mettapedia/Languages/ProcessCalculi/RhoCalculus.lean` now imports the new
  `Bridges` barrel.
- No old `Mettapedia.Logic.Bridges.RhoTemporal` import path, qualified
  namespace, or old source path remains outside this ledger.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TemporalLogic
  Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges
  Mettapedia.Languages.ProcessCalculi.RhoCalculus
  Mettapedia.TaxonomyMigrationLedger`
- Check no old `Mettapedia.Logic.Bridges.RhoTemporal`, old import, old
  qualified declaration namespace, or old file path remains outside this
  ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved ρ-calculus temporal bridge file.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint:
  `present_is_one_step`, `future_decomposition`, and
  `past_as_backward_shift`.

## Cluster 6c.87: MeTTaIL-to-LP bridge

Status: completed in the working tree.

Moved path:
- `LP/MeTTaILBridge.lean` moved from the logic-programming room to
  `Mettapedia/OSLF/MeTTaIL/LPBridge.lean`.

Namespace:
- The bridge now lives under
  `Mettapedia.OSLF.MeTTaIL.LPBridge`.

Rationale:
- The moved file encodes MeTTaIL rewrite rules and declarative reductions into
  LP knowledge bases, then proves least-Herbrand-model membership results for
  that encoding.
- Its definitions are a bridge from the MeTTaIL/OSLF source language into LP
  semantics, not generic LP infrastructure such as substitution, unification,
  SLD resolution, least-model semantics, or range restriction.
- The active users are MeTTa/PeTTa language modules, so the source-language
  side is the less misleading home.

References repointed:
- PeTTa LP-soundness and its downstream examples now import/open
  `Mettapedia.OSLF.MeTTaIL.LPBridge`.
- The LP README no longer lists the moved bridge as a local LP-kernel module.
- No old `Mettapedia.Logic.LP.MeTTaILBridge` import path, qualified namespace,
  or old source path remains outside this ledger.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.OSLF.MeTTaIL.LPBridge
  Mettapedia.Languages.MeTTa.PeTTa.LPSoundness
  Mettapedia.Languages.MeTTa.PeTTa.OSLFInstance
  Mettapedia.Languages.MeTTa.DTTSeedProofPath
  Mettapedia.TaxonomyMigrationLedger`
- Check no old `Mettapedia.Logic.LP.MeTTaILBridge`, old import, old
  qualified declaration namespace, or old file path remains outside this
  ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved MeTTaIL LP bridge file.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint:
  `groundTerm_pairTerm`, `lp_complete_topRule`, and
  `lp_sound_rewriteOnly`.

## Cluster 6c.88: LP-to-OSLF RelationEnv bridge

Status: completed in the working tree.

Moved path:
- `LP/OSLFBridge.lean` moved from the logic-programming room to
  `Mettapedia/OSLF/MeTTaIL/LPRelationEnvBridge.lean`.

Namespace:
- The bridge now lives under
  `Mettapedia.OSLF.MeTTaIL.LPRelationEnvBridge`.

Rationale:
- The moved file converts LP finite interpretations and least Herbrand models
  into MeTTaIL/OSLF `RelationEnv` tuples.
- Its definitions are an adapter from LP models into the OSLF relation-query
  interface, not generic LP kernel material such as substitution, unification,
  SLD, or least-model construction itself.
- The OSLF specification index is the direct consumer of the bridge constants,
  while the LP barrel no longer needs to present them as core LP API.

References repointed:
- `Mettapedia/OSLF/SpecIndex.lean` now imports and checks the new bridge module
  path.
- `Mettapedia/Logic/LP.lean` no longer imports or advertises the OSLF
  RelationEnv adapter as part of the LP kernel barrel.
- The LP README points readers to the new OSLF/MeTTaIL bridge home.
- No old `Mettapedia.Logic.LP.OSLFBridge` import path, old qualified
  declarations such as `Mettapedia.Logic.LP.lpToRelEnv`, or old source path
  remains outside this ledger.

Facade deletion:
- No compatibility module was left at the old path.

Verification surface:
- Targeted build:
  `lake build Mettapedia.OSLF.MeTTaIL.LPRelationEnvBridge
  Mettapedia.OSLF.SpecIndex Mettapedia.Logic.LP
  Mettapedia.TaxonomyMigrationLedger`
- Check no old `Mettapedia.Logic.LP.OSLFBridge`, old bridge-local qualified
  declaration namespace, old import, or old file path remains outside this
  ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved RelationEnv bridge file.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint:
  `constToPattern_injective`, `leastHerbrandModelRelEnv_complete`, and
  `leastHerbrandModelRelEnv_sound`.

## Cluster 6c.89: PLN-facing Probabilistic HOL bridge/regression surface

Status: completed in the working tree.

Moved paths:
- `HOL/Probabilistic/EmpiricalSpecialCase.lean`,
  `Regression.lean`, `BenchmarkBridge.lean`,
  `HierarchicalRegression.lean`, `BeliefBridge.lean`,
  `BenchmarkBeliefBridge.lean`, and `BeliefRegression.lean`
  moved from `Mettapedia/Logic/` to
  `Mettapedia/PLN/Bridges/HOL/Probabilistic/`.

Namespace:
- The moved bridge/regression surface now lives under
  `Mettapedia.PLN.Bridges.HOL.Probabilistic`.

Rationale:
- The unmoved `Mettapedia.Logic.HOL.Probabilistic` layer contains the semantic
  core: model spaces, sentence probabilities, indexed spaces, hierarchical
  states, and flattening.
- The moved files are the PLN-facing empirical, benchmark, belief, and
  regression surfaces. They import PLN world-model bridges or PLN guarded
  higher-order semantics, and their definitions consume semantic ProbHOL as a
  bridge into PLN rule-family and benchmark machinery.
- The split keeps the core HOL probability semantics in `Logic` while housing
  the consumer-facing PLN bridge under the PLN bridge hierarchy.

References repointed:
- `Mettapedia/PLN/Bridges/HOL.lean` imports the new probabilistic bridge
  barrel.
- `Mettapedia/Logic/HOL/Probabilistic.lean` now exports only the semantic core
  and points readers to the PLN bridge barrel for empirical, benchmark, belief,
  and regression consumers.
- The PLN planner bridge and the HOL example ladder now import the new
  `Mettapedia.PLN.Bridges.HOL.Probabilistic.BenchmarkBeliefBridge` path.
- No old bridge/regression import path, old qualified declaration namespace, or
  old source path remains outside this ledger.

Facade deletion:
- No compatibility module was left at the old paths.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Bridges.HOL.Probabilistic
  Mettapedia.PLN.Bridges.HOL Mettapedia.Logic.HOL.Probabilistic
  Mettapedia.PLN.RuleFamilies.HigherOrder.PLNProbHOLPlannerBridge
  Mettapedia.Examples.PLN.HOLExampleLadder
  Mettapedia.TaxonomyMigrationLedger`
- Check no old bridge/regression `Mettapedia.Logic.HOL.Probabilistic.*`
  import, qualified namespace, or old source path remains outside this ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved probabilistic bridge/regression files.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint:
  `empiricalSentenceProb_eq_staticQueryStrength`,
  `benchmarkBeliefDay_tracks_benchmarkSentenceProb`, and
  `regression_empiricalBeliefDay_tracks_empiricalPair_sample`.

## Cluster 6c.90: PLN-facing Logical-Induction empirical/regression bridge

Status: completed in the working tree.

Moved paths:
- `HOL/LogicalInduction/EmpiricalSpecialCase.lean` and
  `HOL/LogicalInduction/Regression.lean` moved from `Mettapedia/Logic/` to
  `Mettapedia/PLN/Bridges/HOL/LogicalInduction/`.

Namespace:
- The moved empirical/regression surface now lives under
  `Mettapedia.PLN.Bridges.HOL.LogicalInduction`.

Rationale:
- The unmoved `Mettapedia.Logic.HOL.LogicalInduction` layer contains the core
  HOL-facing logical-induction vocabulary: closed-code syntax, deductive
  processes, market orders, exploitability criterion, conditioning,
  calibration, and the Pure artifact boundary.
- The moved files are the PLN/HOL world-model empirical shadow and its
  regression wrapper. They import the PLN/HOL logical-induction world-model
  bridge and compare day-level belief prices with static HOL world-model query
  strength.
- The split keeps logical-induction theory under `Logic.HOL` while housing the
  PLN-facing empirical and regression consumers under the PLN bridge hierarchy.

References repointed:
- `Mettapedia/PLN/Bridges/HOL.lean` imports the new logical-induction bridge
  barrel.
- `Mettapedia/Logic/HOL/LogicalInduction.lean` now exports only the core
  logical-induction layer and points readers to the PLN bridge barrel for the
  empirical/regression shadow.
- `Mettapedia/PLN/Bridges/HOL/Probabilistic/BeliefBridge.lean` imports the new
  `Mettapedia.PLN.Bridges.HOL.LogicalInduction.EmpiricalSpecialCase` path.
- `Mettapedia/PLN/Core/PLNCanonicalAPI.lean` now exports the empirical
  belief-day helpers from their new PLN bridge namespace.
- `Mettapedia/papers/wm-pln-book.tex` cites the new empirical special-case
  source path.
- No old empirical/regression import path, old qualified declaration namespace,
  or old source path remains outside this ledger.

Facade deletion:
- No compatibility module was left at the old paths.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Bridges.HOL.LogicalInduction
  Mettapedia.PLN.Bridges.HOL Mettapedia.Logic.HOL.LogicalInduction
  Mettapedia.PLN.Bridges.HOL.Probabilistic.BeliefBridge
  Mettapedia.PLN.Bridges.HOL.Probabilistic.BeliefRegression
  Mettapedia.PLN.Core.PLNCanonicalAPI Mettapedia.Logic.ProbHOL
  Mettapedia.TaxonomyMigrationLedger`
- Check no old `Mettapedia.Logic.HOL.LogicalInduction.EmpiricalSpecialCase`,
  `Mettapedia.Logic.HOL.LogicalInduction.Regression`, corresponding moved
  qualified declaration namespace, or old file path remains outside this
  ledger.
- Check no migration facade marker remains.
- The strict unfinished-proof scan found no `sorry`, `admit`, or
  `theorem_wanted` in the moved logical-induction empirical/regression files.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint:
  `empiricalDayStrength_eq_staticQueryStrength`,
  `empiricalBeliefDay_singleton_of_satisfies`, and
  `regression_empiricalDayStrength_eq_staticQueryStrength`.

## Cluster 6c.91: Probabilistic HOL barrel boundary cleanup

Status: completed in the working tree.

Moved paths:
- None. This was a no-move boundary cleanup tied to the already-completed
  probabilistic HOL bridge relocation.

Namespace:
- No declaration namespace changed.

Rationale:
- `Mettapedia.Logic.HOL.Probabilistic` is the public entrypoint for the core
  semantic ProbHOL layer: model spaces, sentence probabilities, indexed spaces,
  hierarchical states, and flattening.
- The PLN-facing WM/strength bridge already lives at
  `Mettapedia.PLN.Bridges.HOL.ProbHOLWorldModelBridge`, and the richer
  empirical/benchmark/belief/regression consumers live under
  `Mettapedia.PLN.Bridges.HOL.Probabilistic`.
- Therefore the Logic barrel should not re-export the PLN bridge. Removing that
  import keeps the semantic core in Logic and the PLN consumer surface in PLN.

References repointed:
- No external references needed repointing. PLN consumers import the bridge
  modules explicitly through `Mettapedia.PLN.Bridges.HOL` /
  `Mettapedia.PLN.Bridges.HOL.Probabilistic`.
- `Mettapedia/Logic/HOL/Probabilistic.lean` documentation now describes only
  the semantic core and points readers to the PLN bridge barrel for consumer
  surfaces.

Facade deletion:
- No compatibility module was left or needed.

Verification surface:
- Targeted build:
  `lake build Mettapedia.Logic.HOL.Probabilistic Mettapedia.Logic.ProbHOL
  Mettapedia.PLN.Bridges.HOL.Probabilistic Mettapedia.PLN.Core.PLNCanonicalAPI
  Mettapedia.TaxonomyMigrationLedger`
- Check `Mettapedia/Logic/HOL/Probabilistic.lean` contains no import of
  `Mettapedia.PLN.Bridges.HOL.ProbHOLWorldModelBridge`.
- Check no migration facade marker remains.
- No proof terms were changed by this boundary cleanup.

## Cluster 6c.92: hierarchical ProbHOL strength readout bridge

Status: completed in the working tree.

Moved paths:
- None. This was a definition extraction from the core Logic flattening module
  into a new PLN bridge module:
  `Mettapedia/PLN/Bridges/HOL/Probabilistic/HierarchicalStrengthBridge.lean`.

Namespace:
- `hierarchicalProbEvidence`,
  `hierarchicalProbEvidence_total_one`,
  `hierarchicalProbQueryStrength`,
  `hierarchicalProbQueryStrength_eq_sentenceProb`,
  `hierarchicalProbQueryStrength_mono_of_pointwiseImplies`, and
  `hierarchicalProbQueryStrength_eq_of_pointwiseIff` moved from
  `Mettapedia.Logic.HOL.Probabilistic` to
  `Mettapedia.PLN.Bridges.HOL.Probabilistic`.

Rationale:
- `Mettapedia.Logic.HOL.Probabilistic.Flattening` should state the semantic
  Kyburg/HOL flattening facts: hierarchical sentence probability and its
  monotonicity/equivalence laws.
- The extracted declarations package that probability as PLN `BinaryEvidence`
  and WM-style query strength. Those definitions depend on the PLN evidence
  calculus, so they belong under the PLN/HOL bridge hierarchy.
- This split removes PLN evidence/world-model imports from the Logic
  flattening module while keeping the semantic probability theorems in Logic.

References repointed:
- `Mettapedia.PLN.Bridges.HOL.Probabilistic` imports the new bridge module.
- PLN probabilistic HOL consumers that use `hierarchicalProbQueryStrength` now
  import or open `Mettapedia.PLN.Bridges.HOL.Probabilistic` explicitly.
- `Mettapedia.PLN.Core.PLNCanonicalAPI` exports the moved declarations from
  their new PLN bridge namespace.

Facade deletion:
- No compatibility declarations or modules were left at the old namespace.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Bridges.HOL.Probabilistic.HierarchicalStrengthBridge
  Mettapedia.Logic.HOL.Probabilistic.Flattening
  Mettapedia.PLN.Bridges.HOL.Probabilistic
  Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLProbabilisticBridge
  Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLCredalBridge
  Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLCanary
  Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLCompletenessTightness
  Mettapedia.PLN.Core.PLNCanonicalAPI Mettapedia.TaxonomyMigrationLedger`
- Check no `hierarchicalProbEvidence` / `hierarchicalProbQueryStrength`
  declarations remain under `Mettapedia.Logic.HOL.Probabilistic`.
- Check no migration facade marker remains.
- Spot-check moved theorem axiom footprints remain within the accepted project
  footprint.

## Cluster 6c.93: pure HOL satisfaction vocabulary extraction

Status: completed in the working tree.

Moved paths:
- None. This was a definition extraction from the PLN/HOL world-model bridge
  into a new pure HOL semantics module:
  `Mettapedia/Logic/HOL/Semantics/Satisfaction.lean`.

Namespace:
- `HOLQuery` and `holSatisfies` moved from
  `Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCore` to
  `Mettapedia.Logic.HOL`.

Rationale:
- `HOLQuery := ClosedFormula` and `holSatisfies := HenkinModel.models` are
  pure HOL semantic vocabulary.
- `Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCore` remains the PLN bridge:
  it counts satisfaction over multisets of Henkin models and provides the
  binary-evidence/world-model instance.
- This extraction removes the inverted dependency where
  `Mettapedia.Logic.HOL.Probabilistic` imported the PLN world-model bridge only
  to name HOL satisfaction.

References repointed:
- `Mettapedia.Logic.HOL` imports the new satisfaction module.
- `Mettapedia.Logic.HOL.Probabilistic.ModelSpace`, `IndexedSpaces`,
  `Semantics`, and `Flattening` use `Mettapedia.Logic.HOL.holSatisfies`
  through the HOL semantic namespace, not the PLN bridge namespace.
- Qualified uses of
  `Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCore.HOLQuery` and
  `Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCore.holSatisfies` were
  repointed to `Mettapedia.Logic.HOL.HOLQuery` and
  `Mettapedia.Logic.HOL.holSatisfies`.
- `Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOL` keeps PLN-facing public
  aliases, but those aliases now target the pure HOL semantic declarations.

Facade deletion:
- No compatibility declarations were left in
  `Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCore`.

Verification surface:
- Targeted build:
  `lake build Mettapedia.Logic.HOL.Semantics.Satisfaction
  Mettapedia.Logic.HOL.Probabilistic.ModelSpace
  Mettapedia.Logic.HOL.Probabilistic
  Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCore
  Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOL
  Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCompletenessCore
  Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCompleteness
  Mettapedia.PLN.Bridges.HOL.LogicalInduction.Regression
  Mettapedia.PLN.Bridges.HOL.Probabilistic.HierarchicalRegression
  Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCategoricalRegression
  Mettapedia.PLN.Core.PLNCanonicalAPI`
- Check no qualified
  `Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCore.HOLQuery` /
  `Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCore.holSatisfies` references
  remain outside this ledger.
- Check no `Mettapedia.Logic.HOL.Probabilistic` file imports or opens
  `Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCore`.
- Check no migration facade marker remains.
- Spot-check extracted theorem/definition axiom footprints remain within the
  accepted project footprint.

## Cluster 6c.94: HOL logical-induction Pure bridge evacuation

Status: completed in the working tree.

Moved paths:
- `Mettapedia/Logic/HOL/LogicalInduction/PureBridge.lean` moved to
  `Mettapedia/Languages/MeTTa/PureKernel/HOLLogicalInductionBridge.lean`.

Namespace:
- The artifact-boundary declarations moved from
  `Mettapedia.Logic.HOL.LogicalInduction` to
  `Mettapedia.Languages.MeTTa.PureKernel.HOLLogicalInductionBridge`.

Rationale:
- The moved file is not part of the core HOL logical-induction semantics. It
  packages closed HOL formula codes through the MeTTa Pure checking boundary
  and imports the Pure checking service, Pure-kernel pattern bridge, and
  HOL-to-Pure integration contract.
- `Mettapedia.Logic.HOL.LogicalInduction` now remains the logical-induction
  code/process/market/criterion/conditioning/calibration entrypoint.
- The Pure artifact boundary is housed on the language side, next to the
  existing PureKernel HOL integration contract.

References repointed:
- `Mettapedia.Logic.HOL.LogicalInduction` no longer imports the Pure bridge.
- `Mettapedia.Languages.MeTTa.PureKernel` and `Mettapedia.Languages.MeTTa`
  import the new language-side bridge module.
- The WM-PLN book code path for the bridge was repointed to the new location.

Facade deletion:
- No compatibility module or declaration was left at
  `Mettapedia.Logic.HOL.LogicalInduction.PureBridge`.

Verification surface:
- Targeted build:
  `lake build Mettapedia.Languages.MeTTa.PureKernel.HOLLogicalInductionBridge
  Mettapedia.Logic.HOL.LogicalInduction Mettapedia.Languages.MeTTa.PureKernel
  Mettapedia.Languages.MeTTa Mettapedia.TaxonomyMigrationLedger`
- Check no old `Mettapedia.Logic.HOL.LogicalInduction.PureBridge` import path,
  qualified namespace, or file path remains outside this ledger.
- Check no migration facade marker remains.

## Cluster 6c.95: modal query encoding bridge evacuation

Status: completed in the working tree.

Moved paths:
- `Mettapedia/Logic/ModalQueryEncoder.lean` moved to
  `Mettapedia/PLN/Bridges/Logic/ModalQueryEncoding.lean`.

Namespace:
- The encoder bridge declarations moved from
  `Mettapedia.Logic.ModalQueryEncoder` to
  `Mettapedia.PLN.Bridges.Logic.ModalQueryEncoding`.

Rationale:
- The moved file is not the modal μ-calculus or a core modal/deontic logic
  kernel. It imports the PLN temporal event-calculus encoder surface and the
  governance/deontic query encoder, then proves the shared modal-encoder
  interface between those already-existing structures.
- `Mettapedia.Logic.ModalMuCalculus`, `Mettapedia.Logic.ModalQuantaleSemantics`,
  `Mettapedia.Logic.DDLPlus`, and `Mettapedia.Logic.GovernanceReasoning` remain
  in Logic/deferred territory. This cluster only evacuates the PLN-facing bridge.

References repointed:
- `Mettapedia.PLN.Bridges.Logic` now imports the new bridge module.
- No compatibility module or declaration was left at
  `Mettapedia.Logic.ModalQueryEncoder`.

Verification surface:
- Targeted build:
  `lake build Mettapedia.PLN.Bridges.Logic.ModalQueryEncoding
  Mettapedia.PLN.Bridges.Logic Mettapedia.TaxonomyMigrationLedger`
- Check no old `Mettapedia.Logic.ModalQueryEncoder` import path, qualified
  namespace, or file path remains outside this ledger.
- Check no migration facade marker remains.
-/
