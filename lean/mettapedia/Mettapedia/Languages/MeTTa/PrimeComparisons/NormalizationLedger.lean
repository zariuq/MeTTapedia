import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueSound
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ConsistencySound
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.Comparison
import Mettapedia.Languages.MeTTa.PrimeCandidates.GSLTILLayeredCrown
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.HazardControl
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.TransportReadout
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis
import Mettapedia.GSLT.Core.SearchStreamProductivity
import Mettapedia.GSLT.Dynamics.RegionHolePlan
import Mettapedia.GSLT.Dynamics.GuardRevision
import Mettapedia.TypeTheory.UniverseLevel.Notation
import Mettapedia.TypeTheory.OperationalIntensionalExtensionalDependentFactorization
import Mettapedia.TypeTheory.OperationalIntensionalExtensionalSemanticThinness
import Mettapedia.TypeTheory.OperationalIntensionalExtensionalLocalTruncation
import Mettapedia.TypeTheory.OperationalIntensionalExtensionalTransportDiscriminator
import Mettapedia.TypeTheory.ListSuffixCostComparison
import Mettapedia.TypeTheory.ObserverTransportCompatibility
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Confluence.ReceiverRace

/-!
# The ledger of qualified normalization and compositional observation

One section per subject of the ledger.  Each settled statement is an alias of
the result that settles it, so it keeps that result's exact statement,
hypotheses and axioms; a subject with no settling result has no declaration,
and its section says what is open.

| Subject | Settled by | Open |
|---|---|---|
| object package with codes | strong normalization, consistency | conversion completeness, confluence, canonicity |
| executable package without codes | confluence, conversion algorithm | none for this package; nothing transfers to other packages |
| decoder hazard | a typed term that is not strongly normalizing, and the model obstruction | none |
| regular kernel (C) | none | outcome soundness of the implementation, capacity exhaustion |
| general Prime execution | an executable divergence control, not a theorem | exhaustion as its own outcome |
| OSLF/GSLT instances | modal meaning; rho nonconfluence by a nonjoinable fork, with the commuting twin | none for these statements |
| search and control | fairness, productivity and finite closure are independent | none for these canaries |
| local plan normalization | exact, trace-preserving, idempotent normalization of composition | the behaviour of regions |
| supercompilation | none | termination, residual correctness, residual behaviour |
| level notation | well-founded comparison below ε₀ | soundness of the universe rules, coherence of extensions |
| GSLT-IL | the functional fragment, the companion binding, the initial factorization | none for these statements |
| erasure | dependent factorization, semantic descent, observer contracts, the univalent control, the cost observer, transport compatibility | none for these statements |
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeComparisons.NormalizationLedger

/-! ## The object package with codes

Language: `objectRules`, the executable package with the program's proposition
codes and their decoder.  Relation: its root steps closed under every
congruence, under binders included; η is a conversion, not a reduction.
Quantified: terms typed in formed contexts.  Settled: strong normalization, for
a typed term and for both sides of a derivable equality, and consistency.  Open:
conversion completeness, confluence and canonicity for this package. -/

namespace ObjectPackage

alias strongNormalization :=
  Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.objectRules_sn

alias equalStrongNormalization :=
  Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.objectRules_equal_sn

alias consistency :=
  Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.CodeModel.consistent

end ObjectPackage

/-! ## The executable package without codes

Language: `rules`.  Settled for this package, and only for it: confluence of
its step relation and the conversion algorithm's completeness and decision. -/

namespace ExecutablePackage

alias churchRosser :=
  Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.churchRosser

alias conversionComplete :=
  Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.algorithm_complete

alias conversionDecision :=
  Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.equal_decide

end ExecutablePackage

/-! ## The decoder hazard

Language: the package with the code destructor `pred (all f) ⟶ f`.  Two kinds
of statement: a typed term that is not strongly normalizing, and the model
obstruction derived from it.  The obstruction: no model S whose realizer side
reduces by the package with the destructor is sound for that package, even
with its root steps read with their typing (`¬ TypedSoundS`).  Soundness in the
untyped reading implies the typed reading, so this also refutes the untyped
reading `SoundS`. -/

namespace DecoderHazard

alias omegaTyped :=
  Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality.Impredicative.Hazards.Omega_typed

alias omegaNotStronglyNormalizing :=
  Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality.Impredicative.Hazards.Omega_not_sn

alias modelObstruction :=
  Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality.Impredicative.Hazards.not_soundS

end DecoderHazard

/-! ## The regular kernel

Open: outcome soundness of the C implementation, including capacity exhaustion
at its fixed-size limits.  A bounded algorithm stopping is not a normalization
theorem for its inputs.

## General Prime execution

No termination theorem, and none is expected in general; particular programs
can still be proved terminating, divergent, productive or correct.  The
divergence control is an executable run of the C evaluator, not a theorem
here.  Open: exhaustion under a fuel bound as an outcome of its own, distinct
from an empty answer.  Answer sets, bags and ordered streams are distinct
observers. -/

/-! ## OSLF and GSLT instances

Settled: the modal meaning of synthesized types, and rho nonconfluence.
Confluence depends on the instance.

Rho relation: communication closed under parallel composition and structural
congruence (`Reduction.Reduces`), with its reflexive-transitive closure
`ReducesStar`; joinability is up to structural congruence.  The race
`@0!(M) | for(y <- @0){*y} | for(z <- @0){0}`, with `M = for(w <- @0){0}`,
steps to two reducts that have no common reduct: neither contains an output,
so neither reduces again, and structural congruence keeps their numbers of
input prefixes, two and one.  Rho reduction is therefore neither locally
confluent nor confluent.  The twin, the same two receivers on separate
channels with a copy of the message on each, closes the diamond after one step
on each side. -/

namespace ModalMeaning

alias galois := Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltGalois

alias diamondSpec := Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond_spec

end ModalMeaning

namespace RhoConfluence

alias outputNeeded :=
  Mettapedia.Languages.ProcessCalculi.RhoCalculus.Confluence.one_le_outputs_of_reduces

alias joinableIffCongruentWithoutOutputs :=
  Mettapedia.Languages.ProcessCalculi.RhoCalculus.Confluence.joinable_iff_of_no_output

alias nonjoinableFork :=
  Mettapedia.Languages.ProcessCalculi.RhoCalculus.Confluence.race_nonjoinable_fork

alias noCommonReduct :=
  Mettapedia.Languages.ProcessCalculi.RhoCalculus.Confluence.race_no_common_reduct

alias notLocallyConfluent :=
  Mettapedia.Languages.ProcessCalculi.RhoCalculus.Confluence.not_locallyConfluent

alias notConfluent := Mettapedia.Languages.ProcessCalculi.RhoCalculus.Confluence.not_confluent

alias separateChannelsSquare :=
  Mettapedia.Languages.ProcessCalculi.RhoCalculus.Confluence.separate_channels_square

alias twinSquare := Mettapedia.Languages.ProcessCalculi.RhoCalculus.Confluence.twin_square

alias twinJoinable := Mettapedia.Languages.ProcessCalculi.RhoCalculus.Confluence.twin_joinable

end RhoConfluence

/-! ## Search and control

Fairness, productivity and finite closure do not imply one another, with the
hypotheses of each canary. -/

namespace SearchControl

alias productiveFairOpenNotFiniteBag :=
  Mettapedia.GSLT.Core.SearchStreamProductivity.Canaries.productive_fair_open_and_not_finite_bag

alias fairnessNotProductivity :=
  Mettapedia.GSLT.Core.SearchStreamProductivity.Canaries.occurrence_fairness_does_not_imply_stream_productivity

alias productivityNotFairness :=
  Mettapedia.GSLT.Core.SearchStreamProductivity.Canaries.stream_productivity_does_not_imply_occurrence_fairness

end SearchControl

/-! ## Local plan normalization

Normalization of composition that preserves ordered suspended work; not the
behaviour of every region or of the whole agent. -/

namespace LocalPlan

alias normalizeExact := Mettapedia.GSLT.Dynamics.RegionHolePlan.normalize_exact

alias normalizeHoleTrace := Mettapedia.GSLT.Dynamics.RegionHolePlan.normalize_holeTrace

alias normalizeIdempotent := Mettapedia.GSLT.Dynamics.RegionHolePlan.normalize_idempotent

end LocalPlan

/-! ## Supercompilation

Open: transformation termination, residual correctness and residual-program
behaviour, three separate statements.  A whistle is not an object-program
normal form.

## Level notation

Settled: terminating comparison of level notations.  Open: soundness of the
universe rules that use them, and coherence of notation-system extensions. -/

namespace LevelNotation

alias comparisonWellFounded := Mettapedia.TypeTheory.UniverseLevel.Level.lt_wf

end LevelNotation

/-! ## GSLT-IL

Proof-relevant partial and nondeterministic routes are retained; direct
functional execution is an earned representation of the selected fragment. -/

namespace GSLTIL

alias fragmentDoesNotFunctionalizeRawCommands :=
  Mettapedia.Languages.MeTTa.PrimeCandidates.GSLTILLayeredCrown.represented_fragment_does_not_functionalize_raw_commands

alias dataExecutionCompanionBinding :=
  Mettapedia.Languages.MeTTa.PrimeCandidates.GSLTILLayeredCrown.dataExecution_companion_binding

alias initialFactorization :=
  Mettapedia.Languages.MeTTa.PrimeCandidates.GSLTILLayeredCrown.selected_initial_factorization

end GSLTIL

/-! ## Erasure

Semantic descent for named observer families, with the evidence retained and
the conditions for changing the family.

* Operational/intensional/extensional modes: operational observation factors
  through evidence completion and readout, dependently; the selected semantic
  cells descend to the locally thin reflection while raw histories stay
  distinct; revision- and work-distinct routes keep dependent discriminators.
* World revision: reuse under kept dependencies for every finite prefix, the
  stale-guard control, and movement across a partial valuation.
* The univalent control: transport along the identity and the negation of
  `Bool` differ, so an erasure identifying the loops is not admissible for
  transport observers.
* The cost observer: a directed comparison `copy ⇒ suffix` of the runtime's list
  tails; the result observer inverts it, the work observer does not.
* Transport compatibility: the naive law `E_B (transport p a) = transport_E (E p,
  E_A a)` fails for the value observer of the univalent universe; it holds
  exactly for observers that factor through the extensional readout, and the
  value model's transport satisfies it at the relation of the target pack.  In
  the object package's value model, identity elimination at instances of the
  motive related in a universe is related to its method at the pack of those
  instances. -/

namespace Erasure

alias dependentObservationFactorization :=
  Mettapedia.TypeTheory.OperationalIntensionalExtensionalDependentFactorization.dependent_observation_factorization

alias semanticFactorsThroughThin :=
  Mettapedia.TypeTheory.OperationalIntensionalExtensionalSemanticThinness.global_semantic_factors_through_thin

alias localErasureCoexistsWithRawHistory :=
  Mettapedia.TypeTheory.OperationalIntensionalExtensionalLocalTruncation.local_erasure_coexists_with_raw_history

alias localThinnessWithoutGlobalCutoff :=
  Mettapedia.TypeTheory.OperationalIntensionalExtensionalLocalTruncation.local_core_thinness_without_global_cutoff

alias thinnessAndContextProofRelevance :=
  Mettapedia.TypeTheory.OperationalIntensionalExtensionalTransportDiscriminator.local_thinness_and_context_proof_relevance_coexist

alias factorsThroughIffFactors :=
  Mettapedia.TypeTheory.ObserverErasure.factorsThrough_iff_factors

alias reuseOfKeptDependencies :=
  Mettapedia.GSLT.Dynamics.GuardRevision.reuse_of_kept_dependencies_prefix

alias staleGuardControl := Mettapedia.GSLT.Dynamics.GuardRevision.note_selection_not_adequate

alias hoistingChangesCompletion := Mettapedia.GSLT.Dynamics.GuardRevision.hoisting_changes_completion

/-! ### The univalent control -/

alias univalentProfileControl :=
  Mettapedia.TypeTheory.UnivalentUniverseTransport.FiniteUniverse.univalent_profile_control

alias notFactorsOfIdentifiedLoops :=
  Mettapedia.TypeTheory.UnivalentUniverseTransport.not_factors_transport_of_identifies_loops

alias factorsTransportObserverIff :=
  Mettapedia.TypeTheory.UnivalentUniverseTransport.FiniteUniverse.factors_transportObserver_iff

alias boolLoopsDiscriminated :=
  Mettapedia.TypeTheory.UnivalentUniverseTransport.FiniteUniverse.bool_loops_have_transportDiscriminator

alias unitLoopsNotDiscriminated :=
  Mettapedia.TypeTheory.UnivalentUniverseTransport.FiniteUniverse.unit_loops_have_no_transportDiscriminator

/-! ### The cost observer -/

alias observerContract :=
  Mettapedia.TypeTheory.ListSuffixCostComparison.factors_erase_iff_isInvertedBy

alias comparisonDirected := Mettapedia.TypeTheory.ListSuffixCostComparison.comparison_not_isIso

alias comparisonsImprove := Mettapedia.TypeTheory.ListSuffixCostComparison.cell_improves

alias resultObserverInverts :=
  Mettapedia.TypeTheory.ListSuffixCostComparison.resultObserver_inverts_comparison

alias resultFactors := Mettapedia.TypeTheory.ListSuffixCostComparison.result_factors

alias workObserverDoesNotInvert :=
  Mettapedia.TypeTheory.ListSuffixCostComparison.workObserver_not_inverts

alias workNotFactors := Mettapedia.TypeTheory.ListSuffixCostComparison.work_not_factors

/-! ### Transport compatibility -/

alias transportCompatibleIffFactors :=
  Mettapedia.TypeTheory.ObserverTransportCompatibility.transportCompatible_iff_factors

alias naiveTransportLawFails :=
  Mettapedia.TypeTheory.ObserverTransportCompatibility.FiniteUniverse.value_not_transportCompatible

alias readoutCompatible :=
  Mettapedia.TypeTheory.ObserverTransportCompatibility.totalReadout_transportCompatible

alias valueTransportReadout :=
  Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality.Impredicative.ValueSide.coe_readout

alias identityTransportReadout :=
  Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality.Impredicative.ValueSide.transportJ_readout

alias identityTransportAtUniverse :=
  Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality.Impredicative.ValueSide.transportJ_rel_of_universe

alias identityTransportInObjectModel :=
  Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.CodeModel.vmodel_transportJ_rel_of_universe

alias transportedTermNotObserver :=
  Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality.Impredicative.ValueSide.coe_term_not_factors

end Erasure

end Mettapedia.Languages.MeTTa.PrimeComparisons.NormalizationLedger
