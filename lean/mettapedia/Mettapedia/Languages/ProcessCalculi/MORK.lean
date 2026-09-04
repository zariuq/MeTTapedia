import Mettapedia.Languages.ProcessCalculi.MORK.MORKCommBridge
import Mettapedia.Languages.ProcessCalculi.MORK.PathMapBridge
import Mettapedia.Languages.ProcessCalculi.MORK.MatchSpec
import Mettapedia.Languages.ProcessCalculi.MORK.MeTTaILBridge
import Mettapedia.Languages.ProcessCalculi.MORK.WorkQueueExec
import Mettapedia.Languages.ProcessCalculi.MORK.WorkQueueOrder
import Mettapedia.Languages.ProcessCalculi.MORK.ThreePhaseRefinement
import Mettapedia.Languages.ProcessCalculi.MORK.Conformance
import Mettapedia.Languages.ProcessCalculi.MORK.ArithmeticExtension
import Mettapedia.Languages.ProcessCalculi.MORK.BridgeWorkspaceInterfaceRefinement
import Mettapedia.Languages.ProcessCalculi.MORK.BridgeCursorInterfaceRefinement
import Mettapedia.Languages.ProcessCalculi.MORK.BridgeAlgebraInterfaceRefinement
import Mettapedia.Languages.ProcessCalculi.MORK.PathOfAtomEncodingContract
import Mettapedia.Languages.ProcessCalculi.MORK.ExecutionBoundary
import Mettapedia.Languages.ProcessCalculi.MORK.CapabilityProfile
import Mettapedia.Languages.ProcessCalculi.MORK.GSLTSemantics
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveExecution
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveGSLTNativeTypes
import Mettapedia.Languages.ProcessCalculi.MORK.GSLTNativeTypes
import Mettapedia.Languages.ProcessCalculi.MORK.ProofRelevantGSLT
import Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface
import Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxSemantics
import Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxUTF8
import Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxWire
import Mettapedia.Languages.ProcessCalculi.MORK.MM2ParserProfileWire
import Mettapedia.Languages.ProcessCalculi.MORK.MM2ExecutionProfileWire
import Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenUTF8
import Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenExecution
import Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationPlanWire
import Mettapedia.Languages.ProcessCalculi.MORK.MM2RuleScopedExecution
import Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenRuleScopedExecution
import Mettapedia.Languages.ProcessCalculi.MORK.MM2RuleScopedReloadCanary
import Mettapedia.Languages.ProcessCalculi.MORK.ProviderExtension
import Mettapedia.Languages.ProcessCalculi.MORK.MeTTaZeroBoundary
import Mettapedia.Languages.ProcessCalculi.MORK.OccurrenceSeam

/-!
# MORK: Minimal Model 2 (MM2) Formalization

MORK (MM2 Object-Relational Kernel) is the execution substrate for MeTTa-Compiler.
This module formalises MORK's execution semantics and proves its structural
correspondence with the MQ-calculus COMM rule.

## Structure

```
MORK/
  Syntax.lean          — MM2 atoms, exec rules, patterns, templates, sinks, FoldAggregator
  Space.lean           — Space = Finset Atom; firing semantics; matchAtom/applySubst
  ThreePhaseExec.lean  — Authored hosted protocol: unfold/base/fold priority bands
  WorkQueueOrder.lean      — Exact full compact-expression scheduler key
  WorkQueueExec.lean       — Compatible/source-aware queues, explicit failure policy, exact fuel
  ThreePhaseRefinement.lean — Hosted phase steps → work-queue firing under hypotheses
  Conformance.lean         — 27 kernel-checked conformance + correspondence theorems
  ArithmeticExtension.lean — Int/float sink lowering + `CmpSource` packaging
  BridgeWorkspaceInterfaceRefinement.lean — Live insert/match/step workspace interface
  BridgeCursorInterfaceRefinement.lean — Bridge cursor API ↔ PathMap cursor semantics
  BridgeAlgebraInterfaceRefinement.lean — Live stepping vs structural export boundary
  PathOfAtomEncodingContract.lean — `path-of-atom` render/parse/traverse contract
  MORKCommBridge.lean  — Bridge: MORK binary fold ↔ MQ-calculus CommReduction
  PathMapBridge.lean   — Bridge: MORK space transitions ↔ PathMap lattice ops
  MatchSpec.lean       — Relational spec of atom matching (sound/complete fragment)
  MeTTaILBridge.lean   — Authored-rule and premise-to-source execution bridges
  ExecutionBoundary.lean — Packages the proven morkTranslatable execution boundary
  CapabilityProfile.lean — Native support strengths and faithful-encoding obstruction
  GSLTSemantics.lean   — Indexed MM2 GSLTs, control reification, honest bounded reports
  GSLTNativeTypes.lean — OSLF/CertificateGSLT native judgments generated from the family
  ProviderExtension.lean — Authored source/sink interfaces and realization laws
  MeTTaZeroBoundary.lean — Internal work-closure separation from bare Zero
```

## Key Results

- `phase_ranges_disjoint`: unfold/base/fold priority bands are mutually disjoint
- `phase_priority_monotone`: priorities are ordered unfold < base < fold
- `mork_fold_is_comm`: any binary MORK fold step corresponds to a MQ CommReduction
- `mork_fold_both_outcomes_exist`: MORK fold is non-deterministic (both sub-results possible)
- `mork_mq_nondeterminism_corresponds`: MORK non-determinism ↔ MQ comm_both_outcomes
- `applyBase_eq_lattice_ops`: MORK base step = PathMap psubtract + pjoin
- `applyFold_eq_lattice_ops`: MORK fold step = PathMap psubtract chain + pjoin
- `applySubst_commutes`: MORK applySubst commutes with morkPatternToAtom
- `stepAt_compiles_to_mork_fire`: bounded authored contextual step → MORK firing
- `rewriteRuleToSourceExecRule`: MeTTaIL rule (with premises) → MORK SourceExecRule
- `premiseToSourceFactor`: MeTTaIL relationQuery → MORK btm source factor
- `premisesToSourceFactors_length`: translatable premises preserve count
- `readCopy_mem_exec`: read copy always contains the exec fact (self-matching)
- `readCopy_eq_of_mem`: remove + re-insert = identity on membership
- `order_p0_lt_p1`: atomKey orders priority 0 before priority 1
- `order_1_lt_10`: atomKey shortlex: single-digit before double-digit
- `matchAtom_iff`: matchAtom (incl. expressions) ↔ MatchAtomRel (sound + complete)
- `nary_fold_all_outcomes_exist`: N-ary fold generalizes binary non-determinism
- `applyBase_eq_applySinks`: phase step = scheduler sink application
- `applySubst_nil`: empty substitution is identity on all atoms
- `applyAggregator_count`: count returns cardinality of staged support
- `applyAggregator_selectFirst`: fold selectFirst aggregator returns first sub-result
- `applyAggregator_count_perm`: count is permutation-invariant (match order irrelevant)
- `applyAggregator_sum_cons_of_mem`: duplicate staged rows do not change support sum
- `applyAggregator_sum_perm`: sum is permutation-invariant (match order irrelevant)
- `applySinks_mem_of_mem`: atoms persist through sink pipelines if never removed
- `canary8_ground_self_respawn`: ground self-respawn rule fires and re-adds exec fact
- `AggregatorConsistent`: fold assembled result matches aggregator semantics
- `mork_fold_both_outcomes_consistent`: binary outcomes + aggregator consistency
- `nary_fold_all_outcomes_consistent`: N-ary outcomes + aggregator consistency
- `naryFoldPicks_implies_consistent`: NaryFoldPicksSubResult → AggregatorConsistent
- `applyAggregator_implies_consistent`: applyAggregator = some assembled → AggregatorConsistent
- `aggregatorConsistent_exists`: AggregatorConsistent is satisfiable for non-empty subResults
- `instDecidableAggregatorConsistent`: AggregatorConsistent is decidable
- `cmatchAtom_eq_matchAtom`: computable cmatchAtom = spec matchAtom (exact, unconditional)
- `capplySink_add_toFinset`: list-level add sink = Finset add sink (via toFinset)
- `capplySink_head_toFinset`: list-level head sink = Finset head sink (via toFinset)
- `capplySink_remove_toFinset`: list-level remove sink = Finset erase (under Nodup)
- `capplySinks_toFinset_no_remove`: sinks composition = applySinks (no-remove templates)
- `capplySinks_toFinset_safe`: sinks composition = applySinks (NodupSafe templates)
- `matchAtom_extends`: matchAtom preserves existing substitution bindings
- `matchOneInSpace_mem`: matchAtom success → membership in matchOneInSpace result
- `cmatchPattern_consumed_subset`: consumed atoms belong to input space
- `cmatchPattern_subst_extends`: output substitution extends input substitution
- `cmatchPattern_toFinset_sound`: cmatchPattern result ∈ matchPattern (forward soundness)
- `cfireRule_toFinset_sound`: cfireRule result.toFinset ∈ fireRule (forward soundness)
- `matchPattern_toFinset_complete`: matchPattern result has cmatchPattern preimage (backward)
- `fireRule_toFinset_complete`: fireRule result has cfireRule preimage (backward)
- `lexLt_asymm`, `lexLt_trans`, `lexLt_eq_of_not_both`: structural properties of lexLt
- `lexLt_irrefl`: lexLt is irreflexive
- `lexLt_iff_lex`: lexLt agrees with Mathlib's `List.Lex (· < ·)` (bridge to LinearOrder)
- `selectNextExec_perm`: selectNextExec is permutation-invariant (under KeyInjective)
- `cExecFacts_perm_execFacts`: computable ↔ spec exec-fact extraction (under Nodup)
- `cWorkQueueStep_selectExec_eq`: scheduler selects same exec fact (Nodup + KeyInjective)
- `extractExecFact_atom`: extractExecFact preserves the original atom in .atom field
- `extractExecFact_injective`: two atoms extracting to the same ExecFact must be identical
- `consumeExec_card_lt`: consuming exec fact strictly decreases space cardinality
- `applySinks_removeOnly_card_le`: remove-only templates cannot increase cardinality
- `cConsumeExec_toFinset`: list erase = Finset erase under Nodup
- `cReadCopy_toFinset`: computable read copy = spec read copy under Nodup
- `cFireExecFact_toFinset_single`: fireExecFact correspondence (single-match case)
- `cFireExecFact_toFinset_empty`: fireExecFact correspondence (no-match case)
- `cFireExecFact_toFinset`: fireExecFact correspondence (general multi-match case)
- `foldl_capplySinks_toFinset`: foldl correspondence for multi-match sink application
- `FoldNodupSafe`: NodupSafe at every step of the outer foldl over match results
- `cWorkQueueStep_toFinset`: work-queue step correspondence (computable = spec)
- `cWorkQueueRunN_toFinset`: bounded-run correspondence (computable = spec under invariant)
- `cSourceWorkQueueStep_GSLT_adequate`: native source-aware step → authored GSLT step
- `cSourceWorkQueueRunN_GSLT_adequate`: native exact-fuel run → GSLT reachability
- `WorkQueueInvariant`: per-step invariant bundle (Nodup + KeyInjective + firing alignment)
- `CReachable`: computable reachability predicate for bounded-run
- `fireExecFact_readCopy_simplify`: fireExecFact simplifies when exec fact is in space
- `fireSourceRule_compat`: source-aware firing on compat-mode = regular fireRule
- `cfireSourceRule_compat_eq`: computable source-aware compat = cfireRule
- `extractSourceExecFact`: parses both `(, ...)` compat and `(I ...)` explicit modes
- `SourceExecFact.toExecFact?`: converts compat-mode source facts to standard ExecFact
- `fireSourceExecFact`: spec-level source-aware firing via matchInputSpec
- `cFireSourceExecFact`: computable source-aware firing via cmatchInputSpec
- `canary10_source_fire`: explicit BTM source fires against `(data hello)` → `(found hello)`
- `canary10_eq_fire`: `==` constraint fires when lookup succeeds
- `canary10_eq_nomatch`: `==` constraint no-op when lookup fails
- `source_test6_neq`: `!=` constraint excludes target, matches remaining
- `source_test7_neq_nomatch`: `!=` with no remaining matches → no fire
- `source_test8_neq_multi`: `!=` with multiple remaining → non-deterministic results
- `canary11_neq_fire`: `!=` through cFireSourceExecFact pipeline
- `canary11_neq_nomatch`: `!=` no remaining match through pipeline
- `canary11_extraction_parses`: extractSourceExecFact parses `!=` atoms
- `cmatchSourceFactor_sound`: cmatchSourceFactor → matchSourceFactor (forward soundness)
- `cmatchSourceFactors_toFinset_sound`: cmatchSourceFactors → matchSourceFactors (forward)
- `cmatchInputSpec_toFinset_sound`: cmatchInputSpec → matchInputSpec (forward soundness)
- `cfireSourceRule_toFinset_sound`: cfireSourceRule → fireSourceRule (forward soundness)
- `cmatchSourceFactor_complete`: matchSourceFactor → cmatchSourceFactor (backward)
- `cmatchSourceFactors_toFinset_complete`: matchSourceFactors → cmatchSourceFactors (backward)
- `cmatchInputSpec_toFinset_complete`: matchInputSpec → cmatchInputSpec (backward)
- `fireSourceRule_toFinset_complete`: fireSourceRule → cfireSourceRule (backward)
- `applySinks_intArithTemplate`: decoded integer arithmetic lowers to a single core add effect
- `applySinks_floatArithTemplate`: decoded float arithmetic lowers to a single core add effect
- `matchInputSpec_cmpSourceInput`: `CmpSource` is the explicit core source seam `eqConstraint` / `neqConstraint`
- `cfireSourceRule_cmpSourceRule_noGuards`: single comparison-source rules execute through the existing computable source-rule pipeline
- `liveInsert_then_exactMatch`: explicit live insertion makes an exact live match immediately visible
- `liveRemove_then_noExactMatch`: absent atoms do not survive exact live matching
- `liveRun_steps_le_fuel`: live scheduler execution is bounded by its fuel
- `pathSupport_readPrefixRestrict_eq_restrictPaths`: read-side `prefix-restrict` is a structural export law
- `rootedSnapshotExport_lookup_nil`: rooted snapshot export preserves the focused root value
- `structuralSubtrieExport_lookup_nil`: structural subtrie export clears the focused root value
- `fireExecFact_card_lt_of_removeOnly`: remove-only templates → cardinality strictly decreases
- `workQueueRunN_steps_le_fuel`: scheduler takes at most `fuel` steps
- `upstream_zero_differs_from_exact_fuel`: upstream post-check fuel is observably distinct
- `count_support_invariant`, `sum_support_invariant`: native reductions factor through support
- `selectFirst_not_support_invariant`: authored first choice does not factor through support
- `explicit_count_spaces_injective`: explicit counts remain representable as atoms
- `no_faithful_bag_choice_encoding_into_support_union`: faithful bag choice cannot retain native union
- `validExecGSLT_step_iff`: the MM2 GSLT rewrite is exactly one valid queue step
- `validExecControlReification`: pending work and scheduler configuration are language-visible
- `runReport_completed_normalForm`: completion certifies quiescence
- `runReport_expired_has_step`: expiration certifies retained pending work
- `unsupported_exec_separates_source_profiles`: inert and consuming boundaries differ explicitly
- `malformed_exec_canary_separates`: a concrete malformed exec distinguishes those profiles
- `sourceExecStepNativeClaim_meaning_iff_step`: generated OSLF/CertificateGSLT claim means one MM2 step
- `cSourceContractFor_refines`: list source provider realizes its authored contract
- `cSinkContractFor_refines`: staged list sink realizes its authored batch contract
- `evaluationStatus_not_factors_through_answers`: Zero answer bags erase runner status
- `no_authoredMM2_embedding_into_bareZero`: MM2 generated work cannot embed directly into one-step Zero

## Spec status

This is a layered MM2/MORK formalization. It distinguishes the raw valid-exec
work queue, pinned implementation behavior, and authored hosted protocols.
The spec currently covers:
- A support-valued raw MM2 space and an indexed deterministic work-queue family
- Exact-fuel execution plus the current upstream post-check behavior
- The three-phase protocol as an authored hosted convention, not a raw MM2 law
- Binary non-determinism (the fundamental quantum-inspired structure)
- Connection to MQ-calculus COMM (the theoretical foundation)
- Work-queue firing with read-copy semantics on the formalized valid-exec fragment
- Support-staged count and sum matching upstream reduction-sink staging
- Authored fold aggregation (`selectAll`, `selectFirst`) kept distinct from raw sinks
- Batch `head` / `tail` reductions over staged support in compact-expression order
- Sink persistence through pipelines (`applySinks_mem_of_mem`)
- Ground self-respawn (`canary8_ground_self_respawn`)
- Source-side input: `(I (BTM pat) (== pat witness) ...)` with `SourceFactor`/`InputSpec`
- Source-side conformance: 5 kernel-checked `rfl` tests for BTM and `==` constraints
- Strict source-side decoding: unknown factors and sinks reject the whole directive
- Source-side GSLTs for open-world inertness and remove-before-interpret consumption
- Automatic OSLF native types and CertificateGSLT claims generated from each GSLT member
- Catalog-indexed provider declarations, typed oracle projections, and
  observation-indexed native source/sink realization laws
- Arithmetic/comparison extension interface: int/float sink lowerings and explicit `CmpSource` packaging

Explicit current boundaries:
- The active scheduler uses the full exact compact-expression key.  The older
  `PathMapByteOrderRefinement.lean` remains a theorem about a historical
  location projection and must not be cited as full-directive adequacy
- Remove-before-interpret is modeled relative to the strict Lean decoder and
  separated from the open-world member; full upstream source/sink factory
  classification remains a declared realization obligation

Details likely to change in future MORK versions (not formalized here):
- Exact sub-query naming convention (`(sub-k qid)` format)
- MAX_DEPTH constant (32 by default)
- Sink priority refinements (streaming/partial-fold)
- MM2 bytecode instruction set extensions

Canaries in `ThreePhaseExec.lean` pin the authored hosted protocol. They are not
claims that upstream MORK itself gives semantic meaning to those phase bands.
-/
