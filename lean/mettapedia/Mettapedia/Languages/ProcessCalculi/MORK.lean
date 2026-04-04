import Mettapedia.Languages.ProcessCalculi.MORK.MORKCommBridge
import Mettapedia.Languages.ProcessCalculi.MORK.PathMapBridge
import Mettapedia.Languages.ProcessCalculi.MORK.MatchSpec
import Mettapedia.Languages.ProcessCalculi.MORK.MeTTaILBridge
import Mettapedia.Languages.ProcessCalculi.MORK.WorkQueueExec
import Mettapedia.Languages.ProcessCalculi.MORK.WorkQueueOrder
import Mettapedia.Languages.ProcessCalculi.MORK.ThreePhaseRefinement
import Mettapedia.Languages.ProcessCalculi.MORK.Conformance
import Mettapedia.Languages.ProcessCalculi.MORK.ArithmeticExtension
import Mettapedia.Languages.ProcessCalculi.MORK.BridgeWorkspaceSurfaceRefinement
import Mettapedia.Languages.ProcessCalculi.MORK.BridgeCursorSurfaceRefinement
import Mettapedia.Languages.ProcessCalculi.MORK.BridgeAlgebraSurfaceRefinement
import Mettapedia.Languages.ProcessCalculi.MORK.PathOfAtomEncodingContract
import Mettapedia.Languages.ProcessCalculi.MORK.ExecutionBoundary

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
  ThreePhaseExec.lean  — Phase protocol: unfold (0–31), base (32–63), fold (64–95)
  WorkQueueOrder.lean      — Location-based exec ordering (atomKey, lexLt)
  WorkQueueExec.lean       — Faithful work-queue scheduler with read-copy semantics
  ThreePhaseRefinement.lean — Phase steps ↔ scheduler steps; applySubst_nil identity
  Conformance.lean         — 27 kernel-checked conformance + correspondence theorems
  ArithmeticExtension.lean — Int/float sink lowering + `CmpSource` packaging
  BridgeWorkspaceSurfaceRefinement.lean — Live insert/match/step workspace surface
  BridgeCursorSurfaceRefinement.lean — Bridge cursor API ↔ PathMap cursor semantics
  BridgeAlgebraSurfaceRefinement.lean — Live stepping vs structural export boundary
  PathOfAtomEncodingContract.lean — `path-of-atom` render/parse/traverse contract
  MORKCommBridge.lean  — Bridge: MORK binary fold ↔ MQ-calculus CommReduction
  PathMapBridge.lean   — Bridge: MORK space transitions ↔ PathMap lattice ops
  MatchSpec.lean       — Relational spec of atom matching (sound/complete fragment)
  MeTTaILBridge.lean   — Bridge: DeclReduces ↔ MORK fireRule; premise→source translation
  ExecutionBoundary.lean — Packages the proven morkTranslatable execution boundary
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
- `declReduces_implies_mork_fire`: DeclReduces → MORK fireRule fires (topRule case)
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
- `applyAggregator_count`: fold count aggregator returns list length as grounded int
- `applyAggregator_selectFirst`: fold selectFirst aggregator returns first sub-result
- `applyAggregator_count_perm`: count is permutation-invariant (match order irrelevant)
- `applyAggregator_sum_cons`: sum unfolds one step on cons list
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

## Spec status

This is a CORE MORK formalization capturing the stable 2026-02 semantics.
The spec intentionally covers:
- The three-phase protocol (stable)
- Binary non-determinism (the fundamental quantum-inspired structure)
- Connection to MQ-calculus COMM (the theoretical foundation)
- Work-queue scheduler with read-copy semantics (the actual runtime model)
- Conformance testing against `mork run` CLI (ground truth)
- Fold-level aggregation (`FoldAggregator`: selectAll, selectFirst, count, sum)
- Per-match `head` sink (idempotent add in Finset model)
- Sink persistence through pipelines (`applySinks_mem_of_mem`)
- Ground self-respawn (`canary8_ground_self_respawn`)
- Source-side input: `(I (BTM pat) (== pat witness) ...)` with `SourceFactor`/`InputSpec`
- Source-side conformance: 5 kernel-checked `rfl` tests for BTM and `==` constraints
- Source-side work-queue: 6 canary tests for extraction + firing through scheduler
- Arithmetic/comparison extension surface: int/float sink lowerings and explicit `CmpSource` packaging

Details likely to change in future MORK versions (NOT formalized here):
- Exact sub-query naming convention (`(sub-k qid)` format)
- MAX_DEPTH constant (32 by default)
- Sink priority refinements (streaming/partial-fold)
- MM2 bytecode instruction set extensions

**Canary theorems** in `MORKCommBridge.lean` and `ThreePhaseExec.lean` will
fail to compile if the stable invariants change.
-/
