# GSLT Formalization Manifest
# Auto-maintained by Oruži at commit time
# Format: FILE | DECL_NAME | KIND | PAPER_REF | STATUS
# KIND: def/thm/struct/inductive/class
# STATUS: ✅ (proven) | 🔶 (sorry) | 📐 (definition only)
# PAPER_REF: Meredith CCC 2026 section

## ═══════════════════════════════════════════════════
## Core/GSLT.lean — §2 Graph-enriched Lawvere Theories
## ═══════════════════════════════════════════════════

Core/GSLT.lean | GSLT | struct | §2 Def 2.1 | 📐
Core/GSLT.lean | GSLT.Step | field | §2 | 📐
Core/GSLT.lean | GSLT.MultiStep | inductive | §2 | 📐
Core/GSLT.lean | GSLT.IsNormalForm | def | §2 | 📐
Core/GSLT.lean | GSLT.IsRedex | def | §2 | 📐
Core/GSLT.lean | GSLT.Bisimilar | def | §2 Def 2.2 | 📐
Core/GSLT.lean | GSLT.bisimilar_refl | thm | §2 | ✅
Core/GSLT.lean | GSLT.bisimilar_symm | thm | §2 | ✅
Core/GSLT.lean | GSLT.bisimilar_trans | thm | §2 | ✅
Core/GSLT.lean | GSLTMorphism | struct | §2 Def 2.3 | 📐
Core/GSLT.lean | GSLTMorphism.comp | def | §2 | 📐
Core/GSLT.lean | GSLTMorphism.id | def | §2 | 📐
Core/GSLT.lean | morphism_preserves_multistep | thm | §2 | ✅
Core/GSLT.lean | morphism_preserves_bisimilar | thm | §2 | ✅

## ═══════════════════════════════════════════════════
## Causality/Trace.lean — §3 Traces & Reversibility
## ═══════════════════════════════════════════════════

Causality/Trace.lean | Trace | inductive | §3 Def 3.1 | 📐
Causality/Trace.lean | Trace.length | def | §3 | 📐
Causality/Trace.lean | Trace.append | def | §3 | 📐
Causality/Trace.lean | RewritePath | inductive | §3 | 📐
Causality/Trace.lean | RewritePath.length | def | §3 | 📐
Causality/Trace.lean | RewritePath.toTrace | def | §3 | 📐
Causality/Trace.lean | RewritePath.toTrace_length | thm | §3 | ✅
Causality/Trace.lean | ReversibleEnvelope | struct | §3 Def 3.2 | 📐
Causality/Trace.lean | ReversibleEnvelope.eta | field | §3 | 📐
Causality/Trace.lean | ReversibleEnvelope.pi | field | §3 | 📐
Causality/Trace.lean | eta_pi_roundtrip | thm | §3 Prop 3.1 | ✅
Causality/Trace.lean | pi_eta_roundtrip | thm | §3 Prop 3.1 | ✅
Causality/Trace.lean | CausalTrace | struct | §3 Def 3.3 | 📐
Causality/Trace.lean | causalTrace_monotone | thm | §3 | ✅

## ═══════════════════════════════════════════════════
## Causality/SyncTree.lean — §4 Synchronization Trees
## ═══════════════════════════════════════════════════

Causality/SyncTree.lean | ClosedEdge | struct | §4 Def 4.1 | 📐
Causality/SyncTree.lean | closedTree_trivial_iff_normalForm | thm | §4 Rmk | ✅
Causality/SyncTree.lean | OpenEdge | struct | §4 Def 4.2 | 📐
Causality/SyncTree.lean | OpenReachable | inductive | §4 | 📐
Causality/SyncTree.lean | autonomous_is_open_step | thm | §4 | ✅
Causality/SyncTree.lean | closedReachable_implies_openReachable | thm | §4 Prop 4.1 | ✅
Causality/SyncTree.lean | AutonomousCausalOrder | def | §4 Def 4.3 | 📐
Causality/SyncTree.lean | InteractiveCausalOrder | def | §4 Def 4.3 | 📐
Causality/SyncTree.lean | autonomousCausalOrder_refl | thm | §4 | ✅
Causality/SyncTree.lean | interactiveCausalOrder_refl | thm | §4 | ✅
Causality/SyncTree.lean | autonomousCausalOrder_trans | thm | §4 | ✅
Causality/SyncTree.lean | interactiveCausalOrder_trans | thm | §4 | ✅
Causality/SyncTree.lean | autonomousCausal_embeds_interactive | thm | §4 Prop 4.1 | ✅
Causality/SyncTree.lean | InteractivePath | inductive | §4 Def 4.4 | 📐
Causality/SyncTree.lean | InteractivePath.length | def | §4 Def 4.4 | 📐
Causality/SyncTree.lean | RewritePath.toInteractive | def | §4 | 📐
Causality/SyncTree.lean | RewritePath.toInteractive_length | thm | §4 | ✅
Causality/SyncTree.lean | IsPureInterface | def | §4 Rmk 4.1 | 📐
Causality/SyncTree.lean | IsAutonomouslyActive | def | §4 | 📐

## ═══════════════════════════════════════════════════
## Logic/ContextHML.lean — §5 LTS & Context-Decorated HML
## ═══════════════════════════════════════════════════

Logic/ContextHML.lean | GSLTContext | class | §5 Def 5.1 | 📐
Logic/ContextHML.lean | GSLTContext.id | def | §5 | 📐
Logic/ContextHML.lean | GSLTContext.comp | def | §5 | 📐
Logic/ContextHML.lean | GSLT.contextStep | def | §5 | 📐
Logic/ContextHML.lean | HMLFormula | inductive | §5 Def 5.2 | 📐
Logic/ContextHML.lean | satisfies | def | §5 | 📐
Logic/ContextHML.lean | hmlEquiv | def | §5 | 📐
Logic/ContextHML.lean | hmlEquiv_refl | thm | §5 | ✅
Logic/ContextHML.lean | hmlEquiv_symm | thm | §5 | ✅
Logic/ContextHML.lean | hmlEquiv_trans | thm | §5 | ✅
Logic/ContextHML.lean | hmlSetoid | def | §5 | 📐
Logic/ContextHML.lean | GSLT.adequacy_sound | def | §5 Thm 5.1 | 📐
Logic/ContextHML.lean | GSLT.adequacy_complete | def | §5 Thm 5.1 | 📐
Logic/ContextHML.lean | GSLT.adequacy | def | §5 Thm 5.1 | 📐

## ═══════════════════════════════════════════════════
## Dynamics/WeightCost.lean — §§6-7 Weights & Costs
## ═══════════════════════════════════════════════════

Dynamics/WeightCost.lean | WeightStructure | class | §6 Def 6.1 | 📐
Dynamics/WeightCost.lean | WeightedGSLT | struct | §6 Def 6.2 | 📐
Dynamics/WeightCost.lean | WeightedGSLT.weightedStep | def | §6 | 📐
Dynamics/WeightCost.lean | WeightedGSLT.totalWeight | def | §6 | 📐
Dynamics/WeightCost.lean | CostMap | struct | §7 Def 7.1 | 📐
Dynamics/WeightCost.lean | VectorialAccount | struct | §7 Def 7.2 | 📐
Dynamics/WeightCost.lean | VectorialAccount.debit | def | §7 | 📐
Dynamics/WeightCost.lean | VectorialAccount.solvent | def | §7 | 📐
Dynamics/WeightCost.lean | debit_monotone | thm | §7 Prop 7.1 | ✅
Dynamics/WeightCost.lean | debit_preserves_insolvency | thm | §7 | ✅
Dynamics/WeightCost.lean | ResourceBoundedGSLT | struct | §7 | 📐

## ═══════════════════════════════════════════════════
## Dynamics/ExtendedHML.lean — §8 Extended HML
## ═══════════════════════════════════════════════════

Dynamics/ExtendedHML.lean | ExtHMLFormula | inductive | §8 Def 8.1 | 📐
Dynamics/ExtendedHML.lean | ExtHMLFormula.satisfies | def | §8 | 📐
Dynamics/ExtendedHML.lean | satisfies_top | thm | §8 | ✅
Dynamics/ExtendedHML.lean | satisfies_conj_comm | thm | §8 | ✅
Dynamics/ExtendedHML.lean | weightBisimilar | def | §8 Def 8.2 | 📐
Dynamics/ExtendedHML.lean | weightBisimilar_refl | thm | §8 | ✅
Dynamics/ExtendedHML.lean | weightBisimilar_symm | thm | §8 | ✅
Dynamics/ExtendedHML.lean | weightBisimilar_trans | thm | §8 | ✅
Dynamics/ExtendedHML.lean | weightBisimilar_setoid | def | §8 | 📐
Dynamics/ExtendedHML.lean | weightBisim_refines_bisim | thm | §8 Prop 8.1 | ✅

## ═══════════════════════════════════════════════════
## Dynamics/PathIntegral.lean — §9 Finite-Support Path Integrals
## ═══════════════════════════════════════════════════

Dynamics/PathIntegral.lean | AmplitudeWeightedGSLT | def | §9 Def 9.1 | 📐
Dynamics/PathIntegral.lean | rewritePathAppend | def | §9 | 📐
Dynamics/PathIntegral.lean | rewritePathLength_append | thm | §9 | ✅
Dynamics/PathIntegral.lean | transitionAmplitude | def | §9 Def 9.2 | 📐
Dynamics/PathIntegral.lean | pathAmplitude_append | thm | §9 | ✅
Dynamics/PathIntegral.lean | transitionAmplitude_empty | thm | §9 | ✅
Dynamics/PathIntegral.lean | transitionAmplitude_singleton | thm | §9 | ✅
Dynamics/PathIntegral.lean | transitionAmplitude_union | thm | §9 | ✅

## ═══════════════════════════════════════════════════
## Synthesis/MainConservation.lean — §10 Quantum Reversible Synthesis
## ═══════════════════════════════════════════════════

Synthesis/MainConservation.lean | QuantumTraceEntry | struct | §10 Constr 10.1 | 📐
Synthesis/MainConservation.lean | QuantumState | struct | §10 Constr 10.1 | 📐
Synthesis/MainConservation.lean | QuantumState.initial | def | §10 | 📐
Synthesis/MainConservation.lean | QuantumState.cptTransform | def | §10 Thm 10.1(iii) | 📐
Synthesis/MainConservation.lean | QuantumState.cptTransform_involutive | thm | §10 | ✅
Synthesis/MainConservation.lean | QuantumState.cptTransform_traceAccount | thm | §10(iii) | ✅
Synthesis/MainConservation.lean | QuantumState.cptTransform_conservedBalance | thm | §10(iii) | ✅
Synthesis/MainConservation.lean | traceAccount | def | §7/§10 | 📐
Synthesis/MainConservation.lean | traceAccount_map_cptConjugate | thm | §10(iii) | ✅
Synthesis/MainConservation.lean | traceAccount_append | thm | §10(iii) | ✅
Synthesis/MainConservation.lean | traceAccount_reverse | thm | §10(iii) | ✅
Synthesis/MainConservation.lean | conservedBalance | def | §10 | 📐
Synthesis/MainConservation.lean | netAccountChange | def | §7/§10 | 📐
Synthesis/MainConservation.lean | ClosedRewriteCycle | def | §7/§10 | 📐
Synthesis/MainConservation.lean | QuantumStep | inductive | §10 Constr 10.1 | 📐
Synthesis/MainConservation.lean | QuantumStepStar | inductive | §10 | 📐
Synthesis/MainConservation.lean | QuantumStepStar.trans | thm | §10 | ✅
Synthesis/MainConservation.lean | conservedBalance_step | thm | §10 | ✅
Synthesis/MainConservation.lean | conservedBalance_stepStar | thm | §10 | ✅
Synthesis/MainConservation.lean | closedCycle_account_eq | thm | §7 Thm 7.1 / §10(i) | ✅
Synthesis/MainConservation.lean | netAccountChange_eq_zero_of_closedCycle | thm | §7 Thm 7.1 / §10(i) | ✅
Synthesis/MainConservation.lean | resourceConservation_initialClosedPath | thm | §7 Thm 7.1 | ✅
Synthesis/MainConservation.lean | transitionProbability | def | §9 Def 9.2 / §10(ii) | 📐
Synthesis/MainConservation.lean | oneStepTransitionProbability | def | §10(ii) | 📐
Synthesis/MainConservation.lean | oneStepTransitionProbability_eq_normSq | thm | §10(ii) | ✅
Synthesis/MainConservation.lean | LocalUnitaryWitness | struct | §10(ii) | 📐
Synthesis/MainConservation.lean | oneStepProbabilityConservation | thm | §10(ii) | ✅
Synthesis/MainConservation.lean | PathProbabilityNormalization | struct | §10(ii) | 📐
Synthesis/MainConservation.lean | transitionProbabilityConservation | thm | §10(ii) | ✅
Synthesis/MainConservation.lean | WeightMap.cptConjugate | def | §10(iii) | 📐
Synthesis/MainConservation.lean | CPTSymmetric | struct | §10(iii) | 📐
Synthesis/MainConservation.lean | mainConservation_resource | thm | §10 Thm 10.1(i) | ✅
Synthesis/MainConservation.lean | mainConservation_probability | thm | §10 Thm 10.1(ii) interface | ✅
Synthesis/MainConservation.lean | mainConservation_cpt | thm | §10 Thm 10.1(iii) interface | ✅

## ═══════════════════════════════════════════════════
## Life/AssemblyTheory.lean — §23 Assembly Depth and Copy Number
## ═══════════════════════════════════════════════════

Life/AssemblyTheory.lean | AssemblyPath | inductive | §23.1 | 📐
Life/AssemblyTheory.lean | AssemblyPath.length | def | §23.1 | 📐
Life/AssemblyTheory.lean | AssemblyWitness | struct | §23.1 | 📐
Life/AssemblyTheory.lean | Assemblable | def | §23.1 | 📐
Life/AssemblyTheory.lean | assemblyDepths | def | §23.1 | 📐
Life/AssemblyTheory.lean | assemblyIndex | def | §23 Prop 23.1 | 📐
Life/AssemblyTheory.lean | assemblyDepths_nonempty | thm | §23.1 | ✅
Life/AssemblyTheory.lean | assemblyIndex_mem | thm | §23 Prop 23.1 | ✅
Life/AssemblyTheory.lean | assemblyIndex_attained | thm | §23 Prop 23.1 | ✅
Life/AssemblyTheory.lean | assemblyIndex_le_of_witness | thm | §23 Prop 23.1 | ✅
Life/AssemblyTheory.lean | assemblyIndex_eq_of_minimal | thm | §23 Prop 23.1 | ✅
Life/AssemblyTheory.lean | elementaryWitness | def | §23 Def 23.1 | 📐
Life/AssemblyTheory.lean | elementary_assemblable | thm | §23 Def 23.1 | ✅
Life/AssemblyTheory.lean | assemblyIndex_eq_zero_of_mem | thm | §23 Prop 23.1 | ✅
Life/AssemblyTheory.lean | Namespace | struct | §23.3 | 📐
Life/AssemblyTheory.lean | Namespace.copyNumber | def | §23 Def 23.4 | 📐
Life/AssemblyTheory.lean | Namespace.copyNumber_empty | thm | §23 Def 23.4 | ✅
Life/AssemblyTheory.lean | Namespace.copyNumber_le_card | thm | §23 Def 23.4 | ✅
Life/AssemblyTheory.lean | Namespace.copyNumber_eq_of_bisimilar | thm | §23.4 | ✅
Life/AssemblyTheory.lean | Namespace.copyNumber_eq_card_of_forall | thm | §23.4 | ✅

## ═══════════════════════════════════════════════════
## Life/ReplicationFixedPoint.lean — §24 Replication Fixed-Point Kernel
## ═══════════════════════════════════════════════════

Life/ReplicationFixedPoint.lean | replicate | def | §24 | 📐
Life/ReplicationFixedPoint.lean | replicationBody | def | §24 | 📐
Life/ReplicationFixedPoint.lean | replicationPrefix | def | §24 | 📐
Life/ReplicationFixedPoint.lean | replicationPrefix_one | thm | §24 | ✅
Life/ReplicationFixedPoint.lean | replicate_fixedPointKernel | def | §24 | 📐
Life/ReplicationFixedPoint.lean | replicationPrefix_step | def | §24 | 📐
Life/ReplicationFixedPoint.lean | replicate_unfolds_to_prefix | def | §24 | 📐
Life/ReplicationFixedPoint.lean | replicate_fixedPointKernel_nonempty | thm | §24 | ✅
Life/ReplicationFixedPoint.lean | replicationPrefix_step_nonempty | thm | §24 | ✅
Life/ReplicationFixedPoint.lean | replicate_unfolds_to_prefix_nonempty | thm | §24 | ✅

## ═══════════════════════════════════════════════════
## COVERAGE SUMMARY
## ═══════════════════════════════════════════════════
## Paper sections covered: §2, §3, §4, §5, §6, §7, §8, §9, §10 (resource kernel), §23 (assembly/copy-number kernel), §24 (derived replication kernel)
## Paper sections remaining: full §10(ii)–(iii) derivations, Part II epistemic theorems, the pure quote/COMM concurrent-Y part of §24, §25–§26, and later speculative layers
## Total definitions: ~80
## Total theorems proven (✅): ~61
## Total sorry: 0
## Last updated: 2026-03-28
