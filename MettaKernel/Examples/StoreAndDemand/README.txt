Store and demand contracts
==========================

Classification
--------------
The .metta and .expected files are calibration fixtures. replay.py is an
untrusted source adapter that launches an explicitly selected executable and
compares exact output. cases.json associates observations with relevant Lean
contracts; it is not a source-to-theorem codec or a C-correspondence certificate.

The Lean entry is:
  lean/mettapedia/Mettapedia/Languages/MeTTa/StoreAndDemand/Contracts.lean
Its Audit.lean checks every declaration in the two new contract namespaces,
including generated helpers, against the standard axiom allowlist.

Contract map
------------
Lean names below are relative to Mettapedia.Languages.MeTTa.StoreAndDemand,
except for Machines/StoreAndDemand/FirstAnswer, which is generic cursor machinery.

Operation / law                    Main Lean contract                     Positive / boundary fixtures
---------------------------------  -------------------------------------  -----------------------------------------------
Add one supplied atom              StoreEffects.add_is_make               add-one / add-comma-is-one-atom
Remove all completed matches       StoreEffects.removeAll_occurrence_projection
                                                                          remove-multiplicity / remove-miss
Scoped, independent row unifiers   PeTTaSelection.survivors_selection     remove-independent-bindings / remove-open-row
Remove one occurrence              StoreEffects.removeOne_occurrence_projection
                                                                          remove-multiplicity / remove-miss
Two takes need two copies          StoreEffects.double_take_iff           double-accepted / double-refused
Read plus take needs two copies    StoreEffects.read_take_iff             read-take-accepted / read-take-refused
Take conservation                 StoreEffects.take_count_conservation   accepted/refused take cases
Count already split instances     StoreEffects.route_count_is_growth     destination-count / destination-empty
Earlier effects survive refusal   ValidationReuse.checked_refusal        routing-error-retains-take / source-error-retains-earlier-effect
Stable dependency reuse           ValidationReuse.direct_after_preparation
                                                                          unrelated-write-preserves-enabling / selected-value-invalidated-before-first
Independent batch reuse           ValidationReuse.independent_batch_direct
                                                                          independent-writers-both-fire / disjoint-takes-absence-interference
Read and query dependencies       ValidationReuse.Agreement.enabled_iff  lost-keep-stops-later-firing / uniqueness-spoiled-by-addition
Conservative revision rejection   ValidationReuse.Controls.whole_store_validation_rejects_independent
                                                                          independent-writers-both-fire / disjoint-takes-absence-interference
Adjacent effect fusion            ValidationReuse.adjacent_fusion         sequential-adds / fused-makes / routing-error-retains-take
Optional, unobserved records       RunReceipts.erase_unobserved_receipts  record-absent / record-unobserved
Records cannot always be erased   RunReceipts.observed_receipts_cannot_be_erased
                                                                          record-observed / record-disabled-observed
First answer differs from firing  Demand.silent_prefix                    answerless-firing-prefix / once-stops-later-firing
Collapse of first demand          Demand.collapse_once                    once-stops-later-firing / empty-first-producer
Required operand preparation      Demand.preparation_effects_precede_first
                                                                          operand-evaluation-boundary / generation-effect-invalidates-first
Order can affect first result     Demand.Controls.bag_equality_does_not_preserve_first
                                                                          once-order-forward / once-order-reverse
Complete bags can hide effects    Demand.Controls.complete_bag_does_not_preserve_effects
                                                                          ordered-effects-forward / ordered-effects-reverse
Duplicate answers survive         Demand.pure_complete_bag               collapse-keeps-duplicates
HE errors remain values           Demand.he_all_errors_keep_multiplicity he-errors-are-values / he-success-displaces-error
PeTTa raises stop continuation     Demand.petta_raise_stops_sequence       petta-raise-stops-tail
Export before closing             Demand.publish_then_close              answer-survives-producer-scope / once-stops-later-firing
Unused storage, no world rollback  Demand.close_reclaims_unused_without_rollback
                                                                          answer-survives-producer-scope / answerless-firing-prefix

Additional machine laws
-----------------------
Machines/StoreAndDemand/FirstAnswer.lean instantiates the existing indexed
cursor protocol. first_after_progress retains the state reached by an arbitrary
finite prefix of nonanswering requests. answer_stops and no_requests_after_answer
do not invoke the unused tail. endless_progress_pauses covers a producer that
never answers. interruption_is_not_exhaustion distinguishes those outcomes.
These request counts are not a specification of native instruction counts or
the exact cutoffs of --fuel.

SearchCursor.first_refines_once connects that consumer to the existing
LibTransform.Search.once observation. RunReceipts.spent_append and spent_prefix_le
reuse the general Step.Run account rather than introducing another cost algebra.

Interpretation boundaries
-------------------------
The store primitive takes a completed selection. It does not turn failed or
interrupted matching into an empty selection. PeTTaSelection uses the existing
renamed per-row unifier, including open stored rows. Its theorem does not import
the older Unifying.removeRows return-value policy: current CeTTa's expression
removal answers whether a row was removed.

The occurrence laws permit reuse only for the observations they represent.
Permissions, callbacks or shared knowledge outside an adapter's occurrence state
need their own stability evidence. A whole-space epoch is not a concurrency
protocol, and the first firing is not inherently stable.

Fusion preserves the stated store/result observation under its precondition.
It does not merge an ordered surface firing's error boundaries. In particular,
HE's completed take remains visible when a later destination write fails.

Receipt erasure is proved for observers that read the semantic state, not the
optional record. The record-* fixtures use authored logging to expose that
observation distinction; they do not test an unimplemented native receipt switch.
Likewise, source fixtures observe retained values and skipped effects, while the
heap-reclamation law uses the existing ownership graph. They are not memory-growth
or native finalizer proofs.

The generation-effect-invalidates-first fixture is deliberately dialect-specific:
its PeTTa result is (result (yes) ()), whereas HE returns (result () ()). Both were
checked against their authored transform references. It is an evaluation-boundary
characterization, not a universal rule about when source-level let code runs.
The operand-evaluation-boundary fixture also retains HE's required eager work;
first demand is not permission to move operand preparation.

Run
---
From the repository root, supply the executable to qualify:

  python3 MettaKernel/Examples/StoreAndDemand/replay.py --binary "$CETTA_BIN"

The independent authored PeTTa transform lane uses the default PeTTa profile,
imports lib_transform_swi and refuses a run with native transform traces:

  python3 MettaKernel/Examples/StoreAndDemand/replay.py --binary "$CETTA_BIN" --petta-reference

Use --case NAME to select a reproduction, or --report FILE to retain all outputs
and the executable/source/expected-output hashes. Neither command builds CeTTa.
The reference lane is independent for transform, not for every primitive of the
host evaluator. HE extended-only control forms cannot be tested by pretending
that plain HE interprets them.

All observations must pass to claim that a runtime meets these fixtures. Known
runtime failures remain failures; expected files are not regenerated from the
runtime under test. The contract package and the runtime's qualification are
separate deliverables.
