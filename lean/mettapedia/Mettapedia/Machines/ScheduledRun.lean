import Mettapedia.Machines.ScheduledRun.LocalControls
import Mettapedia.Machines.ScheduledRun.BoundedClock

/-!
# Scheduled runs, live-return certificates and period-reset detection

The theory is language-independent and therefore lives under `Machines`.
`next : S → List S` is a fixed, ordered successor function. A configuration
must retain every component affecting its future: changing the program,
external world or controller outside `S` is not licensed by state equality.
Canonical and rotating choice are explicit instances, not language defaults.

`run` has type `Nat → Option S`. A terminal state is visible at its ending
turn; subsequent observations are absent. `Nonterminating` is proved equivalent
to never reaching an ending turn. All return theorems compare present states,
not equality between stopped observations. Successor distinctness is unnecessary
for soundness; `Sharpness` uses it to prove the divisibility licence necessary.

## Live-return and detection contracts

All theorem names below are in `Mettapedia.Machines.ScheduledRun`, with the
concrete controls in its `Controls` namespace.

| Item | Theorem | Exact content |
| --- | --- | --- |
| 1 | `rotating_return_periodic` | A live return at `first < last`, with every intervening arity dividing `last-first`, gives nontermination and periodicity from `first` with that positive period. |
| 2 | `return_mod_lcm_periodic` | Equal live states and congruent turns modulo the segment LCM imply item 1's conclusion. `return_mod_prefix_lcm_periodic` uses the whole preceding prefix. `return_mod_common_period` accepts any common multiple. |
| 3 | `canonical_return_periodic` | For canonical choice a live state return alone suffices. |
| 4 | `Controls.rotating_revisit_not_infinite` | Waiting at turns 0 and 1 can be followed by waking and ending at turn 2. |
| 5 | `Controls.stale_phase_not_infinite` | The five-state period-change system revisits state 2 at turns 1 and 4 but ends at turn 7. |
| 6 | `finite_infinite_detected` | Every infinite rotating run with finite visited states repeats a state/phase pair modulo the LCM of visited arities. `finite_reachable_infinite_detected` supplies the requested reachable-state hypothesis. |
| 7 | `finite_run_never_claimed` | An ending run has no licensed common-period return pair. |
| 8 | `finite_monitor_reports_iff`, `finite_eventually_reports_iff` | The actual prefix-record procedure reports eventually exactly on nonterminating runs with finite visited states. `claimsAt_sound` needs no finiteness assumption. |

The finite-state hypothesis is essential: `Controls.infinite_growth_is_not_detected`
has an infinite one-successor run and no repeated configuration.
`finite_schedule_phase_detected` gives the phase-pair pigeonhole result for
arbitrary schedules too, but it does not license an LCM clock for an arbitrary
controller. `Controls.bounded_picks_alone_do_not_license_the_lcm_clock` is the
counterexample; the rotating/canonical licences must not be omitted.

## Shared-runner and fixture correspondence

`Mode.schedule` and `step` model `src/runner.h:run_pick`, guarded by a positive
successor count. `updatePeriod`/`prefixPeriod` model the mathematical value of
`run_period` before bounded overflow. `recordPrefix` and `claimsAt` model the
`run_visit` then `run_picks_among` order used by `run_path`: probe first, learn
the current arity afterwards, and clear old residue keys on a period change.
Canonical native code need not increment its counter: all its phases are zero
modulo one, as proved by `canonical_prefixPeriod`.

* `tests/tcalc/observe_run_wait.tcalc`: `canonical_waits_forever` and
  `canonical_monitor_claims`.
* `tests/tcalc/observe_run_rotating_wakes.tcalc`: `rotating_revisit_trace`,
  `rotating_revisit_not_infinite`, `rotating_wakes_never_claimed`.
* `tests/tcalc/observe_run_rotating_cycle.tcalc`: `rotating_cycle_is_infinite`,
  `rotating_cycle_lcm_certificate`, `finite_infinite_cycle_is_detected`,
  `rotating_monitor_claims`.
* `tests/tcalc/observe_run_rotating_period.tcalc`: `stale_phase_trace`,
  `stale_phase_not_infinite`, `stale_phase_never_claimed` and the failing
  `stale_residue_mutant_claims_finite_run`.
* `tests/tcalc/observe_run_rotating.tcalc`: `second_pick_distinguishes_the_schedules`
  isolates the different second choice underlying the fixture's deadlock.

These are mathematical graph instances and arithmetic contracts, not a proof
of either language-to-state decoding. Graph-cycle existence, scheduled-run
nontermination, fairness and producing useful observations remain different
properties.

## Local certificates and implementation boundaries

`checkLoop_sound_of_entry` certifies a finite cyclic word from its checked
edges, local clock licence and actual entry. `checkLoop_congr_next` transports
it across changes outside its ordered successor footprint; `checkLoop_reuse`
transports it across compatible local phases. A valid cycle elsewhere does
not establish that the current run enters it.

`localClaimAt` extracts candidates from actual intervals. Its conservative
portfolio with the global monitor is sound and retains finite-state
completeness. The candidate search is a prototype, not an asymptotic native
optimization claim. The transient-arity control proves a fourfold logical
detection-delay improvement without asserting a CPU or allocation speedup.

Natural-number completeness does not establish completeness with a finite
budget or an overflow-disabled period. `wrapping_prefix_agrees` and
`faithful_wrapped_prefix_claim` separate a faithful finite prefix from a
different wrapping future. A native refinement still owes state/ordering
decoding, probe-counter bounds, period overflow handling, hashing, storage,
allocation failure and budget behavior. No C implementation or default changes
are made by this package.
-/
