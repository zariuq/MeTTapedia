import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsAnnotations
import Mettapedia.Machines.NativeCostLedger

/-!
# The native cost ledger as structure on annotations of runs

The native ledger (`Machines.NativeCostLedger`) keeps a chronological receipt of named
operations and several readouts of it. Each part is a piece of monoid structure, and each
says exactly what it keeps.

* **Named operation valuations** are a monoid hom out of the free monoid of native events
  (`nativeTotals`, `nativeTotals_ofList`): per-kind counts and total work.
* **The chronological receipt** is the free-monoid history itself. When every firing's native
  events are determined by the firing, its totals are a site annotation into a commutative
  monoid and respect the interchange squares (`receiptTotals_factor_static`), while the
  receipt itself does not (`AnnotationControls.history_not_traced`).
* **Compression** is a section of the expansion hom (`expand_compress`): it keeps totals,
  order and identities. It is not itself a hom of representations: compressing a
  concatenation merges runs across the boundary (`Controls.compression_merges_runs`).
* **Forgetting the chronology** is the hom to totals: it keeps totals and loses order
  (`Controls.forgetting_loses_order`). **An incomplete chronology** is a hom into the free
  monoid with an absorbing zero: one refusal to retain annihilates the readout
  (`retained_eq_zero_iff`), while the totals are not affected.
* **Overflow** is saturation, a hom from addition onto saturating addition
  (`boundedTotal_hom`). It forgets the excess (`Controls.saturation_forgets`) and is not
  additive (`Controls.saturation_not_additive`).
* **Nested-scope deduplication** reads the scope chain as a finite set: duplicate and permuted
  chains have the same targets (`scopeTargets_idempotent`, `scopeTargets_comm`), an
  idempotent merge. Without it a re-entered destination is charged twice
  (`NativeCostLedger.repeated_destination_double_charges`).
* **Worker joins** add work and take the scheduled critical path as span, the lax
  interchange of `AnnotatedRunsAnnotations.round_receipts`; a join of an incomplete child
  keeps only the parent's chronology (`join_keeps_parent_history`).

A native charge that scans the space is not determined by the firing, and it separates
trace-equivalent runs (`AnnotationControls.space_cost_not_traced`). The three metrics of the
runtime (native counts, equation admissions and PeTTa evaluator transitions) are valuations of
three different run categories; no natural transformation between them is claimed here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open Mettapedia.Effects (RunAccount)

open Mettapedia.Machines.NativeCostLedger (Event Totals eventGrade totals boundedTotal scopeTargets)

/-! ## Named operation valuations and receipts -/

section Valuations

/-- **Named operation valuations as a monoid hom** out of the free monoid of native events:
per-kind counts and total work. -/
def nativeTotals : FreeMonoid Event →* Multiplicative Totals :=
  FreeMonoid.lift fun event => Multiplicative.ofAdd (eventGrade event)

theorem nativeTotals_ofList (events : List Event) :
    nativeTotals (FreeMonoid.ofList events) = Multiplicative.ofAdd (totals events) := by
  rw [nativeTotals, FreeMonoid.lift_ofList, totals]
  induction events with
  | nil => rfl
  | cons event rest ih =>
      rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.sum_cons, ofAdd_add]

/-- **Compression**: the run-length receipt of a list of events. -/
def compress (maximum : Nat) (events : List Event) : Mettapedia.Machines.NativeCostLedger.Ledger :=
  events.foldl (Mettapedia.Algebra.RunLengthEvents.appendEvent maximum) []

theorem expand_foldl (maximum : Nat) :
    ∀ (events : List Event) (ledger : Mettapedia.Machines.NativeCostLedger.Ledger),
      Mettapedia.Algebra.RunLengthEvents.expand
          (events.foldl (Mettapedia.Algebra.RunLengthEvents.appendEvent maximum) ledger) =
        Mettapedia.Algebra.RunLengthEvents.expand ledger ++ events
  | [], ledger => by simp
  | event :: rest, ledger => by
      rw [List.foldl_cons, expand_foldl maximum rest, Mettapedia.Algebra.RunLengthEvents.expand_appendEvent,
        List.append_assoc, List.singleton_append]

/-- **Compression is a section of expansion**: it keeps order and identities exactly. -/
theorem expand_compress (maximum : Nat) (events : List Event) :
    Mettapedia.Algebra.RunLengthEvents.expand (compress maximum events) = events := by
  have expanded := expand_foldl maximum events []
  rw [show Mettapedia.Algebra.RunLengthEvents.expand
      ([] : Mettapedia.Machines.NativeCostLedger.Ledger) = [] from rfl, List.nil_append] at expanded
  exact expanded

/-- Compression keeps the totals. -/
theorem snapshot_compress (maximum : Nat) (events : List Event) :
    Mettapedia.Machines.NativeCostLedger.snapshot (compress maximum events) = totals events := by
  rw [Mettapedia.Machines.NativeCostLedger.snapshot, expand_compress]

/-- **Overflow is a hom onto saturating addition**: saturating the saturated parts saturates
the exact sum. -/
theorem boundedTotal_hom (maximum first second : Nat) :
    boundedTotal maximum (boundedTotal maximum first + boundedTotal maximum second) =
      boundedTotal maximum (first + second) := by
  unfold boundedTotal
  omega

end Valuations

/-! ## Nested-scope deduplication is an idempotent merge -/

section Scopes

theorem scopeTargets_perm_of_locations {first second : List (Option Nat)}
    (same : ∀ location, some location ∈ first ↔ some location ∈ second) :
    (scopeTargets first).Perm (scopeTargets second) :=
  (List.perm_ext_iff_of_nodup (Mettapedia.Machines.NativeCostLedger.scopeTargets_unique first)
    (Mettapedia.Machines.NativeCostLedger.scopeTargets_unique second)).mpr fun location => by
      rw [Mettapedia.Machines.NativeCostLedger.scopeTargets_mem,
        Mettapedia.Machines.NativeCostLedger.scopeTargets_mem]
      exact same location

/-- Charging a chain twice is charging it once. -/
theorem scopeTargets_idempotent (scopes : List (Option Nat)) :
    (scopeTargets (scopes ++ scopes)).Perm (scopeTargets scopes) :=
  scopeTargets_perm_of_locations fun location => by simp

/-- Merging two chains does not depend on their order. -/
theorem scopeTargets_comm (first second : List (Option Nat)) :
    (scopeTargets (first ++ second)).Perm (scopeTargets (second ++ first)) :=
  scopeTargets_perm_of_locations fun location => by simp [or_comm]

end Scopes

/-! ## Worker joins -/

/-- A join of a child whose chronology is incomplete keeps only the parent's chronology and
marks the result incomplete; its counters add with saturation. -/
theorem join_keeps_parent_history {width : Nat}
    (parent child : Mettapedia.Machines.NativeCostLedger.Recording.State width) :
    (Mettapedia.Machines.NativeCostLedger.Recording.importIncomplete parent child).history =
        parent.history ∧
      (Mettapedia.Machines.NativeCostLedger.Recording.importIncomplete parent child).traceIncomplete =
        true ∧
      (Mettapedia.Machines.NativeCostLedger.Recording.importIncomplete parent child).work.toNat =
        boundedTotal (2 ^ width - 1) (parent.work.toNat + child.work.toNat) :=
  ⟨rfl, rfl, Mettapedia.Machines.NativeCostLedger.Recording.importIncomplete_work parent child⟩

/-! ## Receipts of the candidate step's runs -/

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

section Receipts

variable (A : SubstitutionAction T S) (label : O → T)

/-- **A receipt annotation**: each firing contributes the native events it charges. -/
def receiptAccount (charges : Firing T S O → List Event) :
    RunAccount (Runs A label) (FreeMonoid Event) :=
  siteAccount A label fun f => FreeMonoid.ofList (charges f)

/-- The totals of a receipt annotation are the site annotation of the firings' totals. -/
theorem receiptTotals (charges : Firing T S O → List Event) :
    (receiptAccount A label charges).map nativeTotals =
      siteAccount A label fun f => Multiplicative.ofAdd (totals (charges f)) := by
  refine account_ext fun o => ?_
  show nativeTotals (FreeMonoid.ofList (charges o.site) * 1) =
    Multiplicative.ofAdd (totals (charges o.site)) * 1
  rw [mul_one, mul_one, nativeTotals_ofList]

/-- **Totals of firing-determined receipts respect the interchange squares.** -/
theorem receiptTotals_factor_static (charges : Firing T S O → List Event) :
    ∃ traced : RunAccount (StaticTraces A label) (Multiplicative Totals),
      traced.comap (Mettapedia.GSLT.Causality.TraceCostValuation.traceFunctor _) =
        (receiptAccount A label charges).map nativeTotals := by
  rw [receiptTotals]
  exact siteAccount_factors_static A label _

/-- **An incomplete chronology**: a firing whose events are not retained annihilates the
chronological readout. -/
def retainedAccount (retained : Firing T S O → Bool) (charges : Firing T S O → List Event) :
    RunAccount (Runs A label) (WithZero (FreeMonoid Event)) :=
  siteAccount A label fun f =>
    if retained f then ((FreeMonoid.ofList (charges f) : FreeMonoid Event) : WithZero _) else 0

/-- **One refusal annihilates the chronology**: the retained readout of a run is zero exactly
when some firing of it was not retained. -/
theorem retained_eq_zero_iff (retained : Firing T S O → Bool)
    (charges : Firing T S O → List Event) :
    ∀ {s t : (theory A label).Term}
      (run : Mettapedia.GSLT.Causality.OccurrenceHistory.OccurrencePath (presentation A label) s t),
      (retainedAccount A label retained charges).of run = 0 ↔
        ∃ f ∈ Mettapedia.GSLT.Causality.OccurrenceHistory.OccurrencePath.sites run,
          retained f = false
  | _, _, .refl _ => by
      change (1 : WithZero (FreeMonoid Event)) = 0 ↔ _
      simp
  | _, _, .cons o rest => by
      have split : (retainedAccount A label retained charges).of
          (Mettapedia.GSLT.Causality.OccurrenceHistory.OccurrencePath.cons o rest) =
            (retainedAccount A label retained charges).of (single o) *
              (retainedAccount A label retained charges).of rest :=
        (retainedAccount A label retained charges).of_comp (single o) rest
      have head : (retainedAccount A label retained charges).of (single o) =
          if retained o.site then
            ((FreeMonoid.ofList (charges o.site) : FreeMonoid Event) : WithZero _) else 0 :=
        ofGrade_single _ o
      rw [split, mul_eq_zero, retained_eq_zero_iff retained charges rest, head]
      cases keep : retained o.site <;>
        simp [keep, Mettapedia.GSLT.Causality.OccurrenceHistory.OccurrencePath.sites]

end Receipts

/-! ## Controls -/

namespace LedgerControls

open Mettapedia.Machines.NativeCostLedger (Payload)

/-- One heap lookup. -/
def payload : Payload := ⟨12, 30, .heapLookup, 1⟩

/-- Two consecutive identities with one payload. -/
def first : Event := (8, payload)
def second : Event := (9, payload)

/-- **Separating control: compression is not a hom of representations.** Compressing the
concatenation gives one run of two; concatenating the compressions gives two runs. Both
expand to the same receipt. -/
theorem compression_merges_runs :
    (compress 255 ([first] ++ [second])).length = 1 ∧
      (compress 255 [first] ++ compress 255 [second]).length = 2 ∧
      Mettapedia.Algebra.RunLengthEvents.expand (compress 255 ([first] ++ [second])) =
        Mettapedia.Algebra.RunLengthEvents.expand (compress 255 [first] ++ compress 255 [second]) := by
  refine ⟨by decide, by decide, ?_⟩
  rw [Mettapedia.Algebra.RunLengthEvents.expand_append, expand_compress, expand_compress, expand_compress]

/-- A cost read. -/
def other : Event := (9, ⟨12, 31, .costRead, 1⟩)

/-- **Separating control: forgetting the chronology keeps totals and loses order.** -/
theorem forgetting_loses_order :
    totals [first, other] = totals [other, first] ∧ [first, other] ≠ [other, first] := by
  refine ⟨?_, by decide⟩
  simp only [totals, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  abel

/-- **Separating control: saturation forgets the excess.** -/
theorem saturation_forgets : boundedTotal 1 2 = boundedTotal 1 3 := rfl

/-- **Separating control: saturation is not additive.** -/
theorem saturation_not_additive : boundedTotal 1 (1 + 1) ≠ boundedTotal 1 1 + boundedTotal 1 1 := by
  decide

end LedgerControls


#print axioms nativeTotals_ofList
#print axioms expand_compress
#print axioms snapshot_compress
#print axioms boundedTotal_hom
#print axioms scopeTargets_idempotent
#print axioms scopeTargets_comm
#print axioms join_keeps_parent_history
#print axioms receiptTotals
#print axioms receiptTotals_factor_static
#print axioms retained_eq_zero_iff
#print axioms LedgerControls.compression_merges_runs
#print axioms LedgerControls.forgetting_loses_order
#print axioms LedgerControls.saturation_forgets
#print axioms LedgerControls.saturation_not_additive

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
