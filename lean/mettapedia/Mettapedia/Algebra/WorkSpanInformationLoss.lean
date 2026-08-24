import Mettapedia.Algebra.WorkSpan

/-!
# What a work/span readout cannot tell you

`WorkSpan` is a *valuation* of an execution, not the execution.  It is one
observation among several a costed run admits — allocation, energy,
communication, provenance — and like any observation it forgets.  The
theorems here fix exactly what it forgets, so that no downstream consumer
mistakes equal work and span for equal computation.

The pattern is uniform and deliberately elementary: for each attribute a
caller might hope to recover, exhibit two executions that differ in that
attribute yet carry the same `WorkSpan`.  Each is a genuine negative,
which is the only honest way to state an information-loss claim.

The positive laws — associativity, monotonicity, the lax interchange, and
`parallel_le_sequential` — live in `WorkSpan`.  Nothing here weakens them;
this module bounds their interpretation.
-/

namespace Mettapedia.Algebra

namespace WorkSpan

/-- An abstract costed execution: some payload, valued by a work/span
readout.  The payload stands for whatever the execution actually carries —
colour, declaration identity, receipts, causal order, elaboration path. -/
structure ValuedRun (Payload : Type) where
  payload : Payload
  value : WorkSpan

/-- A readout forgets an attribute when two runs agree on the readout yet
disagree on that attribute. -/
def ForgetsObservation {Payload Attribute : Type}
    (observe : Payload → Attribute) : Prop :=
  ∃ left right : ValuedRun Payload,
    left.value = right.value ∧ observe left.payload ≠ observe right.payload

/-- **The general information-loss theorem.**  A work/span readout forgets
*every* attribute that distinguishes two payloads at all.  Nothing about
the payload survives the valuation beyond what the two coordinates
record. -/
theorem workSpan_forgets_any_separating_attribute
    {Payload Attribute : Type} (observe : Payload → Attribute)
    {first second : Payload}
    (separates : observe first ≠ observe second) :
    ForgetsObservation observe :=
  ⟨⟨first, 0⟩, ⟨second, 0⟩, rfl, separates⟩

/-! ## The named readouts, as corollaries

Each names an attribute a consumer might try to recover from work and
span.  The hypothesis in every case is only that the attribute is not
constant — i.e. that it is worth recording at all. -/

/-- Work and span do not determine execution **colour**. -/
theorem workSpan_forgets_colour {Payload Colour : Type}
    (colour : Payload → Colour) {first second : Payload}
    (distinct : colour first ≠ colour second) :
    ForgetsObservation colour :=
  workSpan_forgets_any_separating_attribute colour distinct

/-- Work and span do not determine **declaration identity**. -/
theorem workSpan_forgets_declaration {Payload Decl : Type}
    (declaration : Payload → Decl) {first second : Payload}
    (distinct : declaration first ≠ declaration second) :
    ForgetsObservation declaration :=
  workSpan_forgets_any_separating_attribute declaration distinct

/-- Work and span do not determine the **receipt**. -/
theorem workSpan_forgets_receipt {Payload Receipt : Type}
    (receipt : Payload → Receipt) {first second : Payload}
    (distinct : receipt first ≠ receipt second) :
    ForgetsObservation receipt :=
  workSpan_forgets_any_separating_attribute receipt distinct

/-- Work and span do not determine **causal order**. -/
theorem workSpan_forgets_causalOrder {Payload Order : Type}
    (causalOrder : Payload → Order) {first second : Payload}
    (distinct : causalOrder first ≠ causalOrder second) :
    ForgetsObservation causalOrder :=
  workSpan_forgets_any_separating_attribute causalOrder distinct

/-- Work and span do not determine the **elaboration path**.  This is the
readout-level counterpart of the cost-layer iteration non-factorization results: compact
observation cannot recover elaboration provenance. -/
theorem workSpan_forgets_elaborationPath {Payload Path : Type}
    (elaborationPath : Payload → Path) {first second : Payload}
    (distinct : elaborationPath first ≠ elaborationPath second) :
    ForgetsObservation elaborationPath :=
  workSpan_forgets_any_separating_attribute elaborationPath distinct

/-! ## Loss inside the readout itself

Even the two coordinates do not determine each other, and neither
determines the shape of the run that produced them. -/

/-- Equal work does not determine span: one unit of work spent as a single
phase and as one of two independent branches differ in span. -/
theorem work_does_not_determine_span :
    ∃ left right : WorkSpan,
      left.work = right.work ∧ left.span ≠ right.span :=
  ⟨⟨2, 2⟩, ⟨2, 1⟩, rfl, by decide⟩

/-- Equal span does not determine work. -/
theorem span_does_not_determine_work :
    ∃ left right : WorkSpan,
      left.span = right.span ∧ left.work ≠ right.work :=
  ⟨⟨1, 1⟩, ⟨2, 1⟩, rfl, by decide⟩

/-- **Sequential and parallel composition can coincide.**  When one branch
is empty the two composites agree, so the readout does not record whether
a run was scheduled sequentially or in parallel. -/
theorem sequential_eq_parallel_of_zero_right (value : WorkSpan) :
    sequential value 0 = parallel value 0 := by
  ext <;> simp [sequential, parallel]

/-- Consequently the readout forgets the **schedule shape**: two runs with
the same value can have been composed differently. -/
theorem workSpan_forgets_schedule_shape :
    ∃ left right : WorkSpan,
      sequential left right = parallel left right ∧
        ¬ ∀ first second : WorkSpan,
          sequential first second = parallel first second := by
  refine ⟨⟨1, 1⟩, 0, sequential_eq_parallel_of_zero_right _, ?_⟩
  intro allEqual
  have collision := allEqual ⟨0, 1⟩ ⟨0, 1⟩
  have spans : (2 : Nat) = 1 := congrArg WorkSpan.span collision
  exact absurd spans (by decide)

end WorkSpan

end Mettapedia.Algebra
