import Mettapedia.GSLT.LanguageDef.Cost

/-! Probes testing whether the audited negatives carry the content their names claim.
    Each `example` that elaborates is EVIDENCE FOR the audit finding stated above it. -/

namespace Mettapedia.Algebra

open Mettapedia.Algebra.WorkSpan

/-- PROBE 1. `workSpan_forgets_any_separating_attribute` uses no property of
`WorkSpan`.  The identical statement holds with the valuation carrier replaced by
an arbitrary inhabited type — indeed by `Unit`.  So the theorem is a fact about
`Prod`, not about work and span. -/
structure ValuedRun' (Payload Valuation : Type) where
  payload : Payload
  value : Valuation

example {Payload Attribute Valuation : Type} (v : Valuation)
    (observe : Payload → Attribute) {first second : Payload}
    (separates : observe first ≠ observe second) :
    ∃ left right : ValuedRun' Payload Valuation,
      left.value = right.value ∧ observe left.payload ≠ observe right.payload :=
  ⟨⟨first, v⟩, ⟨second, v⟩, rfl, separates⟩

/-- PROBE 1b. Even with the valuation carrier `Unit`. -/
example {Payload Attribute : Type} (observe : Payload → Attribute)
    {first second : Payload} (separates : observe first ≠ observe second) :
    ∃ left right : ValuedRun' Payload Unit,
      left.value = right.value ∧ observe left.payload ≠ observe right.payload :=
  ⟨⟨first, ()⟩, ⟨second, ()⟩, rfl, separates⟩

/-- PROBE 2. The five named corollaries are one theorem alpha-renamed:
each is definitionally the general one. -/
example : @WorkSpan.workSpan_forgets_colour = @WorkSpan.workSpan_forgets_any_separating_attribute := rfl
example : @WorkSpan.workSpan_forgets_declaration = @WorkSpan.workSpan_forgets_any_separating_attribute := rfl
example : @WorkSpan.workSpan_forgets_receipt = @WorkSpan.workSpan_forgets_any_separating_attribute := rfl
example : @WorkSpan.workSpan_forgets_causalOrder = @WorkSpan.workSpan_forgets_any_separating_attribute := rfl
example : @WorkSpan.workSpan_forgets_elaborationPath = @WorkSpan.workSpan_forgets_any_separating_attribute := rfl

/-- PROBE 3. `ReceiptSchema.omitted_attribute_undetectable` is `And.intro` applied
to its own two hypotheses: nothing is derived. -/
example {Execution Record Attribute : Type}
    (schema : ReceiptSchema.Schema Execution Record)
    (observe : Execution → Attribute) {left right : Execution}
    (conflated : schema left = schema right)
    (differs : observe left ≠ observe right) :
    ReceiptSchema.omitted_attribute_undetectable schema observe conflated differs
      = ⟨conflated, differs⟩ := rfl

/-- PROBE 4. `recorded_attribute_detectable` is the identity function. -/
example {Execution Attribute : Type} (observe : Execution → Attribute)
    {left right : Execution} (differs : observe left ≠ observe right) :
    ReceiptSchema.recorded_attribute_detectable observe differs = differs := rfl

/-- PROBE 5. `drop_field_monotone` is definitionally `tuple_separates_of_left`. -/
example : @ReceiptSchema.drop_field_monotone = @ReceiptSchema.tuple_separates_of_left := rfl

/-- PROBE 6. `checksAsEqual_iff_not_separates` is Mathlib's `not_ne_iff`. -/
example {Execution Record : Type} (schema : ReceiptSchema.Schema Execution Record)
    (left right : Execution) :
    ReceiptSchema.ChecksAsEqual schema left right ↔
      ¬ ReceiptSchema.Separates schema left right := not_ne_iff.symm

/-- PROBE 7. `occurrence_correspondence_not_determined_by_values` never uses the
frontier: the same statement holds for the constantly-`()` frontier, and indeed
for any constant frontier, because the value clause degenerates to `rfl`. -/
example : ∃ first second : Fin 2 → Fin 2,
    first ≠ second ∧ ∀ index, (fun _ : Fin 2 => ()) (first index) =
      (fun _ : Fin 2 => ()) (second index) :=
  ⟨id, OccurrenceIdentity.exchange,
    fun equal => OccurrenceIdentity.exchange_ne_id equal.symm, fun _ => rfl⟩

/-- PROBE 8. `value_agreement_does_not_yield_correspondence` never uses
`duplicateFrontier` either: any argument works. -/
example (recover : (Fin 2 → Nat) → (Fin 2 → Fin 2)) (anyFrontier : Fin 2 → Nat) :
    ¬ ((recover anyFrontier = id) ∧ (recover anyFrontier = OccurrenceIdentity.exchange)) := by
  rintro ⟨isIdentity, isExchange⟩
  exact OccurrenceIdentity.exchange_ne_id (isExchange.symm.trans isIdentity)

/-- PROBE 9. THE LOAD-BEARING FORM IS AVAILABLE.  The honest statement matching
the docstring "peak allocation is not a `ConcurrentCostAlgebra`" is a
non-existence of structure, and it is provable today. -/
theorem probe_no_peakAllocation_algebra :
    ¬ ∃ algebra : ConcurrentCostAlgebra Nat,
        algebra.sequential = peakSequential ∧ algebra.parallel = peakParallel := by
  rintro ⟨algebra, seq, par⟩
  have law := algebra.lax_interchange 1 0 0 1
  rw [seq, par] at law
  simp only [peakSequential, peakParallel] at law
  omega

/-- PROBE 10. The two conjuncts of `parallelism_improves_span_worsens_allocation`
are independent: each is provable alone, and neither mentions the other's carrier. -/
theorem probe_parallel_span_le_sequential_span (left right : WorkSpan) :
    (WorkSpan.parallel left right).span ≤ (WorkSpan.sequential left right).span := by
  simp only [WorkSpan.parallel, WorkSpan.sequential]; omega

theorem probe_peakSequential_lt_peakParallel_one :
    peakSequential 1 1 < peakParallel 1 1 := by
  simp only [peakSequential, peakParallel]; omega

end Mettapedia.Algebra

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Reflection

/-- PROBE 11. The second conjunct of `quoteBoundary_diverges` involves neither the
profile nor membership: it is `beq` of two distinct strings.  So the theorem is a
conjunction of two independent facts, not a statement about divergence. -/
example (owner other : ReflectivePresentationDecl)
    (distinct : owner.quoteConstructor ≠ other.quoteConstructor) :
    (owner.quoteConstructor == other.quoteConstructor) = false :=
  beq_eq_false_iff_ne.mpr distinct

/-- PROBE 12. The first conjunct is exactly the "own quote is recognized" fact,
which is separately re-proved verbatim inside four other declarations. -/
example (profile : ReflectionProfile) (owner : ReflectivePresentationDecl)
    (ownerMem : owner ∈ profile.presentations) :
    ReflectiveContextSupport.isQuoteConstructor profile owner.quoteConstructor = true := by
  unfold ReflectiveContextSupport.isQuoteConstructor
  exact List.any_eq_true.mpr ⟨owner, ownerMem, beq_self_eq_true _⟩

end Mettapedia.GSLT.LanguageDef
