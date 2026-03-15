import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# The Reversibility Envelope S†

Given a GSLT S = (T, E, R), the reversibility envelope S† extends S with
explicit traces so that every forward rewrite step has a corresponding
backward step.  The arrow of time disappears from the laws and appears
only in the boundary condition (the initial empty trace).

## Construction (following L. Gregory Meredith §3)

1. A **trace** is a finite sequence of (rule-name, matched-LHS) entries.
2. An **extended term** is a pair ⟨P, τ⟩ of a current term and its trace.
3. **Forward rules** r⁺: fire the rule and push an entry onto the trace.
4. **Backward rules** r⁻: pop the trace entry and undo the rule.
5. S† = (T†, E†, R⁺ ∪ R⁻).

## Key Theorems

- `forward_backward_cancel`: A forward step followed by its backward step is identity
- `backward_forward_cancel`: A backward step followed by its forward step is identity
- `projection_section_id`: Projection ∘ section = identity
- `traceBudget`: Sum of costs recorded in the trace (infrastructure for conservation)

## References

- L. Gregory Meredith, "Computation, Causality, and Consciousness" (2026), §3
- Danos & Krivine, "Reversible CCS"
- Phillips & Ulidowski, "Reversible process calculi"
-/

namespace Mettapedia.OSLF.Framework.ReversibilityEnvelope

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.DeclReducesPremises
open Mettapedia.OSLF.Framework.TypeSynthesis

/-! ## Traces and Extended Terms -/

/-- A trace entry records which rule fired and on which term.
    This is the causal history of a single rewrite step. -/
structure TraceEntry where
  /-- Name of the rule that fired -/
  ruleName : String
  /-- The term before the rule fired (the matched left-hand side instance) -/
  beforeTerm : Pattern
  /-- The cost charged for this step (used by resource conservation) -/
  stepCost : ℤ := 0
  deriving Repr, BEq

/-- A trace is a finite sequence of entries, most recent first. -/
abbrev Trace := List TraceEntry

/-- An extended term pairs a current pattern with its causal history. -/
structure ExtendedTerm where
  /-- The current state of the computation -/
  current : Pattern
  /-- The causal history: which rules fired, in reverse chronological order -/
  history : Trace
  deriving Repr

/-- The initial condition: a term with no causal past. -/
def ExtendedTerm.initial (p : Pattern) : ExtendedTerm :=
  ⟨p, []⟩

/-- Project an extended term to its current state (forget the history). -/
def ExtendedTerm.project (et : ExtendedTerm) : Pattern :=
  et.current

/-! ## The Envelope Reduction Relation -/

/-- Reduction in the reversible envelope.
    Forward steps fire a rule and record it; backward steps undo. -/
inductive EnvelopeReduces (lang : LanguageDef) :
    ExtendedTerm → ExtendedTerm → Prop where
  /-- Forward step: fire rule r, push entry (with cost c) onto trace. -/
  | forward
    (r : RewriteRule)
    (hr : r ∈ lang.rewrites)
    (p q : Pattern)
    (bs : Bindings)
    (_hbs : bs ∈ matchPattern r.left p)
    (hq : q = applyBindings bs r.right)
    (c : ℤ)
    (history : Trace) :
    EnvelopeReduces lang
      ⟨p, history⟩
      ⟨q, ⟨r.name, p, c⟩ :: history⟩
  /-- Backward step: pop entry (with cost c) from trace, restore previous term. -/
  | backward
    (r : RewriteRule)
    (hr : r ∈ lang.rewrites)
    (p q : Pattern)
    (bs : Bindings)
    (_hbs : bs ∈ matchPattern r.left p)
    (hq : q = applyBindings bs r.right)
    (c : ℤ)
    (history : Trace) :
    EnvelopeReduces lang
      ⟨q, ⟨r.name, p, c⟩ :: history⟩
      ⟨p, history⟩

/-- Multi-step envelope reduction. -/
inductive EnvelopeReducesStar (lang : LanguageDef) :
    ExtendedTerm → ExtendedTerm → Prop where
  | refl (et : ExtendedTerm) : EnvelopeReducesStar lang et et
  | step {et₁ et₂ et₃ : ExtendedTerm} :
      EnvelopeReduces lang et₁ et₂ →
      EnvelopeReducesStar lang et₂ et₃ →
      EnvelopeReducesStar lang et₁ et₃

/-! ## Cancellation Theorems -/

/-- A forward step followed by its backward step is the identity. -/
theorem forward_backward_cancel
    {lang : LanguageDef}
    {r : RewriteRule} {hr : r ∈ lang.rewrites}
    {p q : Pattern} {bs : Bindings}
    {hbs : bs ∈ matchPattern r.left p}
    {hq : q = applyBindings bs r.right}
    {c : ℤ} {history : Trace} :
    EnvelopeReducesStar lang
      ⟨p, history⟩
      ⟨p, history⟩ := by
  exact .step
    (.forward r hr p q bs hbs hq c history)
    (.step (.backward r hr p q bs hbs hq c history) (.refl _))

/-- A backward step followed by its forward step is the identity. -/
theorem backward_forward_cancel
    {lang : LanguageDef}
    {r : RewriteRule} {hr : r ∈ lang.rewrites}
    {p q : Pattern} {bs : Bindings}
    {hbs : bs ∈ matchPattern r.left p}
    {hq : q = applyBindings bs r.right}
    {c : ℤ} {history : Trace} :
    EnvelopeReducesStar lang
      ⟨q, ⟨r.name, p, c⟩ :: history⟩
      ⟨q, ⟨r.name, p, c⟩ :: history⟩ := by
  exact .step
    (.backward r hr p q bs hbs hq c history)
    (.step (.forward r hr p q bs hbs hq c history) (.refl _))

/-! ## Projection and Section -/

/-- The section: embed a base-language term as an initial extended term. -/
def section_ (p : Pattern) : ExtendedTerm :=
  ExtendedTerm.initial p

/-- Projection ∘ section = identity. -/
theorem projection_section_id (p : Pattern) :
    (section_ p).project = p := rfl

/-! ## Time Symmetry

In the envelope, the laws (forward + backward rules) are symmetric.
The arrow of time appears only in the boundary condition:
an initial term ⟨P, []⟩ has no causal past. -/

/-- An extended term is an initial condition iff its trace is empty. -/
def ExtendedTerm.isInitial (et : ExtendedTerm) : Prop :=
  et.history = []

-- The backward constructor requires a non-empty trace (the trace head
-- records which rule to undo).  An initial term ⟨P, []⟩ therefore admits
-- only forward steps.

/-! ## Transitivity -/

/-- Transitivity of multi-step envelope reductions. -/
theorem EnvelopeReducesStar.trans
    {lang : LanguageDef} {et₁ et₂ et₃ : ExtendedTerm}
    (h₁ : EnvelopeReducesStar lang et₁ et₂)
    (h₂ : EnvelopeReducesStar lang et₂ et₃) :
    EnvelopeReducesStar lang et₁ et₃ := by
  induction h₁ with
  | refl _ => exact h₂
  | step hstep _ ih => exact .step hstep (ih h₂)

/-! ## Trace Budget

The trace is the accounting ledger: each entry records the cost of the step
that created it.  The trace budget is the sum of all recorded costs. -/

/-- The total cost recorded in a trace: sum of stepCost over all entries.
    Defined recursively for clean definitional reduction. -/
def traceBudget : Trace → ℤ
  | [] => 0
  | e :: rest => e.stepCost + traceBudget rest

/-- Empty trace has zero budget. -/
@[simp] theorem traceBudget_nil : traceBudget [] = 0 := rfl

/-- Pushing an entry adds its cost to the budget. -/
@[simp] theorem traceBudget_cons (e : TraceEntry) (hist : Trace) :
    traceBudget (e :: hist) = e.stepCost + traceBudget hist := rfl

end Mettapedia.OSLF.Framework.ReversibilityEnvelope
