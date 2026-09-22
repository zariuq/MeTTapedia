import Mettapedia.OSLF.Framework.WMCalculusContextEncoding

/-!
# Proof-relevant occurrences of the authored WM contextual rules

`WMStep` and `WMContextStep` state the operational relation in `Prop`.
Their proofs do not retain which root rule or constructor position was used.
The indexed event types below retain precisely that information, while their
erasures have exactly the support of the authored relations. A trace is a
finite sequence of such events; it is not inferred from denotational equality.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusOccurrenceTrace

open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusEncoding
open Mettapedia.OSLF.Framework.WMCalculusContextEncoding
open Mettapedia.OSLF.Framework.LangMorphism

/-- A root-rule occurrence, indexed by its exact typed endpoints. -/
inductive WMRootEvent : {s : WMSort} → WMTerm s → WMTerm s → Type where
  | evidence_add (first second : WMTerm .state) (query : WMTerm .query) :
      WMRootEvent (.extract (.revise first second) query)
        (.combine (.extract first query) (.extract second query))
  | revision_comm (first second : WMTerm .state) :
      WMRootEvent (.revise first second) (.revise second first)
  | revision_assoc (first second third : WMTerm .state) :
      WMRootEvent (.revise (.revise first second) third)
        (.revise first (.revise second third))
  | combine_comm (first second : WMTerm .evidence) :
      WMRootEvent (.combine first second) (.combine second first)
  | combine_zero (term : WMTerm .evidence) :
      WMRootEvent (.combine term .zero) term

/-- Forget occurrence identity, retaining the authored root step. -/
theorem WMRootEvent.erase {s : WMSort} {source target : WMTerm s} :
    WMRootEvent source target → WMStep source target
  | .evidence_add first second query => .evidence_add first second query
  | .revision_comm first second => .revision_comm first second
  | .revision_assoc first second third => .revision_assoc first second third
  | .combine_comm first second => .combine_comm first second
  | .combine_zero term => .combine_zero term

/-- Every authored root step has an occurrence, and every occurrence erases
to an authored root step. -/
theorem rootEvent_support_iff {s : WMSort} {source target : WMTerm s} :
    Nonempty (WMRootEvent source target) ↔ WMStep source target := by
  constructor
  · rintro ⟨event⟩
    exact event.erase
  · intro step
    cases step with
    | evidence_add first second query => exact ⟨.evidence_add first second query⟩
    | revision_comm first second => exact ⟨.revision_comm first second⟩
    | revision_assoc first second third =>
        exact ⟨.revision_assoc first second third⟩
    | combine_comm first second => exact ⟨.combine_comm first second⟩
    | combine_zero term => exact ⟨.combine_zero term⟩

/-- A root occurrence placed at a precise constructor position. -/
inductive WMContextEvent : {s : WMSort} → WMTerm s → WMTerm s → Type where
  | root {s : WMSort} {source target : WMTerm s} :
      WMRootEvent source target → WMContextEvent source target
  | revise_left {first first' : WMTerm .state} (second : WMTerm .state) :
      WMContextEvent first first' →
        WMContextEvent (.revise first second) (.revise first' second)
  | revise_right (first : WMTerm .state) {second second' : WMTerm .state} :
      WMContextEvent second second' →
        WMContextEvent (.revise first second) (.revise first second')
  | extract_left {world world' : WMTerm .state} (query : WMTerm .query) :
      WMContextEvent world world' →
        WMContextEvent (.extract world query) (.extract world' query)
  | extract_right (world : WMTerm .state) {query query' : WMTerm .query} :
      WMContextEvent query query' →
        WMContextEvent (.extract world query) (.extract world query')
  | combine_left {first first' : WMTerm .evidence} (second : WMTerm .evidence) :
      WMContextEvent first first' →
        WMContextEvent (.combine first second) (.combine first' second)
  | combine_right (first : WMTerm .evidence) {second second' : WMTerm .evidence} :
      WMContextEvent second second' →
        WMContextEvent (.combine first second) (.combine first second')

/-- Erase the position-labelled event to the existing contextual relation. -/
theorem WMContextEvent.erase {s : WMSort} {source target : WMTerm s} :
    WMContextEvent source target → WMContextStep source target
  | .root event => .root event.erase
  | .revise_left second event => .revise_left second event.erase
  | .revise_right first event => .revise_right first event.erase
  | .extract_left query event => .extract_left query event.erase
  | .extract_right world event => .extract_right world event.erase
  | .combine_left second event => .combine_left second event.erase
  | .combine_right first event => .combine_right first event.erase

/-- The event refinement has exactly the support of contextual WM steps. -/
theorem contextEvent_support_iff {s : WMSort} {source target : WMTerm s} :
    Nonempty (WMContextEvent source target) ↔ WMContextStep source target := by
  constructor
  · rintro ⟨event⟩
    exact event.erase
  · intro step
    induction step with
    | root root =>
        obtain ⟨event⟩ := rootEvent_support_iff.mpr root
        exact ⟨.root event⟩
    | revise_left second _ ih =>
        obtain ⟨event⟩ := ih
        exact ⟨.revise_left second event⟩
    | revise_right first _ ih =>
        obtain ⟨event⟩ := ih
        exact ⟨.revise_right first event⟩
    | extract_left query _ ih =>
        obtain ⟨event⟩ := ih
        exact ⟨.extract_left query event⟩
    | extract_right world _ ih =>
        obtain ⟨event⟩ := ih
        exact ⟨.extract_right world event⟩
    | combine_left second _ ih =>
        obtain ⟨event⟩ := ih
        exact ⟨.combine_left second event⟩
    | combine_right first _ ih =>
        obtain ⟨event⟩ := ih
        exact ⟨.combine_right first event⟩

/-- A sequence of actual contextual occurrences, retaining the length,
intermediate terms, root-rule choices, and constructor positions. -/
inductive WMTrace : {s : WMSort} → WMTerm s → WMTerm s → Type where
  | refl {s : WMSort} {term : WMTerm s} : WMTrace term term
  | tail {s : WMSort} {source middle target : WMTerm s} :
      WMTrace source middle → WMContextEvent middle target →
        WMTrace source target

/-- Number of retained occurrences. This cannot be reconstructed from the
propositional reachability relation or from denotational equality. -/
def WMTrace.length {s : WMSort} {source target : WMTerm s} :
    WMTrace source target → Nat
  | .refl => 0
  | .tail earlier _ => earlier.length + 1

/-- Forget the execution record to the existing reflexive-transitive
contextual relation. -/
theorem WMTrace.erase {s : WMSort} {source target : WMTerm s} :
    WMTrace source target → WMContextStepStar source target
  | .refl => .refl
  | .tail earlier last => .tail earlier.erase last.erase

/-- Trace existence and contextual reachability agree exactly, even though
the trace carrier distinguishes executions that the proposition does not. -/
theorem trace_support_iff {s : WMSort} {source target : WMTerm s} :
    Nonempty (WMTrace source target) ↔ WMContextStepStar source target := by
  constructor
  · rintro ⟨trace⟩
    exact trace.erase
  · intro steps
    induction steps with
    | refl => exact ⟨.refl⟩
    | tail _ last earlier =>
        obtain ⟨trace⟩ := earlier
        obtain ⟨event⟩ := contextEvent_support_iff.mpr last
        exact ⟨.tail trace event⟩

/-- Existence of an occurrence trace is exactly execution in the authored
contextual LanguageDef, for encoded typed endpoints. This is a support
equivalence; the authored relation still does not name the trace. -/
theorem trace_authored_iff {s : WMSort} (source target : WMTerm s) :
    Nonempty (WMTrace source target) ↔
      LangReducesStar
        (Mettapedia.OSLF.Framework.WMCalculusContextClosure.wmExtVertexLanguageDefWithCong
          Mettapedia.OSLF.Framework.WMCalculusLanguageDef.wmExtVertexMinimal)
        (encodeWM source) (encodeWM target) :=
  trace_support_iff.trans (wmContextStepStar_iff source target)

/-- Two genuine revision commutations return to their source. The two
occurrences remain distinct from a zero-step execution. -/
def revisionCommRoundtrip (first second : WMTerm .state) :
    WMTrace (.revise first second) (.revise first second) :=
  .tail
    (.tail .refl (.root (.revision_comm first second)))
    (.root (.revision_comm second first))

theorem refl_ne_revisionCommRoundtrip (first second : WMTerm .state) :
    (WMTrace.refl : WMTrace (.revise first second) (.revise first second)) ≠
      revisionCommRoundtrip first second := by
  intro equal
  cases equal

end Mettapedia.OSLF.Framework.WMCalculusOccurrenceTrace
