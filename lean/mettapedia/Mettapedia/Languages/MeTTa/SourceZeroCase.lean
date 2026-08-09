import Mettapedia.GSLT.LanguageDef.EmptyDemandCoherence

/-!
# Source-local zero observation for `case`

This module separates two superficially similar operations over a finite,
complete, fault-free occurrence sequence:

* `sourceCase source dispatch fallback` runs `fallback` exactly when `source`
  has no occurrences.  Once the source is nonempty, the fallback is outside
  the scope of later matching failure or branch pruning.
* `postDispatchOrElse source dispatch fallback` first dispatches every source
  occurrence and then observes the combined result.  It therefore runs the
  fallback when dispatch produces no survivors, regardless of why.

The first operation is the proposed three-argument `case` law.  The second is
the distinct `try (case ...) fallback` law.  Their separation prevents an
unmatched value or a matching arm whose body returns computational zero from
being reclassified as an empty source computation.

This module deliberately proves the scoping law in the occurrence fragment.
Coverage, faults, receipts, and resumable frontiers are extra report
coordinates; observing an open or faulty report as completed zero would be a
separate error, not a different `case` law.
-/

namespace Mettapedia.Languages.MeTTa.SourceZeroCase

open Mettapedia.GSLT.LanguageDef
open EmptyDemandCoherence (Occurrences zero observeZero)

universe u

/-- Ordinary two-argument case: dispatch every source occurrence independently.
An occurrence for which `dispatch` returns zero contributes no result. -/
def dispatchCase {Atom Result : Type u} (source : Occurrences Atom)
    (dispatch : Atom → Occurrences Result) : Occurrences Result :=
  EmptyDemandCoherence.bind source dispatch

/-- Three-argument case with a source-local fallback.  The fallback observes
zero at the source boundary, before per-occurrence dispatch begins. -/
def sourceCase {Atom Result : Type u} (source : Occurrences Atom)
    (dispatch : Atom → Occurrences Result)
    (fallback : Occurrences Result) : Occurrences Result :=
  observeZero source fallback dispatch

/-- Run a fallback when an entire computation produces no occurrences. -/
def orElse {Atom : Type u} (source fallback : Occurrences Atom) :
    Occurrences Atom :=
  observeZero source fallback EmptyDemandCoherence.pure

/-- Dispatch first, then observe whether anything survived.  This is the
denotation of `try (case source dispatch) fallback`, not source-local case. -/
def postDispatchOrElse {Atom Result : Type u} (source : Occurrences Atom)
    (dispatch : Atom → Occurrences Result)
    (fallback : Occurrences Result) : Occurrences Result :=
  orElse (dispatchCase source dispatch) fallback

/-! ## Source-local laws -/

@[simp] theorem dispatchCase_zero {Atom Result : Type u}
    (dispatch : Atom → Occurrences Result) :
    dispatchCase zero dispatch = zero :=
  rfl

@[simp] theorem dispatchCase_pure {Atom Result : Type u} (atom : Atom)
    (dispatch : Atom → Occurrences Result) :
    dispatchCase (EmptyDemandCoherence.pure atom) dispatch = dispatch atom := by
  simp [dispatchCase]

/-- A completed source zero, and only that source condition, selects the
three-argument case fallback. -/
@[simp] theorem sourceCase_zero {Atom Result : Type u}
    (dispatch : Atom → Occurrences Result)
    (fallback : Occurrences Result) :
    sourceCase zero dispatch fallback = fallback :=
  rfl

/-- An ordinary returned datum is sent to dispatch, regardless of its name. -/
@[simp] theorem sourceCase_pure {Atom Result : Type u} (atom : Atom)
    (dispatch : Atom → Occurrences Result)
    (fallback : Occurrences Result) :
    sourceCase (EmptyDemandCoherence.pure atom) dispatch fallback = dispatch atom := by
  simp [sourceCase]

/-- On a nonempty source, three-argument case is exactly ordinary list bind. -/
theorem sourceCase_eq_dispatchCase_of_ne_zero {Atom Result : Type u}
    (source : Occurrences Atom) (dispatch : Atom → Occurrences Result)
    (fallback : Occurrences Result) (sourceNonzero : source ≠ zero) :
    sourceCase source dispatch fallback = dispatchCase source dispatch := by
  cases source with
  | nil => exact (sourceNonzero rfl).elim
  | cons head tail => rfl

/-- Once a source occurrence exists, changing the fallback cannot change the
result.  This is the locality law that prevents downstream failure laundering. -/
theorem sourceCase_fallback_irrelevant_of_ne_zero {Atom Result : Type u}
    (source : Occurrences Atom) (dispatch : Atom → Occurrences Result)
    (firstFallback secondFallback : Occurrences Result)
    (sourceNonzero : source ≠ zero) :
    sourceCase source dispatch firstFallback =
      sourceCase source dispatch secondFallback := by
  rw [sourceCase_eq_dispatchCase_of_ne_zero source dispatch firstFallback sourceNonzero]
  rw [sourceCase_eq_dispatchCase_of_ne_zero source dispatch secondFallback sourceNonzero]

/-- An unmatched value is represented by dispatch returning zero.  It remains
zero; source-local fallback does not reinterpret it as source absence. -/
theorem sourceCase_unmatched_remains_zero {Atom Result : Type u}
    (atom : Atom) (dispatch : Atom → Occurrences Result)
    (fallback : Occurrences Result) (unmatched : dispatch atom = zero) :
    sourceCase (EmptyDemandCoherence.pure atom) dispatch fallback = zero := by
  rw [sourceCase_pure, unmatched]

/-- The same law covers a matching arm whose body deliberately prunes by
returning computational zero. -/
theorem sourceCase_matching_body_zero_remains_zero {Atom Result : Type u}
    (atom : Atom) (dispatch : Atom → Occurrences Result)
    (fallback : Occurrences Result) (bodyPrunes : dispatch atom = zero) :
    sourceCase (EmptyDemandCoherence.pure atom) dispatch fallback = zero :=
  sourceCase_unmatched_remains_zero atom dispatch fallback bodyPrunes

/-- Multiple source occurrences remain ordinary per-occurrence dispatch; the
fallback is not interleaved with or injected into the answer flow. -/
@[simp] theorem sourceCase_cons {Atom Result : Type u} (head : Atom)
    (tail : Occurrences Atom) (dispatch : Atom → Occurrences Result)
    (fallback : Occurrences Result) :
    sourceCase (head :: tail) dispatch fallback =
      dispatch head ++ dispatchCase tail dispatch := by
  simp [sourceCase, observeZero, dispatchCase, EmptyDemandCoherence.bind]

/-! ## Post-dispatch fallback is a different operator -/

@[simp] theorem orElse_zero {Atom : Type u} (fallback : Occurrences Atom) :
    orElse zero fallback = fallback :=
  rfl

@[simp] theorem orElse_pure {Atom : Type u} (atom : Atom)
    (fallback : Occurrences Atom) :
    orElse (EmptyDemandCoherence.pure atom) fallback =
      EmptyDemandCoherence.pure atom := by
  simp [orElse]

@[simp] theorem postDispatchOrElse_zero {Atom Result : Type u}
    (dispatch : Atom → Occurrences Result)
    (fallback : Occurrences Result) :
    postDispatchOrElse zero dispatch fallback = fallback :=
  rfl

theorem postDispatchOrElse_pure {Atom Result : Type u} (atom : Atom)
    (dispatch : Atom → Occurrences Result)
    (fallback : Occurrences Result) :
    postDispatchOrElse (EmptyDemandCoherence.pure atom) dispatch fallback =
      orElse (dispatch atom) fallback := by
  simp [postDispatchOrElse]

/-- Post-dispatch fallback catches an unmatched value or a pruning body because
it observes after dispatch.  This is useful, but semantically distinct. -/
theorem postDispatchOrElse_catches_downstream_zero {Atom Result : Type u}
    (atom : Atom) (dispatch : Atom → Occurrences Result)
    (fallback : Occurrences Result) (downstreamZero : dispatch atom = zero) :
    postDispatchOrElse (EmptyDemandCoherence.pure atom) dispatch fallback = fallback := by
  rw [postDispatchOrElse_pure, downstreamZero, orElse_zero]

/-- The two candidate meanings of three-argument `case` are observably
different whenever dispatch produces zero and the fallback produces something. -/
theorem sourceCase_ne_postDispatchOrElse_of_downstream_zero
    {Atom Result : Type u} (atom : Atom)
    (dispatch : Atom → Occurrences Result)
    (fallback : Occurrences Result) (downstreamZero : dispatch atom = zero)
    (fallbackNonzero : fallback ≠ zero) :
    sourceCase (EmptyDemandCoherence.pure atom) dispatch fallback ≠
      postDispatchOrElse (EmptyDemandCoherence.pure atom) dispatch fallback := by
  rw [sourceCase_pure, downstreamZero]
  rw [postDispatchOrElse_catches_downstream_zero atom dispatch fallback downstreamZero]
  exact Ne.symm fallbackNonzero

/-! ## Executable semantic canaries -/

namespace Canary

inductive Answer where
  | a
  | b
  | c
  | emptyData
  deriving DecidableEq, Repr

inductive Action where
  | handledA
  | handledB
  | handledEmptyData
  | handledOther (answer : Answer)
  | fallback
  deriving DecidableEq, Repr

/-- `c` has no matching arm.  The atom named `emptyData` is an ordinary datum
with an ordinary matching arm. -/
def selectiveDispatch : Answer → Occurrences Action
  | .a => EmptyDemandCoherence.pure .handledA
  | .b => EmptyDemandCoherence.pure .handledB
  | .emptyData => EmptyDemandCoherence.pure .handledEmptyData
  | .c => zero

/-- A matching arm for `a` whose body deliberately prunes. -/
def pruningDispatch : Answer → Occurrences Action
  | .a => zero
  | answer => selectiveDispatch answer

/-- An explicit catch-all arm handles values omitted by the specific arms. -/
def catchAllDispatch : Answer → Occurrences Action
  | .a => EmptyDemandCoherence.pure .handledA
  | .b => EmptyDemandCoherence.pure .handledB
  | .emptyData => EmptyDemandCoherence.pure .handledEmptyData
  | answer => EmptyDemandCoherence.pure (.handledOther answer)

/-- Positive: source zero selects the fallback. -/
theorem completed_source_zero_uses_fallback :
    sourceCase (zero : Occurrences Answer) selectiveDispatch
      (EmptyDemandCoherence.pure .fallback) =
        EmptyDemandCoherence.pure .fallback :=
  rfl

/-- Negative control: returning an inert atom named `Empty`-like data does not
select the fallback. -/
theorem returned_empty_is_ordinary_data :
    sourceCase (EmptyDemandCoherence.pure Answer.emptyData) selectiveDispatch
      (EmptyDemandCoherence.pure Action.fallback) =
        EmptyDemandCoherence.pure Action.handledEmptyData := by
  simp [selectiveDispatch]

/-- Omitting `c` from the arm set contributes zero; it does not run fallback. -/
theorem unmatched_c_is_not_source_absence :
    sourceCase (EmptyDemandCoherence.pure Answer.c) selectiveDispatch
      (EmptyDemandCoherence.pure Action.fallback) = zero := by
  simp [selectiveDispatch]

/-- A matched `a` arm whose body prunes also contributes zero without fallback. -/
theorem matching_body_pruning_is_not_source_absence :
    sourceCase (EmptyDemandCoherence.pure Answer.a) pruningDispatch
      (EmptyDemandCoherence.pure Action.fallback) = zero := by
  simp [pruningDispatch]

/-- If unmatched data needs handling, an explicit catch-all arm does it. -/
theorem explicit_catch_all_handles_c :
    sourceCase (EmptyDemandCoherence.pure Answer.c) catchAllDispatch
      (EmptyDemandCoherence.pure Action.fallback) =
        EmptyDemandCoherence.pure (.handledOther .c) := by
  simp [catchAllDispatch]

/-- Per-answer processing does not materialize or rematerialize an answer
tuple.  Unmatched `c` is pruned while `a` and `b` continue directly. -/
theorem several_answers_flow_through_dispatch :
    sourceCase [.a, .c, .b] selectiveDispatch
      (EmptyDemandCoherence.pure Action.fallback) =
      [.handledA, .handledB] :=
  rfl

/-- In contrast, `try (case ...) fallback` catches the zero produced after `c`
fails to match. -/
theorem post_dispatch_fallback_catches_unmatched_c :
    postDispatchOrElse (EmptyDemandCoherence.pure Answer.c) selectiveDispatch
      (EmptyDemandCoherence.pure Action.fallback) =
        EmptyDemandCoherence.pure Action.fallback := by
  simp [postDispatchOrElse_catches_downstream_zero, selectiveDispatch]

/-- Permanent separation canary: source-local fallback and post-dispatch
fallback disagree on an unmatched value. -/
theorem source_local_and_post_dispatch_are_distinct :
    sourceCase (EmptyDemandCoherence.pure Answer.c) selectiveDispatch
      (EmptyDemandCoherence.pure Action.fallback) ≠
        postDispatchOrElse (EmptyDemandCoherence.pure Answer.c)
          selectiveDispatch (EmptyDemandCoherence.pure Action.fallback) := by
  exact sourceCase_ne_postDispatchOrElse_of_downstream_zero
    .c selectiveDispatch (EmptyDemandCoherence.pure Action.fallback)
    (by simp [selectiveDispatch])
    (EmptyDemandCoherence.pure_ne_zero Action.fallback)

end Canary

end Mettapedia.Languages.MeTTa.SourceZeroCase
