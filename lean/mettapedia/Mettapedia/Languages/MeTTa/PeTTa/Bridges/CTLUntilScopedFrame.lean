import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilScopedCapture

/-!
# Transport through prepared and captured query frames

Every captured body retains the actual handle-preparation equation before
its row equations. Closed inherited readings survive the resulting principal
solution; fresh retained names survive only when they avoid the captured slot.
The literal satisfaction capture adds no row equation, but keeps preparation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilScopedFrame

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor)
open CTLUntilSourceRows (number)

theorem capture_inherited (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle)
    (pattern body : Atom) (captured : Subst) (environment : Environment)
    (solved : Solves environment (ScopedQuerySource.bodyControl
      (ScopedMatchPreparation.ready caller destination handle pattern body)
      captured body destination caller.goals).bindings) :
    Solves environment caller.bindings := by
  apply ScopedMatchPreparation.ready_inherited caller destination handle pattern body environment
  intro pair member
  exact solved pair (List.mem_append_left _ member)

theorem capture_closed_reading (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle)
    (pattern body : Atom) (captured : Subst) (before after : Environment) (code value : Atom)
    (beforeResolved : resolve caller.bindings = some before)
    (afterResolved : resolve (ScopedQuerySource.bodyControl
      (ScopedMatchPreparation.ready caller destination handle pattern body)
      captured body destination caller.goals).bindings = some after)
    (reading : read before code = value) (closed : ∀ environment, read environment value = value) :
    read after code = value :=
  CapturedQueryOperands.resolved_forces beforeResolved code value reading closed after
    (capture_inherited caller destination handle pattern body captured after (resolve_sound afterResolved))

/-- A fresh numeric capture has a principal solution after the actual handle
operand has been prepared. No selected post-frame is supplied as a premise. -/
theorem number_capture_resolves (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle)
    (pattern body : Atom) (slot : String) (value : Nat) (principal : Environment)
    (resolved : resolve caller.bindings = some principal) (fresh : FreshFor slot caller.bindings)
    (retained : slot ∈ (ScopedMatchPreparation.entry caller destination handle pattern body).support) :
    ∃ after, resolve (ScopedQuerySource.bodyControl
      (ScopedMatchPreparation.ready caller destination handle pattern body)
      [(slot, number value)] body destination caller.goals).bindings = some after := by
  let ready := ScopedMatchPreparation.ready caller destination handle pattern body
  obtain ⟨prepared, preparedResolved⟩ := resolve_complete
    (ScopedMatchPreparation.ready_consistent caller destination handle pattern body
      ⟨principal, resolve_sound resolved⟩)
  have stillFresh := ScopedMatchPreparation.retained_fresh caller destination handle pattern body slot fresh retained
  exact resolve_complete (CTLUntilSourceCapture.unbound_capture_consistent ready.bindings prepared slot slot
    (number value) preparedResolved
    (ClosedOnceQueryFrame.fresh_read ready.bindings slot prepared stillFresh preparedResolved)
    (CTLUntilSourceCapture.number_closed value))

theorem number_capture_read (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle)
    (pattern body : Atom) (slot : String) (value : Nat) (principal : Environment)
    (resolved : resolve (ScopedQuerySource.bodyControl
      (ScopedMatchPreparation.ready caller destination handle pattern body)
      [(slot, number value)] body destination caller.goals).bindings = some principal) :
    read principal (.var slot) = number value :=
  CTLUntilSourceCapture.captured_number_read
    (ScopedMatchPreparation.ready caller destination handle pattern body).bindings slot value principal resolved

theorem number_capture_fresh (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle)
    (pattern body : Atom) (slot name : String) (value : Nat)
    (fresh : FreshFor name caller.bindings)
    (retained : name ∈ (ScopedMatchPreparation.entry caller destination handle pattern body).support)
    (apart : name ≠ slot) :
    FreshFor name (ScopedQuerySource.bodyControl
      (ScopedMatchPreparation.ready caller destination handle pattern body)
      [(slot, number value)] body destination caller.goals).bindings :=
  CTLUntilSourceCapture.fresh_after_capture
    (ScopedMatchPreparation.ready caller destination handle pattern body).bindings slot name value
    (ScopedMatchPreparation.retained_fresh caller destination handle pattern body name fresh retained) apart

theorem empty_capture_resolves (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle)
    (pattern body : Atom) (principal : Environment) (resolved : resolve caller.bindings = some principal) :
    ∃ after, resolve (ScopedQuerySource.bodyControl
      (ScopedMatchPreparation.ready caller destination handle pattern body)
      [] body destination caller.goals).bindings = some after := by
  simpa only [ScopedQuerySource.bodyControl, ScopedQuerySource.extend, List.map_nil, List.append_nil] using
    resolve_complete (ScopedMatchPreparation.ready_consistent caller destination handle pattern body
      ⟨principal, resolve_sound resolved⟩)

theorem empty_capture_fresh (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle)
    (pattern body : Atom) (name : String) (fresh : FreshFor name caller.bindings)
    (retained : name ∈ (ScopedMatchPreparation.entry caller destination handle pattern body).support) :
    FreshFor name (ScopedQuerySource.bodyControl
      (ScopedMatchPreparation.ready caller destination handle pattern body)
      [] body destination caller.goals).bindings := by
  simpa only [ScopedQuerySource.bodyControl, ScopedQuerySource.extend, List.map_nil, List.append_nil] using
    ScopedMatchPreparation.retained_fresh caller destination handle pattern body name fresh retained

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilScopedFrame
