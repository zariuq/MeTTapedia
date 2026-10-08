import Mettapedia.OSLF.Syntax.GSOSNativeGuard
import Mettapedia.OSLF.Syntax.DeterministicGSOSEdgeControls
import Mettapedia.GSLT.Topos.PresheafPredicateHigherOrderControls

/-!
# Separating controls for native negative availability

A genuinely growing event presheaf separates absence now from native
future absence. Empty occurrence carriers cannot test transition support.
Native equality predicates also show why arbitrary definable guards are
richer than the availability fragment of a natural deterministic GSOS law.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS.NativeGuardControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Mettapedia.TypeTheory PresheafEventCertificates
open Mettapedia.GSLT.Topos

namespace Growing

open PresheafPredicateHigherOrderControls

/-- All events have the one fixed action. Their actual source fibre grows
from Empty to Unit along a nonidentity context arrow. -/
def span : EventSpan programs programs where
  events := growing
  source := forgetGrowth
  target := forgetGrowth

theorem absence_now :
    ¬ ∃ event : span.events.obj spot,
      event ∈ (⊤ : Subfunctor span.events).obj spot ∧ span.source.app spot event = () := by
  rintro ⟨event, _, _⟩
  exact Empty.elim event

theorem native_absence_fails :
    () ∉ (PresheafEventAbsence.absent span.source (⊤ : Subfunctor span.events)).obj spot := by
  rw [PresheafEventAbsence.mem_absent]
  intro holds
  exact holds future restriction ⟨(), trivial, rfl⟩

/-- The two propositions disagree on the same supplied source. -/
theorem current_absence_is_not_native_negation :
    ¬ ((¬ ∃ event : span.events.obj spot,
        event ∈ (⊤ : Subfunctor span.events).obj spot ∧ span.source.app spot event = ()) ↔
      () ∈ (PresheafEventAbsence.absent span.source (⊤ : Subfunctor span.events)).obj spot) := by
  intro same
  exact native_absence_fails (same.mp absence_now)

theorem availability_not_reflected :
    ¬ PresheafEventAbsence.ReflectsAvailability span.source (⊤ : Subfunctor span.events) := by
  intro reflection
  obtain ⟨event, _, _⟩ := reflection restriction () () trivial rfl
  exact Empty.elim event

end Growing

namespace EmptyOrigins

open Controls EdgeControls EdgeReadout NativeGuard

theorem genuine_step_present :
    Operational.coalgebra law (variableSteps.app world) PUnit.unit () firstEvent.source 7 =
      some firstEvent.target := firstEvent.valid

theorem event_support_empty :
    firstEvent.source ∉ (enabled law worlds variableSteps Empty () 7).obj world := by
  rw [mem_enabled]
  rintro ⟨event, _, _⟩
  exact Empty.elim event.origin

/-- Empty origins make every future event fibre empty, even though the
independently checked operational transition really exists. -/
theorem false_absence_if_origins_erased :
    firstEvent.source ∈ (noAction law worlds variableSteps Empty () 7).obj world := by
  apply (PresheafEventAbsence.mem_absent (eventSpan law worlds variableSteps Empty ()).source
    (labelPredicate law worlds variableSteps Empty () 7) world firstEvent.source).mpr
  intro future change present
  obtain ⟨event, _, _⟩ := present
  exact Empty.elim event.origin

theorem inhabited_origins_recover_positive_support :
    firstEvent.source ∈ (enabled law worlds variableSteps (Fin 2) () 7).obj world :=
  (mem_enabled law worlds variableSteps (Fin 2) () 7 world firstEvent.source).mpr
    ⟨firstEvent, rfl, rfl⟩

theorem inhabited_origins_reject_negative :
    firstEvent.source ∉ (noAction law worlds variableSteps (Fin 2) () 7).obj world := by
  intro holds
  have none := (noAction_iff_none law worlds variableSteps () 7 world firstEvent.source).mp holds
  rw [genuine_step_present] at none
  cases none

end EmptyOrigins

namespace GuardFormat

open PresheafPredicateHigherOrderControls

def collapse : booleans ⟶ programs where
  app _ := ↾fun _ => ()

theorem native_equality_false_before :
    (false, true) ∉ (PresheafPredicateFirstOrder.equality booleans).obj spot := by
  intro holds
  exact Bool.false_ne_true ((PresheafPredicateFirstOrder.mem_equality booleans spot (false, true)).mp holds)

theorem native_equality_true_after_collision :
    (collapse ⊗ₘ collapse).app spot (false, true) ∈
      (PresheafPredicateFirstOrder.equality programs).obj spot :=
  (PresheafPredicateFirstOrder.mem_equality programs spot _).mpr rfl

/-- A native predicate can gain truth after an input collision. Such a
test cannot be promoted to a natural deterministic availability guard. -/
theorem native_equality_does_not_reflect :
    ¬ ((false, true) ∈ (PresheafPredicateFirstOrder.equality booleans).obj spot ↔
      (collapse ⊗ₘ collapse).app spot (false, true) ∈
        (PresheafPredicateFirstOrder.equality programs).obj spot) := by
  intro same
  exact native_equality_false_before (same.mpr native_equality_true_after_collision)

theorem corresponding_boolean_test_not_natural :
    Controls.equalityProbe Controls.unequal ≠
      Controls.equalityProbe (mapArguments Controls.actions Controls.collapseBool Controls.unequal) :=
  Controls.equality_test_not_natural

end GuardFormat

end Mettapedia.OSLF.DeterministicGSOS.NativeGuardControls
