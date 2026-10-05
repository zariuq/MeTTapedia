import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolGuarded

/-!
# Guarded protocol source and activation controls

The binary listener releases both ordered fields and a further unary listener.
Normalization retains duplicate message occurrences and keeps suspended
continuations opaque. Replication of an autonomous private allocator is
outside the source grammar, even when its body otherwise belongs to it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.GuardedControls

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open ScopedActiveFrontier

abbrev context : Ctx sig := [.nm, .nm, .nm]
def channel : Name context := .var .zero
def first : Name context := .var (.succ .zero)
def second : Name context := .var (.succ (.succ .zero))

def body : Proc (.nm :: .nm :: context) :=
  par (out2 (.var (.succ (.succ .zero))) (.var .zero) (.var (.succ .zero)))
    (inp1 (.var (.succ (.succ .zero)))
      (out1 (.var (.succ (.succ (.succ .zero)))) (.var .zero)))

theorem body_guarded : Guarded body := .par (.out2 _ _ _) (.inp1 _ (.out1 _ _))

def returned : Proc context :=
  par (out2 channel first second) (inp1 channel (out1 (weaken channel) (.var .zero)))

theorem received_fields_in_order : openPair body first second = returned := rfl

theorem actual_binary_receipt :
    Step (par (out2 channel first second) (inp2 channel body)) returned := by
  rw [← received_fields_in_order]
  exact .comm2 _ _ _ _

theorem released_continuation_stays_guarded : Guarded returned := by
  rw [← received_fields_in_order]
  exact body_guarded.openPair first second

theorem persistent_binary_listener_is_guarded : Guarded (rep (inp2 channel body)) :=
  .server2 _ body_guarded

theorem suspended_body_is_one_atom :
    (ScopedActiveFrontier.normalize (inp2 channel body)).atoms.length = 1 := by
  rw [normalize_inp2]
  rfl

theorem equal_messages_keep_two_occurrences :
    (ScopedActiveFrontier.normalize
      (par (out2 channel first second) (out2 channel first second))).atoms.length = 2 := by
  rw [normalize_par, merge_occurrence_count, normalize_out2]
  rfl

theorem equal_message_frontier_is_classified :
    ∀ atom ∈ (ScopedActiveFrontier.normalize
      (par (out2 channel first second) (out2 channel first second))).atoms,
      GuardedAtom atom := (Guarded.par (.out2 _ _ _) (.out2 _ _ _)).normalized_atoms

def allocatorBody : Proc [] := nu (out1 (.var .zero) (.var .zero))

theorem private_body_is_guarded : Guarded allocatorBody := .nu (.out1 _ _)

theorem autonomous_allocator_replication_is_excluded : ¬ Guarded (rep allocatorBody) := by
  intro guarded
  cases guarded

theorem process_variable_is_excluded {Γ : Ctx sig} (processName : Var Γ .pr) :
    ¬ Guarded (.var processName : Proc Γ) := by
  intro guarded
  cases guarded

/-- Canonical guardedness is not falsely claimed of every static representative.
The runtime can retain a guarded canonical source beside such a representative. -/
theorem equations_can_insert_a_unit_inside_a_server :
    StructuralEq (rep (inp2 channel body)) (rep (par (inp2 channel body) nil)) :=
  .rep (.symm (.parUnit _))

theorem server_with_inserted_unit_is_not_canonical :
    ¬ Guarded (rep (par (inp2 channel body) nil)) := by
  intro guarded
  cases guarded

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.GuardedControls
