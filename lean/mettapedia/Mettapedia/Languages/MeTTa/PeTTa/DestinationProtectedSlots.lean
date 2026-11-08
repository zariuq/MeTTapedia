import Mettapedia.Languages.MeTTa.PeTTa.DestinationScopeRefinement
import Mettapedia.Logic.LP.ConjunctiveUnification

/-!
# Protected observations in actual Destination scopes

The existing most-general source resolver earns each fixed ground read.
The scoped refinement theorem then transports it through actual choices,
calls, primitives and collection return. Ground values may differ between
occurrences carrying the same context; their witnesses are branch-local.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.ProtectedSlots

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Logic.LP.ConjunctiveUnification (applyTerm_of_isGround)
open RefinementTransport

def Fixed (bindings : Equations) (slot value : Atom) : Prop :=
  ∀ environment, Solves environment bindings → read environment slot = value

theorem read_ground (environment : Environment) (value : Atom) (ground : (encode value).isGround) :
    read environment value = value := by
  unfold read
  rw [applyTerm_of_isGround environment ground, decode_encode]

theorem fixed_of_resolved {bindings : Equations} {environment : Environment}
    (resolved : resolve bindings = some environment) (slot : Atom)
    (ground : (encode (read environment slot)).isGround) :
    Fixed bindings slot (read environment slot) := by
  intro other solved
  have absorbed := resolve_read_preserves resolved other solved slot
  rw [read_ground other _ ground] at absorbed
  exact absorbed.symm

theorem Fixed.extends {before after : Equations} {slot value : Atom}
    (fixed : Fixed before slot value) (extended : Extends before after) : Fixed after slot value :=
  fun environment solved => fixed environment (extended environment solved)

def GroundRead (bindings : Equations) (slot : Atom) : Prop :=
  ∃ value, (encode value).isGround ∧ Fixed bindings slot value

def groundSlot {Context : Type} (slot : Context → Atom) : BindingPredicate Context where
  holds context bindings := GroundRead bindings (slot context)
  closed _ _ _ before extended := by
    obtain ⟨value, ground, fixed⟩ := before
    exact ⟨value, ground, fixed.extends extended⟩

theorem actual_resolver_earns_ground_slot {Context : Type} (slot : Context → Atom)
    (context : Context) (bindings : Equations) (environment : Environment)
    (resolved : resolve bindings = some environment)
    (ground : (encode (read environment (slot context))).isGround) :
    (groundSlot slot).holds context bindings :=
  ⟨read environment (slot context), ground, fixed_of_resolved resolved (slot context) ground⟩

theorem reached_work_keeps_ground_slot {Context : Type} {policy : Policy}
    {program : SpaceSemantics.Program} (slot : Context → Atom)
    {before after : ScopedCursor Context}
    (path : Relation.ReflTransGen (Continues policy program) before after)
    (valid : ScopesValid before.2.scopes) (good : ScopesGood (groundSlot slot) before.2.scopes)
    (scope : CollectionScope Context) (member : scope ∈ after.2.scopes)
    (work : CollectionWork Context) (present : work ∈ scope.frontier) :
    ∃ value, (encode value).isGround ∧ Fixed work.1.bindings (slot work.2.1) value :=
  ((path_preserves path valid good).2 scope member).work work present

/-- An accepted return equates the actual caller destination to its source
slot. The later solved presentation therefore returns that protected value,
even when the destination was an alias or had prior constraints. -/
theorem accepted_protected_return {before after : Equations} {slot destination value : Atom}
    (fixed : Fixed before slot value) (returned : Refinement before slot destination (some after))
    (environment : Environment) (resolved : resolve after = some environment) :
    read environment destination = value := by
  have solved := resolve_sound resolved
  cases returned with
  | accepted witness old new =>
      have two := (solves_append_equation _ _ _ _).mp solved
      exact two.2.symm.trans (fixed environment two.1)

/-- The inherited world and pending siblings are exactly the ones retained
by the actual source rule; an incompatible protected return removes only
its own active occurrence. -/
theorem conflicting_return_refused {before : Equations} {slot value other : Atom}
    (fixed : Fixed before slot value) (ground : (encode other).isGround) (different : value ≠ other) :
    Refinement before slot other none := by
  apply Refinement.refused
  rintro ⟨environment, solved, same⟩
  apply different
  rw [fixed environment solved, read_ground environment other ground] at same
  exact same

namespace Controls

def seven : Atom := .grounded (.int 7)
def eight : Atom := .grounded (.int 8)
def slot : Atom := .var "protected"

theorem seven_fixed : Fixed [(slot, seven)] slot seven := by
  intro environment solved
  have same := solved (slot, seven) (by simp)
  rw [read_ground environment seven (by simp [seven, encode, Mettapedia.Logic.LP.Term.isGround])] at same
  exact same

theorem eight_fixed : Fixed [(slot, eight)] slot eight := by
  intro environment solved
  have same := solved (slot, eight) (by simp)
  rw [read_ground environment eight (by simp [eight, encode, Mettapedia.Logic.LP.Term.isGround])] at same
  exact same

/-- Equal contexts do not collapse two distinct actual input occurrences. -/
theorem same_context_can_retain_distinct_ground_occurrences :
    (groundSlot (fun _ : Unit => slot)).holds () [(slot, seven)] ∧
      (groundSlot (fun _ : Unit => slot)).holds () [(slot, eight)] ∧ seven ≠ eight := by
  exact ⟨⟨seven, by simp [seven, encode, Mettapedia.Logic.LP.Term.isGround], seven_fixed⟩,
    ⟨eight, by simp [eight, encode, Mettapedia.Logic.LP.Term.isGround], eight_fixed⟩, by decide⟩

theorem changing_ground_slot_is_not_a_refinement :
    ¬ Extends [(slot, seven)] [(slot, eight)] := by
  intro extended
  have inherited := seven_fixed.extends extended
  let environment : Environment := fun _ => encode eight
  have solved : Solves environment [(slot, eight)] := by
    intro pair present
    cases List.mem_singleton.mp present
    simp [read, environment, slot, eight, encode, decode, Mettapedia.Logic.LP.Subst.applyTerm]
  have same := inherited environment solved
  have observed : read environment slot = eight := by
    simp [read, environment, slot, eight, encode, decode, Mettapedia.Logic.LP.Subst.applyTerm]
  rw [observed] at same
  cases same

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.ProtectedSlots
