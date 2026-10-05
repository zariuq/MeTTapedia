import Mathlib.Data.List.Nodup

/-!
# Linked activation scopes

An activation writes its saved predecessor into the activated object's own
link. Leaving restores the saved top; it does not undo that link or any payload
updates. The active list is an independent specification of the reachable
chain. An object may be reused after leaving, but entering an already active
object is not a second activation record.

The finite traversal retains its cursor on exhaustion. A complete traversal
follows from the representation invariant, without imposing a runtime depth
bound. Payload ownership and physical pointer validity are separate contracts.
-/

set_option autoImplicit false

namespace Mettapedia.Machines

universe u

structure LinkedScopeStack (Identity : Type u) where
  top : Option Identity
  parent : Identity → Option Identity

namespace LinkedScopeStack

variable {Identity : Type u}

/-- Every active link names precisely the next active object. Links of
inactive objects are deliberately unconstrained. -/
def MatchesLinks (parent : Identity → Option Identity) : List Identity → Prop
  | [] => True
  | first :: rest => parent first = rest.head? ∧ MatchesLinks parent rest

structure Represents (stack : LinkedScopeStack Identity) (active : List Identity) : Prop where
  top : stack.top = active.head?
  distinct : active.Nodup
  links : MatchesLinks stack.parent active

theorem matchesLinks_congr {first second : Identity → Option Identity}
    {active : List Identity} (same : ∀ object ∈ active, first object = second object)
    (linked : MatchesLinks first active) : MatchesLinks second active := by
  induction active with
  | nil => trivial
  | cons object rest ih =>
      exact ⟨(same object List.mem_cons_self).symm.trans linked.1,
        ih (fun next member => same next (List.mem_cons_of_mem _ member)) linked.2⟩

def enter [DecidableEq Identity] (stack : LinkedScopeStack Identity)
    (object : Identity) : LinkedScopeStack Identity where
  top := some object
  parent := fun candidate => if candidate = object then stack.top else stack.parent candidate

def leave (stack : LinkedScopeStack Identity) (saved : Option Identity) :
    LinkedScopeStack Identity := { stack with top := saved }

theorem enter_represents [DecidableEq Identity]
    {stack : LinkedScopeStack Identity} {active : List Identity} {object : Identity}
    (represented : stack.Represents active) (fresh : object ∉ active) :
    (stack.enter object).Represents (object :: active) := by
  refine ⟨rfl, List.nodup_cons.mpr ⟨fresh, represented.distinct⟩, ?_⟩
  refine ⟨?_, matchesLinks_congr ?_ represented.links⟩
  · simp [enter, represented.top]
  · intro candidate member
    have different : candidate ≠ object := by
      intro same
      exact fresh (same ▸ member)
    simp [enter, different]

/-- A matching leave restores the original active chain, even though the
now inactive object's predecessor remains written. -/
theorem leave_enter_represents [DecidableEq Identity]
    {stack : LinkedScopeStack Identity} {active : List Identity} {object : Identity}
    (represented : stack.Represents active) (fresh : object ∉ active) :
    ((stack.enter object).leave stack.top).Represents active := by
  have pushed := enter_represents represented fresh
  exact ⟨represented.top, represented.distinct, pushed.links.2⟩

/-- A bounded observation follows the links directly and retains the first
unvisited object. This is independent of the list specification. -/
def follow (parent : Identity → Option Identity) :
    Nat → Option Identity → List Identity × Option Identity
  | _, none => ([], none)
  | 0, some object => ([], some object)
  | fuel + 1, some object =>
      let rest := follow parent fuel (parent object)
      (object :: rest.1, rest.2)

theorem follow_of_matches {parent : Identity → Option Identity}
    {active : List Identity} (linked : MatchesLinks parent active) (extra : Nat) :
    follow parent (active.length + extra) active.head? = (active, none) := by
  induction active with
  | nil => cases extra <;> rfl
  | cons object rest ih =>
      have fuel : (object :: rest).length + extra = (rest.length + extra) + 1 := by
        simp only [List.length_cons]
        omega
      rw [fuel]
      simp only [List.head?_cons, follow]
      rw [linked.1, ih linked.2]

theorem follow_complete {stack : LinkedScopeStack Identity} {active : List Identity}
    (represented : stack.Represents active) (extra : Nat) :
    follow stack.parent (active.length + extra) stack.top = (active, none) := by
  rw [represented.top]
  exact follow_of_matches represented.links extra

theorem entering_top_makes_self_link [DecidableEq Identity]
    (stack : LinkedScopeStack Identity) (object : Identity)
    (active : stack.top = some object) :
    (stack.enter object).parent object = some object := by
  simp [enter, active]

theorem self_link_has_no_finite_representation
    {stack : LinkedScopeStack Identity} {object : Identity}
    (top : stack.top = some object) (self : stack.parent object = some object)
    (active : List Identity) : ¬ stack.Represents active := by
  intro represented
  cases active with
  | nil =>
      have impossible : (some object : Option Identity) = none :=
        top.symm.trans represented.top
      cases impossible
  | cons first rest =>
      have same : object = first := Option.some.inj (top.symm.trans represented.top)
      subst first
      have next : rest.head? = some object := represented.links.1.symm.trans self
      have member : object ∈ rest := by
        cases rest with
        | nil => simp at next
        | cons head tail =>
            have same : head = object := Option.some.inj next
            simp [same]
      exact (List.nodup_cons.mp represented.distinct).1 member

theorem reenter_top_refused [DecidableEq Identity]
    (stack : LinkedScopeStack Identity) (object : Identity)
    (active : stack.top = some object) (presentation : List Identity) :
    ¬ (stack.enter object).Represents presentation :=
  self_link_has_no_finite_representation rfl
    (entering_top_makes_self_link stack object active) presentation

theorem self_link_retains_cursor (parent : Identity → Option Identity)
    (object : Identity) (self : parent object = some object) (fuel : Nat) :
    follow parent fuel (some object) = (List.replicate fuel object, some object) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp [follow, self, ih, List.replicate_succ]

namespace Controls

def empty : LinkedScopeStack Nat := ⟨none, fun _ => none⟩

theorem empty_represents : empty.Represents [] := ⟨rfl, List.nodup_nil, trivial⟩

theorem nested_enter_and_leave :
    (((empty.enter 1).enter 2).leave (some 1)).Represents [1] := by
  exact leave_enter_represents (enter_represents empty_represents (by simp)) (by simp)

theorem retired_object_can_resume :
    ((((empty.enter 1).leave none).enter 1)).Represents [1] := by
  exact enter_represents (leave_enter_represents empty_represents (by simp)) (by simp)

theorem same_object_is_not_a_second_frame :
    ¬ ((empty.enter 1).enter 1).Represents [1, 1] := by
  exact reenter_top_refused (empty.enter 1) 1 rfl [1, 1]

theorem repeated_entry_never_completes (fuel : Nat) :
    follow ((empty.enter 1).enter 1).parent fuel (some 1) =
      (List.replicate fuel 1, some 1) :=
  self_link_retains_cursor ((empty.enter 1).enter 1).parent 1 (by simp [enter]) fuel

end Controls
end LinkedScopeStack
end Mettapedia.Machines
