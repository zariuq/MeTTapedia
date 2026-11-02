import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Lean.Elab.Tactic.Omega

/-!
# Fresh scopes for a rule and its selected occurrence uses

One reservation gives the whole rule one scope, followed by one scope per
take port and read port. Ports retain their physical occurrence choices;
repeated reads still receive distinct scopes. The finite occupied ledger
must account for every live scope, including continuations and captures.
Relating that ledger to a complete runtime world is a separate obligation.

Scopes are natural numbers with no fixed bound. The reservation retains old
scopes, so a later reservation cannot reuse a scope still in this ledger.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActivationScopes

universe u
variable {O : Type u}

def count (selection : Selection O) : Nat :=
  1 + selection.taken.length + selection.read.length

abbrev Port (selection : Selection O) := Fin (count selection)

def rulePort (selection : Selection O) : Port selection :=
  ⟨0, by simp [count]⟩

def takePort (selection : Selection O) (position : Fin selection.taken.length) : Port selection :=
  ⟨1 + position.val, by have := position.isLt; dsimp [count]; omega⟩

def readPort (selection : Selection O) (position : Fin selection.read.length) : Port selection :=
  ⟨1 + selection.taken.length + position.val, by have := position.isLt; dsimp [count]; omega⟩

def start (occupied : Finset Nat) : Nat := occupied.sup id + 1

def scopeAt (occupied : Finset Nat) {size : Nat} (port : Fin size) : Nat :=
  start occupied + port.val

def reserved (occupied : Finset Nat) (selection : Selection O) : Finset Nat :=
  Finset.Ico (start occupied) (start occupied + count selection)

def after (occupied : Finset Nat) (selection : Selection O) : Finset Nat :=
  occupied ∪ reserved occupied selection

theorem occupied_lt_start (occupied : Finset Nat) {scope : Nat} (member : scope ∈ occupied) :
    scope < start occupied := by
  have bound := Finset.le_sup (f := id) member
  dsimp [start]
  simpa only [id] using Nat.lt_succ_of_le bound

theorem at_mem_reserved (occupied : Finset Nat) (selection : Selection O) (port : Port selection) :
    scopeAt occupied port ∈ reserved occupied selection := by
  rw [reserved, Finset.mem_Ico]
  have := port.isLt
  dsimp [scopeAt]
  omega

theorem at_fresh (occupied : Finset Nat) {size : Nat} (port : Fin size) :
    scopeAt occupied port ∉ occupied := by
  intro member
  have below := occupied_lt_start occupied member
  dsimp [scopeAt] at below
  omega

theorem at_injective (occupied : Finset Nat) (size : Nat) :
    Function.Injective (scopeAt occupied (size := size)) := by
  intro first second same
  apply Fin.ext
  dsimp [scopeAt] at same
  omega

theorem takePort_injective (selection : Selection O) : Function.Injective (takePort selection) := by
  intro first second same
  apply Fin.ext
  have values := congrArg Fin.val same
  dsimp [takePort] at values
  omega

theorem readPort_injective (selection : Selection O) : Function.Injective (readPort selection) := by
  intro first second same
  apply Fin.ext
  have values := congrArg Fin.val same
  dsimp [readPort] at values
  omega

theorem rulePort_ne_takePort (selection : Selection O) (position : Fin selection.taken.length) :
    rulePort selection ≠ takePort selection position := by
  intro same
  have values := congrArg Fin.val same
  dsimp [rulePort, takePort] at values
  omega

theorem rulePort_ne_readPort (selection : Selection O) (position : Fin selection.read.length) :
    rulePort selection ≠ readPort selection position := by
  intro same
  have values := congrArg Fin.val same
  dsimp [rulePort, readPort] at values
  omega

theorem takePort_ne_readPort (selection : Selection O) (taken : Fin selection.taken.length)
    (read : Fin selection.read.length) : takePort selection taken ≠ readPort selection read := by
  intro same
  have values := congrArg Fin.val same
  have bound := taken.isLt
  dsimp [takePort, readPort] at values
  omega

theorem different_ports_have_different_scopes (occupied : Finset Nat) {size : Nat}
    {first second : Fin size} (different : first ≠ second) :
    scopeAt occupied first ≠ scopeAt occupied second :=
  fun same => different (at_injective occupied size same)

theorem reserved_disjoint (occupied : Finset Nat) (selection : Selection O) :
    Disjoint (reserved occupied selection) occupied := by
  apply Finset.disjoint_left.mpr
  intro scope member old
  obtain ⟨lower, _⟩ := Finset.mem_Ico.mp member
  have below := occupied_lt_start occupied old
  omega

theorem reserved_card (occupied : Finset Nat) (selection : Selection O) :
    (reserved occupied selection).card = count selection := by
  simp [reserved]

theorem old_scopes_retained (occupied : Finset Nat) (selection : Selection O) :
    occupied ⊆ after occupied selection := Finset.subset_union_left

theorem allocated_scopes_retained (occupied : Finset Nat) (selection : Selection O) :
    reserved occupied selection ⊆ after occupied selection := Finset.subset_union_right

theorem later_scopes_are_fresh (occupied : Finset Nat) (first second : Selection O)
    (port : Port second) : scopeAt (after occupied first) port ∉ reserved occupied first := by
  intro old
  exact at_fresh (after occupied first) port (allocated_scopes_retained occupied first old)

theorem successive_reservations_disjoint (occupied : Finset Nat) (first second : Selection O) :
    Disjoint (reserved (after occupied first) second) (reserved occupied first) := by
  exact (reserved_disjoint (after occupied first) second).mono_right
    (allocated_scopes_retained occupied first)

theorem start_strictly_advances (occupied : Finset Nat) (selection : Selection O) :
    start occupied < start (after occupied selection) := by
  have retained : start occupied ∈ after occupied selection := by
    exact allocated_scopes_retained occupied selection
      (at_mem_reserved occupied selection (rulePort selection))
  exact occupied_lt_start (after occupied selection) retained

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActivationScopes
