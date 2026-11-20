import Mettapedia.Machines.TIsa.P1WordLiveness

/-! # Continuations after an early-loop body

The p1 loop fixes its iteration count at entry. The remaining count is
related to the unsigned distance between its live index and bound at a
latch. The finished body may also clear the Boolean continuation register.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.P1EarlyLoopContinuation

open P1Source P1WordExecution P1WordLiveness

structure LoopRegisters where
  index : Reg
  bound : Reg
  condition : Reg

def remaining (index bound : Word) : Nat :=
  bound.toNat - (index.toNat + 1)

def increments (registers : LoopRegisters) (state : State) (enabled : Bool) : State :=
  if enabled then state.write registers.index (state.registers registers.index + 1) else state

def reenters (index bound : Word) (enabled : Bool) : Bool :=
  enabled && decide (index.toNat + 1 < bound.toNat)

def resume (registers : LoopRegisters) (body : Stmt) (left : Nat) (state : State) : Flow :=
  continueLoop state (some registers.condition) fun following =>
    loop (execute · body) registers.index (some registers.condition) left
      (following.write registers.index (following.registers registers.index + 1))

theorem iteration (registers : LoopRegisters) (body : Stmt) (left : Nat) (state : State) :
    loop (execute · body) registers.index (some registers.condition) (left + 1) state =
      continueLoop state (some registers.condition) fun started =>
        (execute started body).thenContinue (resume registers body left) := rfl

theorem index_successor (index bound : Word) (inside : index.toNat < bound.toNat) :
    (index + 1).toNat = index.toNat + 1 := by
  have maxBound := bound.isLt
  change (index + (1#64)).toNat = _
  rw [BitVec.toNat_add, show (1#64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]

theorem rank (index bound : Word)
    (inside : index.toNat < bound.toNat) :
    bound.toNat - index.toNat = remaining index bound + 1 ∧
      bound.toNat - (index + 1).toNat = remaining index bound := by
  rw [index_successor index bound inside]
  unfold remaining
  omega

theorem at_latch (registers : LoopRegisters) (body : Stmt) (left : Nat) (state : State)
    (enabled : Bool) (known : state.registers registers.condition = booleanWord enabled)
    (coherent : left = remaining (state.registers registers.index) (state.registers registers.bound)) :
    resume registers body left state =
      let next := increments registers state enabled
      if reenters (state.registers registers.index) (state.registers registers.bound) enabled then
        loop (execute · body) registers.index (some registers.condition) left next
      else .continuing next := by
  cases enabled with
  | false => simp [resume, continueLoop, known, booleanWord, increments, reenters]
  | true =>
    simp only [resume, continueLoop, known, booleanWord, if_true, increments, reenters,
      Bool.true_and, decide_eq_true_eq]
    split
    · rfl
    · rename_i done
      have exhausted : left = 0 := by
        rw [coherent]
        unfold remaining
        omega
      rw [exhausted]
      rfl

theorem resume_observes (registers : LoopRegisters) (body : Stmt) (left : Nat)
    (head live : Finset Reg) (visible : live ⊆ head)
    (guarded : registers.condition ∈ head) (indexed : registers.index ∈ head)
    (stable : liveBefore body head ⊆ head) (before after : State)
    (same : Agree head before after) :
    Observes live (resume registers body left before) (resume registers body left after) := by
  have guard := same.registers registers.condition guarded
  simp only [resume, continueLoop, guard]
  split
  · rw [same.registers registers.index indexed]
    exact loop_observes body registers.index (some registers.condition) head live visible
      (by simpa using Finset.singleton_subset_iff.mpr guarded) indexed stable left _ _
      ((same.mono (Finset.erase_subset registers.index head)).write _)
  · split
    · exact .continuing (same.mono visible)
    · exact .returned same.toStorage

theorem resume_flow_observes (registers : LoopRegisters) (body : Stmt) (left : Nat)
    (head live : Finset Reg) (visible : live ⊆ head)
    (guarded : registers.condition ∈ head) (indexed : registers.index ∈ head)
    (stable : liveBefore body head ⊆ head) {before after : Flow}
    (same : Observes head before after) :
    Observes live (before.thenContinue (resume registers body left))
      (after.thenContinue (resume registers body left)) := by
  cases same with
  | continuing ready => exact resume_observes registers body left head live visible guarded indexed stable _ _ ready
  | returned storage => exact .returned storage

end Mettapedia.Machines.TIsa.P1EarlyLoopContinuation
