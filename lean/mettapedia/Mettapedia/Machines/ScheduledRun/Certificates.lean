import Mettapedia.Machines.ScheduledRun.Sharpness

/-!
# Executable finite lasso certificates with segment-local clock licences

A certificate is a nonempty cyclic word of actual states and its entry turn.
The checker validates every chosen edge and, under rotating choice, that each
arity divides the word length. Its soundness connects this finite data to the
actual run, not to a newly defined reference evaluator. No transient prefix
arity is needed. The fixed `next` function and controller are part of the
certificate's context; the certificate does not survive arbitrary redefinition.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ScheduledRun

universe u
variable {S : Type u}

def localPeriodCheck (mode : Mode) (count period : Nat) : Bool :=
  match mode with
  | .canonical => true
  | .rotating => decide (count ∣ period)

theorem localPeriodCheck_sound (mode : Mode) (start period count : Nat)
    (checked : localPeriodCheck mode count period = true) :
    ShiftCompatible mode.schedule start period count := by
  cases mode with
  | canonical => exact canonical_shift_compatible _ _ _
  | rotating => exact rotating_shift_compatible _ _ _ (of_decide_eq_true checked)

def cyclicAt (path : List S) (positive : 0 < path.length) (offset : Nat) : S :=
  path.get ⟨offset % path.length, Nat.mod_lt _ positive⟩

theorem cyclicAt_lt (path : List S) (positive : 0 < path.length) (index : Fin path.length) :
    cyclicAt path positive index.val = path.get index := by
  apply congrArg path.get
  exact Fin.ext (Nat.mod_eq_of_lt index.isLt)

theorem cyclicAt_length (path : List S) (positive : 0 < path.length) :
    cyclicAt path positive path.length = cyclicAt path positive 0 := by
  apply congrArg path.get
  apply Fin.ext
  simp

variable [DecidableEq S]

def checkLoop (next : S → List S) (mode : Mode) (start : Nat) (path : List S) : Bool :=
  if empty : path.length = 0 then false
  else
    (List.finRange path.length).all fun index =>
      decide (step next mode.schedule (start + index.val) (some (path.get index)) =
        some (cyclicAt path (Nat.pos_of_ne_zero empty) (index.val + 1))) &&
      localPeriodCheck mode (next (path.get index)).length path.length

theorem checkLoop_spec (next : S → List S) (mode : Mode) (start : Nat)
    (path : List S) (positive : 0 < path.length) :
    checkLoop next mode start path = true ↔
      ∀ index : Fin path.length,
        step next mode.schedule (start + index.val) (some (path.get index)) =
          some (cyclicAt path positive (index.val + 1)) ∧
        localPeriodCheck mode (next (path.get index)).length path.length = true := by
  simp [checkLoop, Nat.ne_of_gt positive, List.all_eq_true]

theorem checkLoop_nonempty (next : S → List S) (mode : Mode) (start : Nat) (path : List S)
    (checked : checkLoop next mode start path = true) : 0 < path.length := by
  apply Nat.pos_of_ne_zero
  intro empty
  simp [checkLoop, empty] at checked

theorem checkLoop_prefix (next : S → List S) (mode : Mode) (initial : S) (start : Nat)
    (path : List S) (positive : 0 < path.length) (checked : checkLoop next mode start path = true)
    (entry : run next mode.schedule initial start = some (cyclicAt path positive 0)) :
    ∀ offset, offset ≤ path.length →
      run next mode.schedule initial (start + offset) = some (cyclicAt path positive offset) := by
  have edges := (checkLoop_spec next mode start path positive).mp checked
  intro offset
  induction offset with
  | zero => intro _; simpa only [Nat.add_zero] using entry
  | succ offset ih =>
    intro inside
    rw [Nat.add_succ, run_succ, ih (by omega)]
    have index : offset < path.length := by omega
    rw [cyclicAt_lt path positive ⟨offset, index⟩]
    exact (edges ⟨offset, index⟩).1

theorem checkLoop_sound (next : S → List S) (mode : Mode) (initial : S) (start : Nat)
    (path : List S) (positive : 0 < path.length) (checked : checkLoop next mode start path = true)
    (entry : run next mode.schedule initial start = some (cyclicAt path positive 0)) :
    Nonterminating next mode.schedule initial ∧ PeriodicFrom next mode.schedule initial start path.length := by
  have segment := checkLoop_prefix next mode initial start path positive checked entry
  have edges := (checkLoop_spec next mode start path positive).mp checked
  apply return_periodic_of_shift_compatible next mode.schedule initial start path.length positive
    (cyclicAt path positive 0) entry
    (by simpa only [cyclicAt_length] using segment path.length le_rfl)
  intro offset inside state present
  have value := Option.some.inj ((segment offset inside.le).symm.trans present)
  have equal : path.get ⟨offset, inside⟩ = state :=
    (cyclicAt_lt path positive ⟨offset, inside⟩).symm.trans value
  rw [← equal]
  exact localPeriodCheck_sound mode start path.length _ (edges ⟨offset, inside⟩).2

theorem checkLoop_sound_of_entry (next : S → List S) (mode : Mode) (initial : S) (start : Nat)
    (path : List S) (checked : checkLoop next mode start path = true)
    (entry : run next mode.schedule initial start = path.head?) :
    Nonterminating next mode.schedule initial ∧ PeriodicFrom next mode.schedule initial start path.length := by
  have positive := checkLoop_nonempty next mode start path checked
  have first : some (cyclicAt path positive 0) = path.head? := by
    cases path with
    | nil => cases positive
    | cons state rest => simp [cyclicAt]
  exact checkLoop_sound next mode initial start path positive checked (entry.trans first.symm)

end Mettapedia.Machines.ScheduledRun
