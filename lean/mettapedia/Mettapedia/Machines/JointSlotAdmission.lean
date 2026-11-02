import Mathlib.Data.List.Basic

/-!
# Joint admission to two finite slot tables

A frame and its lifecycle entry are published together. Computing candidate
tables is pure; failure leaves the original state visible. The eager control
exhibits publication after only the first allocation. Native effects and the
C implementation remain separate interpretation obligations.
-/

namespace Mettapedia.Machines.JointSlotAdmission

variable {A B : Type*}

def insertFirst (value : A) : List (Option A) -> Option (List (Option A))
  | [] => none
  | none :: rest => some (some value :: rest)
  | some prior :: rest => (insertFirst value rest).map (fun tail => some prior :: tail)

def vacancies : List (Option A) -> Nat
  | [] => 0
  | none :: rest => vacancies rest + 1
  | some _ :: rest => vacancies rest

theorem inserted_length (value : A) (before after : List (Option A))
    (inserted : insertFirst value before = some after) :
    after.length = before.length := by
  induction before generalizing after with
  | nil => simp [insertFirst] at inserted
  | cons entry rest ih =>
    cases entry with
    | none =>
      simp only [insertFirst, Option.some.injEq] at inserted
      subst after
      rfl
    | some prior =>
      cases step : insertFirst value rest with
      | none => simp [insertFirst, step] at inserted
      | some tail =>
        have same : some prior :: tail = after := by
          simpa [insertFirst, step] using inserted
        subst after
        simpa using congrArg Nat.succ (ih tail step)

theorem inserted_consumes_one (value : A) (before after : List (Option A))
    (inserted : insertFirst value before = some after) :
    vacancies after + 1 = vacancies before := by
  induction before generalizing after with
  | nil => simp [insertFirst] at inserted
  | cons entry rest ih =>
    cases entry with
    | none =>
      simp only [insertFirst, Option.some.injEq] at inserted
      subst after
      rfl
    | some prior =>
      cases step : insertFirst value rest with
      | none => simp [insertFirst, step] at inserted
      | some tail =>
        have same : some prior :: tail = after := by
          simpa [insertFirst, step] using inserted
        subst after
        exact ih tail step

structure State (A B : Type*) where
  frames : List (Option A)
  lifecycles : List (Option B)
  deriving DecidableEq, Repr

def publish (frame : A) (lifecycle : B) (state : State A B) : State A B × Bool :=
  match insertFirst frame state.frames, insertFirst lifecycle state.lifecycles with
  | some frames, some lifecycles => ({ frames, lifecycles }, true)
  | _, _ => (state, false)

theorem rejected_preserves (frame : A) (lifecycle : B) (state : State A B)
    (rejected : (publish frame lifecycle state).2 = false) :
    (publish frame lifecycle state).1 = state := by
  cases frames : insertFirst frame state.frames <;>
    cases lifecycles : insertFirst lifecycle state.lifecycles <;>
    simp_all [publish]

theorem missing_lifecycle_rejects (frame : A) (lifecycle : B) (state : State A B)
    (missing : insertFirst lifecycle state.lifecycles = none) :
    publish frame lifecycle state = (state, false) := by
  cases frames : insertFirst frame state.frames <;> simp [publish, frames, missing]

theorem accepted_preserves_lengths (frame : A) (lifecycle : B) (state : State A B)
    (accepted : (publish frame lifecycle state).2 = true) :
    And ((publish frame lifecycle state).1.frames.length = state.frames.length)
      ((publish frame lifecycle state).1.lifecycles.length = state.lifecycles.length) := by
  cases frames : insertFirst frame state.frames with
  | none => simp [publish, frames] at accepted
  | some nextFrames =>
    cases lifecycles : insertFirst lifecycle state.lifecycles with
    | none => simp [publish, frames, lifecycles] at accepted
    | some nextLifecycles =>
      simpa [publish, frames, lifecycles] using
        And.intro (inserted_length frame _ _ frames) (inserted_length lifecycle _ _ lifecycles)

theorem accepted_consumes_both (frame : A) (lifecycle : B) (state : State A B)
    (accepted : (publish frame lifecycle state).2 = true) :
    And (vacancies (publish frame lifecycle state).1.frames + 1 = vacancies state.frames)
      (vacancies (publish frame lifecycle state).1.lifecycles + 1 = vacancies state.lifecycles) := by
  cases frames : insertFirst frame state.frames with
  | none => simp [publish, frames] at accepted
  | some nextFrames =>
    cases lifecycles : insertFirst lifecycle state.lifecycles with
    | none => simp [publish, frames, lifecycles] at accepted
    | some nextLifecycles =>
      simpa [publish, frames, lifecycles] using
        And.intro (inserted_consumes_one frame _ _ frames)
          (inserted_consumes_one lifecycle _ _ lifecycles)

def eagerPublish (frame : A) (lifecycle : B) (state : State A B) : State A B × Bool :=
  match insertFirst frame state.frames with
  | none => (state, false)
  | some frames =>
    ({ frames, lifecycles := (insertFirst lifecycle state.lifecycles).getD state.lifecycles }, true)

example : publish 7 11
    ({ frames := [some 1, none, some 3], lifecycles := [some 4, none] } : State Nat Nat) =
    ({ frames := [some 1, some 7, some 3], lifecycles := [some 4, some 11] }, true) := by
  decide +kernel

example : publish 7 11
    ({ frames := [none], lifecycles := List.replicate 43 (some 11) } : State Nat Nat) =
    ({ frames := [none], lifecycles := List.replicate 43 (some 11) }, false) := by
  decide +kernel

example : eagerPublish 7 11
    ({ frames := [none], lifecycles := List.replicate 43 (some 11) } : State Nat Nat) =
    ({ frames := [some 7], lifecycles := List.replicate 43 (some 11) }, true) := by
  decide +kernel

end Mettapedia.Machines.JointSlotAdmission
