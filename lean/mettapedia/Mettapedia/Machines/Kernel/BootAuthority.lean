import Mettapedia.Machines.Kernel.SingleAddressSpace

/-!
# Constructing and sealing an authority genesis

Boot installation is a partial operation: it requires an unsealed table,
a nonzero bounded vacant slot, and a communication capability. Sealing is
irreversible and idempotent. Runtime page delegation belongs to the existing
kernel transition system, not to boot installation.

The model separates a stable communication graph from later frame lending.
It does not model executable loading or hardware protection-key enforcement.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.BootAuthority

variable {D : Type} [DecidableEq D]

structure Table (D : Type) where
  caps : D → Nat → Option (Cap D)
  sealed : Bool

def empty : Table D := ⟨fun _ _ => none, false⟩

def sealTable (s : Table D) : Table D := { s with sealed := true }

def install (bound : Nat) (s : Table D) (holder : D) (slot : Nat)
    (cap : Cap D) : Option (Table D) :=
  if s.sealed then none
  else if slot = 0 ∨ bound ≤ slot then none
  else match cap.obj with
    | .frame _ => none
    | .ring _ => if s.caps holder slot = none then
        some { s with caps := upd2 s.caps holder slot (some cap) }
      else none

inductive Action (D : Type) where
  | install (holder : D) (slot : Nat) (cap : Cap D)
  | finishBoot

def step (bound : Nat) (s : Table D) : Action D → Table D
  | .install holder slot cap => (install bound s holder slot cap).getD s
  | .finishBoot => sealTable s

def run (bound : Nat) (s : Table D) (actions : List (Action D)) : Table D :=
  actions.foldl (step bound) s

omit [DecidableEq D] in
@[simp] theorem seal_idempotent (s : Table D) : sealTable (sealTable s) = sealTable s := rfl

theorem install_after_seal (bound : Nat) (s : Table D) (holder : D) (slot : Nat)
    (cap : Cap D) : install bound (sealTable s) holder slot cap = none := by
  simp [install, sealTable]

theorem install_occupied (bound : Nat) (s : Table D) (holder : D) (slot : Nat)
    (cap existing : Cap D) (occupied : s.caps holder slot = some existing) :
    install bound s holder slot cap = none := by
  rcases cap with ⟨obj, writing⟩
  cases obj <;> simp [install, occupied]

theorem step_sealed (bound : Nat) (s : Table D) (action : Action D)
    (locked : s.sealed = true) : step bound s action = s := by
  cases action with
  | install holder slot cap => simp [step, install, locked]
  | finishBoot => cases s; simp_all [step, sealTable]

theorem run_sealed (bound : Nat) (s : Table D) (actions : List (Action D))
    (locked : s.sealed = true) : run bound s actions = s := by
  induction actions with
  | nil => rfl
  | cons action rest ih =>
      simpa [run, List.foldl_cons, step_sealed bound s action locked] using ih

def NoFrames (s : Table D) : Prop :=
  ∀ holder slot frame writing, s.caps holder slot ≠ some ⟨.frame frame, writing⟩

omit [DecidableEq D] in
theorem empty_noFrames : NoFrames (empty : Table D) := by simp [NoFrames, empty]

theorem install_noFrames (bound : Nat) {s result : Table D} (holder : D) (slot : Nat)
    (cap : Cap D) (valid : NoFrames s)
    (accepted : install bound s holder slot cap = some result) : NoFrames result := by
  rcases cap with ⟨obj, writing⟩
  cases obj with
  | frame f => simp [install] at accepted
  | ring target =>
      simp only [install] at accepted
      split at accepted <;> try contradiction
      split at accepted <;> try contradiction
      split at accepted <;> try contradiction
      cases accepted
      intro other position frame writable
      by_cases sameHolder : other = holder
      · subst other
        by_cases sameSlot : position = slot
        · subst position; simp [upd2, upd]
        · simpa [upd2, upd, sameSlot] using valid holder position frame writable
      · simpa [upd2, upd, sameHolder] using valid other position frame writable

theorem step_noFrames (bound : Nat) (s : Table D) (action : Action D)
    (valid : NoFrames s) : NoFrames (step bound s action) := by
  cases action with
  | finishBoot => exact valid
  | install holder slot cap =>
      cases found : install bound s holder slot cap with
      | none => simpa [step, found] using valid
      | some result =>
          simpa [step, found] using install_noFrames bound holder slot cap valid found

theorem run_noFrames (bound : Nat) (s : Table D) (actions : List (Action D))
    (valid : NoFrames s) : NoFrames (run bound s actions) := by
  induction actions generalizing s with
  | nil => exact valid
  | cons action rest ih =>
      exact ih (step bound s action) (step_noFrames bound s action valid)

def launch (config : Config D) (s : Table D) : Option (State D) :=
  if s.sealed then some (genesis config s.caps) else none

omit [DecidableEq D] in
theorem launch_unsealed (config : Config D) (s : Table D)
    (openTable : s.sealed = false) : launch config s = none := by
  simp [launch, openTable]

theorem constructed_genesis_good (config : Config D) (bound : Nat)
    (actions : List (Action D)) :
    Good config (genesis config (sealTable (run bound empty actions)).caps) := by
  apply genesis_good
  exact run_noFrames bound empty actions empty_noFrames

def sample : Table (Fin 3) :=
  run 8 empty [.install 0 2 ⟨.ring 1, true⟩, .finishBoot,
    .install 0 2 ⟨.ring 2, true⟩, .install 2 3 ⟨.ring 0, true⟩]

theorem sample_retains_original : sample.caps 0 2 = some ⟨.ring 1, true⟩ := by decide
theorem sample_refuses_later_edge : sample.caps 2 3 = none := by decide
theorem sample_sealed : sample.sealed = true := by decide

#print axioms run_sealed
#print axioms constructed_genesis_good

end Mettapedia.Machines.Kernel.BootAuthority
