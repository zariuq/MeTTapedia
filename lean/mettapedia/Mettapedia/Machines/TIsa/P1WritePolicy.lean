import Mettapedia.Machines.TIsa.P1WordExecution

/-!
# Framing p1 execution by its writes

A policy bounds register writes and stores through capabilities. The
invariant only needs to be closed under those writes and fuel accounting.
The same rule applies to branches, bounded loops and early returns.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.P1WritePolicy

open P1Source P1WordExecution

structure Policy where
  register : Reg → Bool
  store : Region → Reg → BitVec 32 → Bool

def Policy.instruction (policy : Policy) (code : Instr) : Bool :=
  match code with
  | .store .word64 region pointer displacement _ => policy.store region pointer displacement
  | other => other.destination?.all policy.register

def Policy.accepts (policy : Policy) : Stmt → Bool
  | .instruction code => policy.instruction code
  | .seq first second | .branch _ first second => policy.accepts first && policy.accepts second
  | .counted index _ _ body | .early index _ _ _ body => policy.register index && policy.accepts body
  | _ => true

structure Closed (policy : Policy) (holds : State → Prop) : Prop where
  write : ∀ state register value, holds state → policy.register register = true →
    holds (state.write register value)
  store : ∀ state region pointer displacement location value, holds state →
    policy.store region pointer displacement = true →
    Memory.access? (state.regions region).base (state.regions region).length
      (state.registers pointer) displacement.toInt 8 = some location →
    holds (state.store location value)
  charge : ∀ state spent, holds state → holds {state with spent}

variable {policy : Policy} {holds : State → Prop}

private theorem Closed.scalar (closed : Closed policy holds) {state after : State} (code : Instr)
    (ready : holds state) (allowed : code.destination?.all policy.register = true)
    (ran : scalarInstruction state code = .ok after) : holds after := by
  unfold scalarInstruction at ran
  split at ran
  · cases ran
  · rename_i register destination
    split at ran
    · cases ran
      exact closed.write _ _ _ ready (by simpa only [destination, Option.all_some] using allowed)
    · cases ran

private theorem Closed.step (closed : Closed policy holds) {state after : State} (code : Instr)
    (ready : holds state) (allowed : policy.instruction code = true)
    (ran : instruction state code = .ok after) : holds after := by
  cases code
  case immediate ty dst value => exact closed.scalar (.immediate ty dst value) ready allowed ran
  case move ty dst source => exact closed.scalar (.move ty dst source) ready allowed ran
  case binary op ty dst left right => exact closed.scalar (.binary op ty dst left right) ready allowed ran
  case shift op ty dst source amount => exact closed.scalar (.shift op ty dst source amount) ready allowed ran
  case extract ty dst source low width => exact closed.scalar (.extract ty dst source low width) ready allowed ran
  case compare op ty dst left right => exact closed.scalar (.compare op ty dst left right) ready allowed ran
  case select ty dst cond yes no => exact closed.scalar (.select ty dst cond yes no) ready allowed ran
  case address region dst base index scale displacement =>
    simp only [instruction] at ran
    split at ran
    · cases ran
    · split at ran
      · cases ran
        exact closed.write _ _ _ ready allowed
      · cases ran
  case load ty width region dst base displacement =>
    cases width <;> simp only [instruction] at ran
    · cases ran
    · cases ran
    · split at ran
      · cases ran
      · split at ran
        · split at ran
          · cases ran
            exact closed.write _ _ _ ready allowed
          · cases ran
        · cases ran
  case loadFrame ty dst slot =>
    simp only [instruction] at ran
    split at ran
    · cases ran
      exact closed.write _ _ _ ready allowed
    · cases ran
  case store width region base displacement source =>
    cases width <;> simp only [instruction] at ran
    · cases ran
    · cases ran
    · split at ran
      · cases ran
      · split at ran
        · rename_i location located
          cases ran
          obtain ⟨target, bounded, found⟩ := Option.bind_eq_some_iff.mp located
          split at found
          · cases found
            exact closed.store _ _ _ _ _ _ ready allowed bounded
          · cases found
        · cases ran

private theorem continue_preserves {guard : Option Reg} {state : State} {next : State → Flow}
    (ready : holds state) (continues : holds (next state).after) :
    holds (continueLoop state guard next).after := by
  cases guard with
  | none => exact continues
  | some register =>
    simp only [continueLoop]
    split
    · exact continues
    · split <;> exact ready

private theorem Closed.run_loop (closed : Closed policy holds) (body : State → Flow)
    (runs : ∀ state, holds state → holds (body state).after) {index : Reg}
    (allowed : policy.register index = true) (guard : Option Reg) (count : Nat)
    {state : State} (ready : holds state) : holds (loop body index guard count state).after := by
  induction count generalizing state with
  | zero => exact ready
  | succ count ih =>
    apply continue_preserves ready
    have next := runs state ready
    cases ran : body state with
    | returned =>
      rw [ran] at next
      exact next
    | continuing reached =>
      rw [ran] at next
      let step := reached.write index (reached.registers index + 1)
      have stepped : holds step := closed.write reached index _ next allowed
      have rest : holds (loop body index guard count step).after := ih (state := step) stepped
      exact continue_preserves (guard := guard) (state := reached)
        (next := fun state => loop body index guard count (state.write index (state.registers index + 1)))
        next rest

theorem Closed.execute (closed : Closed policy holds) {code : Stmt}
    (checked : policy.accepts code = true) {state : State} (ready : holds state) :
    holds (P1WordExecution.execute state code).after := by
  induction code generalizing state with
  | skip | ret => exact ready
  | instruction code =>
    simp only [P1WordExecution.execute]
    split
    · rename_i ran
      exact closed.step code ready checked ran
    · exact ready
  | seq first second firstIH secondIH =>
    obtain ⟨one, two⟩ := Bool.and_eq_true_iff.mp checked
    have started := firstIH one ready
    simp only [P1WordExecution.execute]
    cases ran : P1WordExecution.execute state first with
    | continuing reached =>
      rw [ran] at started
      exact secondIH two started
    | returned =>
      rw [ran] at started
      exact started
  | branch condition yes no yesIH noIH =>
    obtain ⟨one, two⟩ := Bool.and_eq_true_iff.mp checked
    simp only [P1WordExecution.execute]
    split
    · exact yesIH one ready
    · split
      · exact noIH two ready
      · exact ready
  | counted index bound cap body ih | early index bound _ cap body ih =>
    obtain ⟨register, body⟩ := Bool.and_eq_true_iff.mp checked
    simp only [P1WordExecution.execute]
    split
    · exact ready
    · exact closed.run_loop _ (fun _ => ih body) register _ _ (closed.write _ _ _ ready register)
  | fund units =>
    simp only [P1WordExecution.execute, P1WordExecution.fund]
    split
    · exact ready
    · exact closed.charge _ _ ready

end Mettapedia.Machines.TIsa.P1WritePolicy
