import Mettapedia.Machines.ScheduledRun.Detection
import Mettapedia.Machines.ScheduledRun.Controls

/-!
# Executable controls for resetting the visit record

The no-reset mutant retains residues computed under different moduli. Its
false report on the period-change fixture is checked by computation. Infinite
growth supplies the negative control for finite-state completeness.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ScheduledRun.Controls

open State

theorem canonical_monitor_claims : claimsAt waitNext .canonical (run waitNext canonical wait) 1 = true := by decide

theorem rotating_monitor_claims : claimsAt cycleNext .rotating (run cycleNext rotating wait) 3 = true := by decide

theorem rotating_wakes_never_claimed (turn : Nat) :
    claimsAt waitNext .rotating (run waitNext rotating wait) turn = false :=
  ended_never_reports waitNext .rotating wait (ending := 2) ⟨wake, by decide, rfl⟩ turn

theorem stale_phase_never_claimed (turn : Nat) :
    claimsAt staleNext .rotating (run staleNext rotating 1) turn = false :=
  ended_never_reports staleNext .rotating 1 (ending := 7) ⟨0, by decide, rfl⟩ turn

def noResetStep {S : Type*} [DecidableEq S] (next : S → List S) (turn : Nat)
    (observation : Option S) (record : VisitRecord S) : VisitRecord S :=
  match observation with
  | none => record
  | some state => ⟨updatePeriod .rotating record.period (next state).length,
      insert (state, turn % record.period) record.seen⟩

def noResetPrefix {S : Type*} [DecidableEq S] (next : S → List S)
    (trace : Nat → Option S) : Nat → VisitRecord S
  | 0 => initialRecord
  | turn + 1 => noResetStep next turn (trace turn) (noResetPrefix next trace turn)

def noResetClaims {S : Type*} [DecidableEq S] (next : S → List S)
    (trace : Nat → Option S) (turn : Nat) : Bool :=
  match trace turn with
  | none => false
  | some state => decide ((state, turn % (noResetPrefix next trace turn).period) ∈
      (noResetPrefix next trace turn).seen)

theorem stale_residue_mutant_claims_finite_run :
    noResetClaims staleNext (run staleNext rotating 1) 4 = true ∧ EndsAt staleNext rotating 1 7 := by
  exact ⟨by decide, 0, by decide, rfl⟩

def delayedExit : Schedule :=
  ⟨fun turn count => (if turn = 4 then 1 else 0) % count,
    fun _ _ positive => Nat.mod_lt _ positive⟩

theorem bounded_picks_alone_do_not_license_the_lcm_clock :
    claimsAt waitNext .rotating (run waitNext delayedExit wait) 3 = true ∧
      EndsAt waitNext delayedExit wait 5 ∧ ¬ Nonterminating waitNext delayedExit wait := by
  have ended : EndsAt waitNext delayedExit wait 5 := ⟨wake, by decide, rfl⟩
  exact ⟨by decide, ended, ended_not_nonterminating waitNext delayedExit wait ended⟩

def growingNext (state : Nat) : List Nat := [state + 1]

theorem growing_run (turn : Nat) : run growingNext rotating 0 turn = some turn := by
  induction turn with
  | zero => rfl
  | succ turn ih => rw [run_succ, ih]; simp [step, growingNext, rotating]

theorem infinite_growth_is_not_detected : Nonterminating growingNext rotating 0 ∧
    ∀ turn, claimsAt growingNext .rotating (run growingNext rotating 0) turn = false := by
  refine ⟨fun turn => by rw [growing_run]; exact Option.some_ne_none _, ?_⟩
  intro turn
  cases result : claimsAt growingNext .rotating (run growingNext rotating 0) turn with
  | false => rfl
  | true =>
    obtain ⟨state, current, member⟩ := (claimsAt_iff growingNext .rotating _ turn).mp result
    obtain ⟨earlier, order, previous, _⟩ := recordPrefix_witness growingNext .rotating _ turn _ member
    rw [growing_run] at current previous
    have first := Option.some.inj current
    have second := Option.some.inj previous
    omega

end Mettapedia.Machines.ScheduledRun.Controls
