import Mettapedia.Machines.ScheduledRun.Detection

/-!
# Wrapping clocks and faithful finite prefixes

Wrapping a turn counter changes the future controller, not merely its storage.
The wrapped and natural rotating runs agree up to the first wrap. Therefore
a report on such a faithful prefix certifies the unbounded declared schedule;
it need not certify the future of a different, wrapping schedule. A small-word
counterexample makes the distinction explicit. This is not a claim that a C
budget permits wrap or a proof of the C budget/counter invariant.
`claimsAt` still timestamps its observations with logical turns; it is not a
full word-sized visit-table model. Native phase correspondence also requires
that the observed counter has not wrapped at the probe itself.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ScheduledRun

universe u
variable {S : Type u}

def wrapping (modulus : Nat) : Schedule :=
  ⟨fun turn count => (turn % modulus) % count, fun _ _ positive => Nat.mod_lt _ positive⟩

theorem wrapping_step (next : S → List S) (modulus turn : Nat) (observation : Option S) :
    step next (wrapping modulus) turn observation = step next rotating (turn % modulus) observation := rfl

theorem wrapping_prefix_agrees (next : S → List S) (initial : S) (modulus : Nat) :
    ∀ turn, turn ≤ modulus → run next (wrapping modulus) initial turn = run next rotating initial turn := by
  intro turn
  induction turn with
  | zero => intro _; rfl
  | succ turn ih =>
    intro bound
    rw [run_succ, run_succ, ih (by omega), wrapping_step, Nat.mod_eq_of_lt (by omega : turn < modulus)]

variable [DecidableEq S]

theorem recordPrefix_congr (next : S → List S) (mode : Mode)
    (first second : Nat → Option S) : ∀ turn,
      (∀ before, before < turn → first before = second before) →
      recordPrefix next mode first turn = recordPrefix next mode second turn := by
  intro turn
  induction turn with
  | zero => intro _; rfl
  | succ turn ih =>
    intro equal
    rw [recordPrefix, recordPrefix, ih (fun before inside => equal before (by omega)), equal turn (by omega)]

theorem claimsAt_congr (next : S → List S) (mode : Mode)
    (first second : Nat → Option S) (turn : Nat)
    (equal : ∀ before, before ≤ turn → first before = second before) :
    claimsAt next mode first turn = claimsAt next mode second turn := by
  unfold claimsAt
  rw [equal turn le_rfl, recordPrefix_congr next mode first second turn (fun before inside => equal before inside.le)]

theorem faithful_wrapped_prefix_claim (next : S → List S) (initial : S) (modulus turn : Nat)
    (bound : turn ≤ modulus)
    (claim : claimsAt next .rotating (run next (wrapping modulus) initial) turn = true) :
    Nonterminating next rotating initial := by
  have same := claimsAt_congr next .rotating (run next (wrapping modulus) initial) (run next rotating initial)
    turn (fun before earlier => wrapping_prefix_agrees next initial modulus before (earlier.trans bound))
  exact claimsAt_sound next .rotating initial turn (same ▸ claim)

namespace ClockControls

inductive State where
  | wait
  | walk
  | stop
  deriving DecidableEq, Repr

open State

def next : State → List State
  | wait => [walk, stop, wait]
  | walk => [wait]
  | stop => []

theorem natural_rotation_is_infinite :
    Nonterminating next rotating wait ∧ PeriodicFrom next rotating wait 0 3 := by
  apply return_mod_lcm_periodic next wait (first := 0) (last := 3) (by decide) wait (by decide) (by decide)
  decide

theorem wrapped_trace : (List.range 8).map (run next (wrapping 4) wait) =
    [some wait, some walk, some wait, some wait, some walk, some wait, some stop, none] := by decide

theorem wrapped_future_terminates : EndsAt next (wrapping 4) wait 6 ∧
    ¬ Nonterminating next (wrapping 4) wait := by
  have ended : EndsAt next (wrapping 4) wait 6 := ⟨stop, by decide, rfl⟩
  exact ⟨ended, ended_not_nonterminating next (wrapping 4) wait ended⟩

theorem an_unbounded_licence_does_not_assert_wrapped_liveness :
    claimsAt next .rotating (run next (wrapping 4) wait) 4 = true ∧
      Nonterminating next rotating wait ∧ ¬ Nonterminating next (wrapping 4) wait :=
  ⟨by decide, natural_rotation_is_infinite.1, wrapped_future_terminates.2⟩

theorem a_faithful_pre_wrap_claim_still_has_an_ideal_target :
    claimsAt next .rotating (run next (wrapping 16) wait) 4 = true ∧ 4 < 16 ∧
      EndsAt next (wrapping 16) wait 18 ∧ Nonterminating next rotating wait :=
  ⟨by decide, by decide, ⟨stop, by decide, rfl⟩, natural_rotation_is_infinite.1⟩

end ClockControls

end Mettapedia.Machines.ScheduledRun
