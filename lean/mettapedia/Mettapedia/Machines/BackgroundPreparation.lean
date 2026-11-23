import Mettapedia.Machines.ReadCertifiedQueryReuse
import Mettapedia.Machines.TierUpReplayCost

/-!
# Availability and validity are different

Workers return immutable prepared observations. A caller chooses only
finished, still-valid work, with ordinary evaluation as a fallback.
Scheduling completion does not give a worker authority to publish a
live effect. The cost model separately accounts for a spare core and
for compiler work consumed by a request that finishes too soon.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BackgroundPreparation

section Adoption

open ReadCertifiedQueryReuse.Supported

variable {State Authority Query Key Value Answer : Type*}
  [DecidableEq Authority] [DecidableEq Query] [DecidableEq Value]

structure Finished (family : Family State Authority Query Key Value Answer) where
  availableAt : Nat
  proposal : Captured family

def takeReady (family : Family State Authority Query Key Value Answer)
    (current : State) (query : Query) (now : Nat) : List (Finished family) → Option Answer
  | [] => none
  | candidate :: rest =>
      if candidate.availableAt ≤ now ∧ admissible family current query candidate.proposal.val = true then
        some candidate.proposal.val.value.answer
      else takeReady family current query now rest

theorem takeReady_witness (family : Family State Authority Query Key Value Answer)
    (current : State) (query : Query) (now : Nat) (candidates : List (Finished family))
    (answer : Answer) (chosen : takeReady family current query now candidates = some answer) :
    ∃ candidate ∈ candidates, candidate.availableAt ≤ now ∧
      admissible family current query candidate.proposal.val = true ∧
      candidate.proposal.val.value.answer = answer := by
  induction candidates with
  | nil => simp [takeReady] at chosen
  | cons candidate rest ih =>
      by_cases ready : candidate.availableAt ≤ now ∧
          admissible family current query candidate.proposal.val = true
      · exact ⟨candidate, List.mem_cons_self .., ready.1, ready.2, by
          simpa [takeReady, ready] using chosen⟩
      · obtain ⟨other, occurs, time, current, same⟩ := ih (by simpa [takeReady, ready] using chosen)
        exact ⟨other, List.mem_cons_of_mem _ occurs, time, current, same⟩

theorem ready_answer_exact (family : Family State Authority Query Key Value Answer)
    (current : State) (query : Query) (now : Nat) (candidates : List (Finished family))
    (answer : Answer) (chosen : takeReady family current query now candidates = some answer) :
    answer = (family.observe current query).answer := by
  obtain ⟨candidate, _, _, admissibleNow, same⟩ :=
    takeReady_witness family current query now candidates answer chosen
  have exactAtUse := reuseCaptured_exact family current query candidate.proposal
  simpa [reuseCaptured, reuse, admissibleNow, same] using exactAtUse

def atUse (family : Family State Authority Query Key Value Answer)
    (current : State) (query : Query) (now : Nat) (candidates : List (Finished family)) : Answer :=
  match takeReady family current query now candidates with
  | some answer => answer
  | none => (family.observe current query).answer

/-- Arbitrary completion order, including a late result from an old
authority, changes work and readiness but cannot change the readout. -/
theorem completion_order_irrelevant (family : Family State Authority Query Key Value Answer)
    (current : State) (query : Query) (now : Nat) (candidates : List (Finished family)) :
    atUse family current query now candidates = (family.observe current query).answer := by
  unfold atUse
  split
  · exact ready_answer_exact family current query now candidates _ ‹_›
  · rfl

namespace Controls

private def choices : Family Bool Bool Unit Empty Unit Nat :=
  ofDerivation (fun current _ => if current then 7 else 3)

private def oldProposal : Finished choices := ⟨0, capture choices false ()⟩
private def currentProposal : Finished choices := ⟨2, capture choices true ()⟩

/-- Staleness and not-yet-ready are independent ways to skip a proposal. -/
theorem stale_fast_candidate_is_skipped :
    takeReady choices true () 1 [oldProposal, currentProposal] = none ∧
    takeReady choices true () 2 [oldProposal, currentProposal] = some 7 ∧
    atUse choices true () 1 [oldProposal, currentProposal] = 7 := by decide

end Controls

end Adoption

noncomputable section

open TierUpReplayCost (Prices gap gap_pos)

structure Meter where
  latency : ℝ
  cpu : ℝ

/-- The interpreter progresses at unit speed on one core while compilation
uses a spare core for C units. A short call cancels the compile job at exit.
No contention or repeated interpreted prefix is charged in this model. -/
def overlap (p : Prices) (launch handoff work : ℝ) : Meter :=
  let ready := launch + p.compile
  if work ≤ ready then
    ⟨work, work + max 0 (work - launch)⟩
  else
    let tailCost := ready + handoff + p.q * (work - ready)
    ⟨tailCost, tailCost + p.compile⟩

theorem latency_wins_iff (p : Prices) (launch handoff work : ℝ)
    (ready : launch + p.compile < work) :
    (overlap p launch handoff work).latency < work ↔
      handoff < gap p * (work - (launch + p.compile)) := by
  simp only [overlap, if_neg (not_le.mpr ready), gap]
  constructor <;> intro h <;> nlinarith only [h]

theorem cpu_wins_iff (p : Prices) (launch handoff work : ℝ)
    (ready : launch + p.compile < work) :
    (overlap p launch handoff work).cpu < work ↔
      handoff + p.compile < gap p * (work - (launch + p.compile)) := by
  simp only [overlap, if_neg (not_le.mpr ready), gap]
  constructor <;> intro h <;> nlinarith only [h]

/-- A launch with an unknown horizon cannot improve both ledgers on
every call. Even cancelling immediately at return cannot refund work. -/
theorem short_call_costs_cpu (p : Prices) (launch handoff : ℝ) (l : 0 ≤ launch) :
    ∃ work : ℝ, 0 < work ∧ (overlap p launch handoff work).latency = work ∧
      work < (overlap p launch handoff work).cpu := by
  have h : launch + p.compile / 2 ≤ launch + p.compile := by linarith [p.compile_pos]
  refine ⟨launch + p.compile / 2, by linarith [p.compile_pos], ?_, ?_⟩
  · simp [overlap, h]
  · simp only [overlap, if_pos h]
    have benefit : 0 < max 0 (launch + p.compile / 2 - launch) := by
      exact lt_max_of_lt_right (by linarith [p.compile_pos])
    linarith

/-- For every positive compile price there is an intermediate call
length where the switch improves latency but makes CPU worse. -/
theorem latency_and_cpu_strictly_diverge (p : Prices) (launch handoff : ℝ) (h : 0 ≤ handoff) :
    ∃ work : ℝ, launch + p.compile < work ∧
      (overlap p launch handoff work).latency < work ∧ work < (overlap p launch handoff work).cpu := by
  let ready := launch + p.compile
  let tail := (handoff + p.compile / 2) / gap p
  have tpos : 0 < tail := div_pos (by linarith [p.compile_pos]) (gap_pos p)
  have fee : gap p * tail = handoff + p.compile / 2 := by
    dsimp [tail]
    field_simp [(gap_pos p).ne']
  let work := ready + tail
  have arrives : launch + p.compile < work := lt_add_of_pos_right _ tpos
  have remaining : work - (launch + p.compile) = tail := by dsimp [work, ready]; ring
  refine ⟨work, arrives, (latency_wins_iff p launch handoff work arrives).mpr ?_, ?_⟩
  · rw [remaining, fee]
    linarith [p.compile_pos]
  · simp only [overlap, if_neg (not_le.mpr arrives)]
    dsimp [gap] at fee
    dsimp [work, ready] at *
    nlinarith only [fee, p.compile_pos]

namespace Controls

def model : Prices := ⟨50, 3 / 5, by norm_num, by norm_num, by norm_num⟩

theorem saves_latency_not_cpu :
    (overlap model 10 6 160).latency = 126 ∧ (overlap model 10 6 160).cpu = 176 := by
  norm_num [overlap, model]

end Controls
end
end Mettapedia.Machines.BackgroundPreparation
