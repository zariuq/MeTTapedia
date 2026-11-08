import Mettapedia.Machines.ReadOnlyQuery

/-!
# Admission of adaptive queries from completed observations

An optional read store distinguishes unavailable observations from completed
negative replies. The transformed query stops at its first unavailable read.
Successful admission has exactly the independently executed source trace;
decline retains its completed prefix and the first missing question. No
source callback, fallback, or effect is hidden in the transformation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ReadOnlyQueryDemand

open Mettapedia.Machines.ReadOnlyQuery

variable {Key Reply Answer : Type}

/-- Transform a pure adaptive query into a check of completed observations.
There is no callback that could produce a missing observation. -/
def demand : Program Key Reply Answer → Program Key (Option Reply) (Option Answer)
  | .pure answer => .pure (some answer)
  | .read key next => .read key fun
      | none => .pure none
      | some reply => demand (next reply)

def liftedReads (reads : Mettapedia.Machines.ReadOnlyQuery.Reads Key Reply) :
    Mettapedia.Machines.ReadOnlyQuery.Reads Key (Option Reply) :=
  reads.map fun read => (read.1, some read.2)

def lifted (observation : Observation Key Reply Answer) :
    Observation Key (Option Reply) (Option Answer) :=
  ⟨some observation.answer, liftedReads observation.reads⟩

/-- Truthfulness concerns only present observations; no total coverage is
required and an unavailable view is not a completed negative answer. -/
def Truthful (source : Key → Reply) (available : Key → Option Reply) : Prop :=
  ∀ key reply, available key = some reply → reply = source key

def Covered (available : Key → Option Reply)
    (reads : Mettapedia.Machines.ReadOnlyQuery.Reads Key Reply) : Prop :=
  ∀ read ∈ reads, available read.1 = some read.2

theorem demand_eq_of_covered (source : Key → Reply) (available : Key → Option Reply)
    (program : Program Key Reply Answer) (covered : Covered available (run source program).reads) :
    run available (demand program) = lifted (run source program) := by
  induction program with
  | pure answer => rfl
  | read key next ih =>
      have here := covered (key, source key) (by simp [run])
      have tail : Covered available (run source (next (source key))).reads := by
        intro read member
        exact covered read (by simp [run, member])
      simp [demand, run, here, ih (source key) tail, lifted, liftedReads]

/-- Every successful admission has exactly the complete source read trace,
with each read explicitly marked available. No unused view is required. -/
theorem demand_success_exact (source : Key → Reply) (available : Key → Option Reply)
    (truthful : Truthful source available) (program : Program Key Reply Answer)
    (success : (run available (demand program)).answer ≠ none) :
    run available (demand program) = lifted (run source program) := by
  induction program with
  | pure answer => rfl
  | read key next ih =>
      cases found : available key with
      | none => simp [demand, run, found] at success
      | some reply =>
          have eq := truthful key reply found
          subst reply
          have tail : (run available (demand (next (source key)))).answer ≠ none := by
            simpa [demand, run, found] using success
          simp [demand, run, found, ih (source key) tail, lifted, liftedReads]

theorem demand_success_iff_covered (source : Key → Reply) (available : Key → Option Reply)
    (truthful : Truthful source available) (program : Program Key Reply Answer) :
    (run available (demand program)).answer ≠ none ↔
      Covered available (run source program).reads := by
  constructor
  · intro success read member
    have agree := run_agrees available (demand program)
    rw [demand_success_exact source available truthful program success] at agree
    exact agree (read.1, some read.2) (List.mem_map.mpr ⟨read, member, rfl⟩)
  · intro covered
    rw [demand_eq_of_covered source available program covered]
    simp [lifted]

/-- On decline the only extra read after the completed prefix is the first
missing one. No suffix is queried and no canonical/body replay occurs. -/
theorem demand_decline_prefix (source : Key → Reply) (available : Key → Option Reply)
    (truthful : Truthful source available) (program : Program Key Reply Answer)
    (declined : (run available (demand program)).answer = none) :
    ∃ before key reply suffix,
      (run source program).reads = before ++ (key, reply) :: suffix ∧
      (run available (demand program)).reads = liftedReads before ++ [(key, none)] ∧
      Covered available before ∧ available key = none := by
  induction program with
  | pure answer => simp [demand, run] at declined
  | read key next ih =>
      cases found : available key with
      | none =>
          refine ⟨[], key, source key, (run source (next (source key))).reads, ?_, ?_, ?_, found⟩
          · rfl
          · simp [demand, run, found, liftedReads]
          · simp [Covered]
      | some reply =>
          have eq := truthful key reply found
          subst reply
          have tail : (run available (demand (next (source key)))).answer = none := by
            simpa [demand, run, found] using declined
          obtain ⟨before, missing, reply, suffix, full, checkedReads, covered, absent⟩ := ih (source key) tail
          refine ⟨(key, source key) :: before, missing, reply, suffix, ?_, ?_, ?_, absent⟩
          · simp only [run, full, List.cons_append]
          · simp [demand, run, found, checkedReads, liftedReads]
          · intro read member
            rcases List.mem_cons.mp member with rfl | member
            · exact found
            · exact covered read member

end Mettapedia.Machines.ReadOnlyQueryDemand

