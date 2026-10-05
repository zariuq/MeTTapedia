import Mettapedia.GSLT.Distinction.ProductiveBlocks
import Mettapedia.GSLT.Dynamics.CacheCoherenceContract

/-!
# Final outcomes are never revised, and exhaustion is not refusal

Three models read fuel-bounded runs: the abstract runs of the cache contract
(`CacheCoherence.RunOutcome`: answered, refused, exhausted), the machines of
`ProductiveBlocks` (`Outcome`: finished, faulted, suspended, stuck, exhausted),
and the equation evaluator behind authored computations
(`DeterministicEquations.Outcome`: value, failure, exhausted).  In each, a final
outcome is never revised by more fuel, and therefore an answerable query is
refused at no fuel while its short runs are exhausted.  This module states that
once and reads the three models into it.

* **The core** (`NeverRevised`, `NeverRevised.eq_of_final`,
  `NeverRevised.ne_of_final`).  A fuel-indexed run never revises an outcome that
  is not exhaustion.  Two final outcomes at any two fuels agree, and a final
  outcome different from one that is reached is reached at no fuel.
* **The three instances** (`RunOutcome` runs with `refused_never_of_answered`,
  `ProductiveBlocks.Machine.outcome_neverRevised`,
  `DeterministicEquations.apply_neverRevised`).  For equation programs this is
  `apply_le`; for machines it is `Machine.run_stable`.
* **Machine outcomes as cache outcomes** (`ProductiveBlocks.Outcome.runOutcome`).
  A machine whose verdicts are optional answers reads its outcome as a cache
  outcome: a verdict answers or refuses, everything else claims nothing.  A
  logical entry is recorded exactly from a finished outcome
  (`logicalEntry_runOutcome_eq_some_iff`), the machine's runs are adequate when
  its verdicts are logical (`Machine.adequate`), and recording an exhausted
  machine run as a refusal is unsound (`Machine.exhaustedAsRefusal_unsound`,
  an instance of `CacheCoherence.exhaustedAsRefusal_unsound`).
* **Controls.**  A run that revises its outcome answers at one fuel and refuses
  at a larger one (`Controls.revising_refuses`); the premise is needed.  A fault
  is final and records no logical entry (`Controls.fault_final_not_cacheable`):
  recording is exact only on fault-free outcomes.

The authored-computation control `ServiceInferenceCache.Controls.exhaustion_is_not_refusal`
excludes refusal through the contract's refusal law, not through fuel: with the
core alone, a refusal at one fuel and an answer at another would only make the
two encoded results equal, and the contract does not ask encodings to be
injective.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.CacheCoherence

universe uO

/-! ## The core -/

/-- A fuel-indexed run **never revises a final outcome**: once its outcome is not
exhaustion, every larger fuel gives the same outcome. -/
def NeverRevised {O : Type uO} (exhausted : O → Prop) (run : ℕ → O) : Prop :=
  ∀ ⦃fuel more : ℕ⦄, fuel ≤ more → ¬ exhausted (run fuel) → run more = run fuel

namespace NeverRevised

variable {O : Type uO} {exhausted : O → Prop} {run : ℕ → O}

/-- **Two final outcomes agree**, at any two fuels. -/
theorem eq_of_final (never : NeverRevised exhausted run) {fuel fuel' : ℕ}
    (final : ¬ exhausted (run fuel)) (final' : ¬ exhausted (run fuel')) : run fuel = run fuel' := by
  rcases Nat.le_total fuel fuel' with le | le
  · exact (never le final).symm
  · exact never le final'

/-- **Exhaustion is not refusal, at the core**: a final outcome different from
one that is reached is reached at no fuel. -/
theorem ne_of_final (never : NeverRevised exhausted run) {fuel : ℕ}
    (final : ¬ exhausted (run fuel)) {other : O} (otherFinal : ¬ exhausted other)
    (different : other ≠ run fuel) (fuel' : ℕ) : run fuel' ≠ other := by
  intro reached
  have final' : ¬ exhausted (run fuel') := fun exhaustedHere => otherFinal (reached ▸ exhaustedHere)
  exact different (reached.symm.trans (never.eq_of_final final final').symm)

end NeverRevised

/-! ## Cache outcomes -/

variable {Answer : Type}

/-- **An answerable run is refused at no fuel**, when it never revises a final
outcome. -/
theorem refused_never_of_answered {run : ℕ → RunOutcome Answer}
    (never : NeverRevised (· = RunOutcome.exhausted) run) {fuel : ℕ} {answer : Answer}
    (answered : run fuel = .answered answer) (fuel' : ℕ) : run fuel' ≠ .refused :=
  never.ne_of_final (other := .refused) (fun impossible => nomatch answered.symm.trans impossible)
    (fun impossible => nomatch impossible) (fun same => nomatch same.trans answered) fuel'

/-- An outcome records no logical entry exactly when it is exhaustion. -/
theorem logicalEntry_eq_none_iff (outcome : RunOutcome Answer) :
    logicalEntry outcome = none ↔ outcome = .exhausted := by
  cases outcome with
  | answered answer => constructor <;> intro impossible <;> cases impossible
  | refused => constructor <;> intro impossible <;> cases impossible
  | exhausted => exact ⟨fun _ => rfl, fun _ => rfl⟩

end Mettapedia.GSLT.Dynamics.CacheCoherence

/-! ## Equation programs -/

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations

open Mettapedia.GSLT.Dynamics.CacheCoherence (NeverRevised)

/-- **The equation evaluator never revises a final outcome** (`apply_le`). -/
theorem apply_neverRevised (P : Program) (H : Host) (head : String) (arguments : List Term) :
    NeverRevised (· = Outcome.exhausted) (fun fuel => apply P H fuel head arguments) :=
  fun _ _ le final => apply_le le final

end Mettapedia.GSLT.LanguageDef.DeterministicEquations

/-! ## Machines -/

namespace Mettapedia.GSLT.Distinction.ProductiveBlocks

open Mettapedia.GSLT.Dynamics.CacheCoherence

namespace Outcome

variable {State Answer Request : Type}

/-- **A machine outcome as a cache outcome**: a verdict answers or refuses; a
fault, a suspension, a stuck state and exhaustion claim nothing. -/
def runOutcome : Outcome State (Option Answer) Request → RunOutcome Answer
  | .finished (some answer) => .answered answer
  | .finished none => .refused
  | .faulted => .exhausted
  | .suspended _ _ => .exhausted
  | .stuck _ => .exhausted
  | .exhausted _ => .exhausted

/-- **A logical entry is recorded exactly from a finished outcome**, and it is the
verdict. -/
theorem logicalEntry_runOutcome_eq_some_iff (outcome : Outcome State (Option Answer) Request)
    (entry : Option Answer) :
    logicalEntry outcome.runOutcome = some entry ↔ outcome = .finished entry := by
  cases outcome with
  | finished verdict =>
      cases verdict with
      | some answer =>
          exact ⟨fun recorded => by cases recorded; rfl, fun finished => by cases finished; rfl⟩
      | none =>
          exact ⟨fun recorded => by cases recorded; rfl, fun finished => by cases finished; rfl⟩
  | faulted => constructor <;> intro impossible <;> cases impossible
  | suspended request saved => constructor <;> intro impossible <;> cases impossible
  | stuck state => constructor <;> intro impossible <;> cases impossible
  | exhausted residual => constructor <;> intro impossible <;> cases impossible

/-- On fault-free outcomes, a logical entry is recorded exactly when the status
is final. -/
theorem isSome_logicalEntry_iff_final (outcome : Outcome State (Option Answer) Request)
    (faultFree : outcome ≠ .faulted) :
    (logicalEntry outcome.runOutcome).isSome ↔ outcome.status.Final := by
  cases outcome with
  | finished verdict => cases verdict <;> exact ⟨fun _ => trivial, fun _ => rfl⟩
  | faulted => exact absurd rfl faultFree
  | suspended request saved => exact ⟨(fun impossible => nomatch impossible), False.elim⟩
  | stuck state => exact ⟨(fun impossible => nomatch impossible), False.elim⟩
  | exhausted residual => exact ⟨(fun impossible => nomatch impossible), False.elim⟩

end Outcome

namespace Machine

variable {State Event Verdict Request : Type} (machine : Machine State Event Verdict Request)

/-- **A machine never revises a final outcome** (`run_stable`). -/
theorem outcome_neverRevised (state : State) :
    NeverRevised (fun outcome : Outcome State Verdict Request => ∃ residual, outcome = .exhausted residual)
      (fun fuel => (machine.run fuel state).2) := by
  intro fuel more le final
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
  exact congrArg Prod.snd
    (machine.run_stable fuel extra state fun residual exhausted => final ⟨residual, exhausted⟩)

/-- A machine that has finished with a verdict finishes with no other verdict at
any fuel. -/
theorem finished_unique (state : State) {fuel : ℕ} {verdict : Verdict}
    (finished : (machine.run fuel state).2 = .finished verdict) {other : Verdict}
    (different : other ≠ verdict) (fuel' : ℕ) :
    (machine.run fuel' state).2 ≠ .finished other :=
  (machine.outcome_neverRevised state).ne_of_final
    (fun ⟨_, impossible⟩ => nomatch finished.symm.trans impossible)
    (fun ⟨_, impossible⟩ => nomatch impossible)
    (fun same => different (Outcome.finished.inj (same.trans finished))) fuel'

variable {Query Answer : Type} (start : Query → State)

/-- The cache outcome of a machine run from the start state of a query. -/
def cacheRun (machine : Machine State Event (Option Answer) Request) (fuel : ℕ) (query : Query) :
    RunOutcome Answer :=
  (machine.run fuel (start query)).2.runOutcome

/-- **A machine whose verdicts are logical runs adequately.** -/
theorem adequate (machine : Machine State Event (Option Answer) Request)
    {logical : Query → Option Answer}
    (sound : ∀ query fuel verdict, (machine.run fuel (start query)).2 = .finished verdict →
      verdict = logical query) :
    Adequate logical (fun query fuel => cacheRun start machine fuel query) := by
  intro query fuel
  constructor
  · intro answer answered
    have recorded : logicalEntry (cacheRun start machine fuel query) = some (some answer) :=
      congrArg logicalEntry answered
    exact (sound query fuel _ ((Outcome.logicalEntry_runOutcome_eq_some_iff
      (machine.run fuel (start query)).2 _).mp recorded)).symm
  · intro refused
    have recorded : logicalEntry (cacheRun start machine fuel query) = some none :=
      congrArg logicalEntry refused
    exact (sound query fuel _ ((Outcome.logicalEntry_runOutcome_eq_some_iff
      (machine.run fuel (start query)).2 _).mp recorded)).symm

/-- **Recording an exhausted machine run as a refusal is unsound** whenever the
query is answerable: the instance of `exhaustedAsRefusal_unsound`. -/
theorem exhaustedAsRefusal_unsound (machine : Machine State Event (Option Answer) Request)
    {logical : Query → Option Answer} {query : Query} {fuel : ℕ} {residual : State} {answer : Answer}
    (exhausted : (machine.run fuel (start query)).2 = .exhausted residual)
    (answerable : logical query = some answer) :
    exhaustedAsRefusal (cacheRun start machine fuel query) = some none ∧ logical query ≠ none :=
  Mettapedia.GSLT.Dynamics.CacheCoherence.exhaustedAsRefusal_unsound
    (run := fun query fuel => cacheRun start machine fuel query)
    (show (machine.run fuel (start query)).2.runOutcome = _ by rw [exhausted]; rfl) answerable

/-- **An answered machine query is refused at no fuel.** -/
theorem never_refused (machine : Machine State Event (Option Answer) Request) {query : Query}
    {fuel : ℕ} {answer : Answer} (answered : (machine.run fuel (start query)).2 = .finished (some answer))
    (fuel' : ℕ) : cacheRun start machine fuel' query ≠ .refused := by
  intro refused
  have recorded : logicalEntry (cacheRun start machine fuel' query) = some none := by
    rw [refused]; rfl
  exact machine.finished_unique (start query) answered (other := none)
    (fun impossible => nomatch impossible)
    fuel' ((Outcome.logicalEntry_runOutcome_eq_some_iff (machine.run fuel' (start query)).2 _).mp
      recorded)

end Machine

end Mettapedia.GSLT.Distinction.ProductiveBlocks

/-! ## Controls -/

namespace Mettapedia.GSLT.Distinction.RunOutcomes.Controls

open Mettapedia.GSLT.Dynamics.CacheCoherence
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Positive: the countdown of the cache contract never revises a final outcome,
so query `1` is refused at no fuel. -/
theorem countdown_never_refused (fuel : ℕ) : Controls.countdown 1 fuel ≠ .refused := by
  have never : NeverRevised (· = RunOutcome.exhausted) (Controls.countdown 1) := by
    intro fuel more le final
    unfold Controls.countdown at final ⊢
    by_cases enough : 1 ≤ fuel
    · rw [if_pos enough, if_pos (Nat.le_trans enough le)]
    · rw [if_neg enough] at final
      exact absurd rfl final
  exact refused_never_of_answered never (fuel := 1) (answer := 1) rfl fuel

/-- A run that answers at fuel `0` and refuses at every larger fuel. -/
def revising (fuel : ℕ) : RunOutcome ℕ :=
  match fuel with
  | 0 => .answered 0
  | _ + 1 => .refused

/-- **Negative: without the premise an answer is followed by a refusal.** -/
theorem revising_refuses :
    revising 0 = .answered 0 ∧ revising 1 = .refused ∧
      ¬ NeverRevised (· = RunOutcome.exhausted) revising := by
  refine ⟨rfl, rfl, fun never => ?_⟩
  exact refused_never_of_answered never (fuel := 0) (answer := 0) rfl 1 rfl

/-- **Negative: a fault is final and records no logical entry.**  Recording is
exact only on fault-free outcomes. -/
theorem fault_final_not_cacheable :
    (Outcome.faulted : Outcome Unit (Option ℕ) Empty).status.Final ∧
      logicalEntry (Outcome.faulted : Outcome Unit (Option ℕ) Empty).runOutcome = none :=
  ⟨trivial, rfl⟩

end Mettapedia.GSLT.Distinction.RunOutcomes.Controls
