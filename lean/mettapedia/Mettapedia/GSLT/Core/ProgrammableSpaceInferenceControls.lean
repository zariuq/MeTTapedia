import Mettapedia.GSLT.Core.ProgrammableSpaceInference
import Mathlib.Tactic

/-!
# Infinite growth and boundaries of support agreement

The positive instance generates every natural number, with an exact finite
prefix and successful firing of every ground rule instance. A delayed fair
policy has the same eventual support and a different finite-budget result.

One-shot schedules can execute all job templates and still miss a later
enabled instance. A recurring job can starve one of its ground instances.
Destructive updates invalidate persistence. Finally, fair policies can agree
on support while differing in successful firing provenance, count and cost.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ProgrammableSpaceInferenceControls

open ProgrammableSpaceInference

def growingTheory : Theory Nat Nat where
  seeds := {0}
  rule ruleIndex := ⟨[ruleIndex], ruleIndex+1⟩

def growing : Run growingTheory where
  facts tick := {atom | atom ≤ tick}
  selected tick := some tick
  initial := by ext atom; simp [growingTheory]
  advance tick := by
    ext atom
    change atom ≤ tick+1 ↔ atom ≤ tick ∨ ∃ index : Nat,
      some tick = some index ∧ (∀ premise ∈ [index], premise ≤ tick) ∧ index+1 = atom
    constructor
    · intro present
      rcases Nat.le_succ_iff.mp present with previous | same
      · exact Or.inl previous
      · refine Or.inr ⟨tick, rfl, ?_, same.symm⟩
        intro premise member
        have equal : premise = tick := List.mem_singleton.mp member
        subst premise
        exact Nat.le_refl tick
    · rintro (previous | ⟨index, selected, _, head⟩)
      · exact Nat.le.step previous
      · have equal : index = tick := (Option.some.inj selected).symm
        subst index
        rw [← head]

theorem growing_fair : growing.RuleInstanceFair := by
  intro ruleIndex _
  refine ⟨ruleIndex, rfl, ?_⟩
  simp [Theory.Enabled, growingTheory, growing]

theorem growing_is_not_recurrently_fair : ¬ growing.RecurrentInstanceFair := by
  intro recurrent
  obtain ⟨tick, later, fired⟩ := recurrent 0 1 (by simp [Theory.Enabled, growingTheory, growing])
  have atZero : tick = 0 := Option.some.inj fired.1
  omega

theorem growing_execution (tick : Nat) :
    (execute growingTheory (fun stage _ => some stage)).facts tick = growing.facts tick := by
  induction tick with
  | zero => exact growing.initial.symm
  | succ tick induction =>
    change iterate growingTheory (fun stage _ => some stage) tick = growing.facts tick at induction
    change growingTheory.step (some tick) (iterate growingTheory (fun stage _ => some stage) tick) = _
    rw [induction]
    exact (growing.advance tick).symm

theorem growing_support : growing.support = Set.univ := by
  ext atom
  constructor
  · intro _; trivial
  · intro _; exact ⟨atom, Nat.le_refl atom⟩

theorem every_nat_derivable (atom : Nat) : growingTheory.Derivable atom :=
  growing.support_sound ⟨atom, Nat.le_refl atom⟩

theorem each_prefix_has_a_new_fact (tick : Nat) :
    tick+1 ∉ growing.facts tick ∧ tick+1 ∈ growing.facts (tick+1) :=
  ⟨Nat.not_succ_le_self tick, Nat.le_refl _⟩

theorem growing_never_finishes (tick : Nat) : growing.facts tick ≠ growingTheory.closure := by
  intro exactSupport
  have present : tick+1 ∈ growing.facts tick := exactSupport.symm ▸ every_nat_derivable (tick+1)
  exact (each_prefix_has_a_new_fact tick).1 present

def delayed (delay : Nat) : Run growingTheory where
  facts tick := {atom | atom ≤ tick-delay}
  selected tick := if delay ≤ tick then some (tick-delay) else none
  initial := by ext atom; simp [growingTheory]
  advance tick := by
    cases Nat.decLe delay tick with
    | isTrue active =>
      rw [if_pos active, Nat.succ_sub active]
      exact growing.advance (tick-delay)
    | isFalse inactive =>
      rw [if_neg inactive, Theory.step_none]
      have next : tick+1 ≤ delay := Nat.lt_of_not_ge inactive
      rw [Nat.sub_eq_zero_of_le next,
        Nat.sub_eq_zero_of_le (Nat.le_trans (Nat.le_succ tick) next)]

theorem delayed_fair (delay : Nat) : (delayed delay).RuleInstanceFair := by
  intro ruleIndex _
  refine ⟨delay+ruleIndex, ?_, ?_⟩
  · change (if delay ≤ delay+ruleIndex then some (delay+ruleIndex-delay) else none) = some ruleIndex
    rw [if_pos (Nat.le_add_right delay ruleIndex), Nat.add_sub_cancel_left]
  · intro atom member
    have same : atom = ruleIndex := List.mem_singleton.mp member
    subst atom
    change ruleIndex ≤ delay+ruleIndex-delay
    rw [Nat.add_sub_cancel_left]

theorem delayed_execution (delay tick : Nat) :
    (execute growingTheory (fun stage _ => if delay ≤ stage then some (stage-delay) else none)).facts tick =
      (delayed delay).facts tick := by
  induction tick with
  | zero => exact (delayed delay).initial.symm
  | succ tick induction =>
    change iterate growingTheory (fun stage _ => if delay ≤ stage then some (stage-delay) else none) tick =
      (delayed delay).facts tick at induction
    change growingTheory.step (if delay ≤ tick then some (tick-delay) else none)
      (iterate growingTheory (fun stage _ => if delay ≤ stage then some (stage-delay) else none) tick) = _
    rw [induction]
    exact ((delayed delay).advance tick).symm

theorem fair_eventual_support_agrees (delay : Nat) : growing.support = (delayed delay).support :=
  fair_policies_agree growing (delayed delay) growing_fair (delayed_fair delay)

theorem finite_budget_does_not_determine_fair_support (budget : Nat) :
    growing.RuleInstanceFair ∧ (delayed (budget+1)).RuleInstanceFair ∧
      growing.support = (delayed (budget+1)).support ∧
      growing.facts (budget+1) ≠ (delayed (budget+1)).facts (budget+1) := by
  refine ⟨growing_fair, delayed_fair _, fair_eventual_support_agrees _, ?_⟩
  intro same
  have available : 1 ∈ growing.facts (budget+1) := Nat.succ_le_succ (Nat.zero_le budget)
  have missing : 1 ∉ (delayed (budget+1)).facts (budget+1) := by
    change ¬ 1 ≤ budget+1-(budget+1)
    rw [Nat.sub_self]
    decide
  exact missing (same ▸ available)

namespace Starvation

def theory : Theory Bool Bool where
  seeds := {false}
  rule ruleIndex := ⟨[false], ruleIndex⟩

def run : Run theory where
  facts _ := {false}
  selected _ := some false
  initial := rfl
  advance _ := by ext atom; simp [Theory.step, Theory.Enabled, theory]

theorem loop_fires_forever (tick : Nat) : run.Fires false tick := by
  exact ⟨rfl, by simp [Theory.Enabled, theory, run]⟩

def JobRecurs : Prop :=
  ∀ (_job : Unit) after, ∃ tick, after ≤ tick ∧
    ∃ ruleIndex, run.Fires ruleIndex tick

theorem job_recurs : JobRecurs :=
  fun _ after => ⟨after, le_rfl, false, loop_fires_forever after⟩

theorem answer_enabled (tick : Nat) : theory.Enabled true (run.facts tick) := by
  simp [Theory.Enabled, theory, run]

theorem answer_never_fires (tick : Nat) : ¬ run.Fires true tick := by
  simp [Run.Fires, run]

theorem not_rule_instance_fair : ¬ run.RuleInstanceFair := by
  intro fair
  obtain ⟨tick, fired⟩ := fair true ⟨0, answer_enabled 0⟩
  exact answer_never_fires tick fired

theorem job_fairness_does_not_imply_rule_instance_fairness :
    JobRecurs ∧ ¬ run.RuleInstanceFair := ⟨job_recurs, not_rule_instance_fair⟩

theorem missing_derivable_answer : theory.Derivable true ∧ true ∉ run.support := by
  refine ⟨.rule true ?_, ?_⟩
  · intro atom member
    have same : atom = false := by simpa [theory] using member
    subst atom
    exact .seed rfl
  · simp [Run.support, run]

end Starvation

namespace OneShot

inductive Atom where
  | p (value : Bool)
  | q (value : Bool)
  deriving DecidableEq

abbrev RuleIndex := Option Bool

def theory : Theory Atom RuleIndex where
  seeds := {Atom.p false}
  rule
    | none => ⟨[], Atom.p true⟩
    | some value => ⟨[Atom.p value], Atom.q value⟩

def consumerFirst : Policy Atom RuleIndex := fun tick _ =>
  match tick with
  | 0 => some (some false)
  | 1 => some (some true)
  | 2 => some none
  | _ => none

def producerFirst : Policy Atom RuleIndex := fun tick _ =>
  match tick with
  | 0 => some none
  | 1 => some (some false)
  | 2 => some (some true)
  | _ => none

abbrev first := execute theory consumerFirst
abbrev second := execute theory producerFirst

theorem first_final_support : first.facts 3 = {Atom.p false, Atom.q false, Atom.p true} := by
  ext atom
  cases atom with
  | p value => cases value <;> simp [execute, iterate, theory, consumerFirst, Theory.step, Theory.Enabled]
  | q value => cases value <;> simp [execute, iterate, theory, consumerFirst, Theory.step, Theory.Enabled]

theorem first_stops : ∀ tick, 3 ≤ tick → first.selected tick = none := by
  intro tick later
  cases tick with
  | zero => omega
  | succ tick =>
    cases tick with
    | zero => omega
    | succ tick =>
      cases tick with
      | zero => omega
      | succ tick => rfl

theorem later_producer_cannot_replay_consumer (extra : Nat) :
    Atom.q true ∉ first.facts (3+extra) := by
  rw [first.idle_prefix_stable first_stops extra, first_final_support]
  simp

theorem first_misses_forever : Atom.q true ∉ first.support := by
  rintro ⟨tick, present⟩
  have later := first.monotone (Nat.le_max_left tick 3) present
  have missing := later_producer_cannot_replay_consumer (max tick 3 - 3)
  have same : 3+(max tick 3-3) = max tick 3 := by omega
  rw [same] at missing
  exact missing later

theorem producer_first_gets_later_instance : Atom.q true ∈ second.facts 3 := by
  simp [execute, iterate, theory, producerFirst, Theory.step, Theory.Enabled]

theorem consumer_templates_ran_in_both_orders :
    first.selected 0 = some (some false) ∧ first.selected 1 = some (some true) ∧
      first.selected 2 = some none ∧ second.selected 0 = some none ∧
      second.selected 1 = some (some false) ∧ second.selected 2 = some (some true) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem one_shot_policies_have_different_support : first.support ≠ second.support := by
  intro same
  exact first_misses_forever (same.symm ▸ ⟨3, producer_first_gets_later_instance⟩)

theorem late_instance_is_enabled : theory.Enabled (some true) (first.facts 3) := by
  rw [first_final_support]
  simp [Theory.Enabled, theory]

theorem one_shot_not_rule_instance_fair : ¬ first.RuleInstanceFair := by
  intro fair
  obtain ⟨tick, fired⟩ := fair (some true) ⟨3, late_instance_is_enabled⟩
  exact first_misses_forever ⟨tick+1, first.fired_head fired⟩

end OneShot

namespace Destructive

def erase (support : Set Bool) : Set Bool := {atom | atom ∈ support ∧ atom ≠ false}
def copy (support : Set Bool) : Set Bool := Starvation.theory.step (some true) support

theorem erase_then_copy : copy (erase {false}) = ∅ := by
  ext atom
  constructor
  · rintro (retained | ⟨ruleIndex, _, enabled, _⟩)
    · exact retained.2 retained.1
    · have impossible := enabled false (List.mem_singleton_self false)
      exact impossible.2 rfl
  · intro impossible
    exact False.elim impossible

theorem copy_then_erase : erase (copy {false}) = {true} := by
  ext atom
  constructor
  · intro retained
    rcases retained.1 with original | ⟨ruleIndex, selected, _, head⟩
    · exact False.elim (retained.2 original)
    · have same : ruleIndex = true := (Option.some.inj selected).symm
      subst ruleIndex
      exact head.symm
  · intro same
    change atom = true at same
    subst atom
    refine ⟨Or.inr ⟨true, rfl, ?_, rfl⟩, by decide⟩
    intro premise member
    exact List.mem_singleton.mp member

theorem destructive_orders_disagree : copy (erase {false}) ≠ erase (copy {false}) := by
  rw [erase_then_copy, copy_then_erase]
  intro same
  have present : true ∈ (∅ : Set Bool) := same.symm ▸ (show true ∈ ({true} : Set Bool) from rfl)
  exact present

theorem erase_violates_persistence : ¬ ({false} : Set Bool) ⊆ erase {false} := by
  intro preserved
  have impossible := preserved (show false ∈ ({false} : Set Bool) from rfl)
  exact impossible.2 rfl

end Destructive

namespace ProvenanceAndCost

def theory : Theory Bool Bool where
  seeds := ∅
  rule _ := ⟨[], true⟩

def first : Policy Bool Bool := fun tick _ =>
  match tick with
  | 0 => some false
  | 1 => some true
  | _ => none

def reverse : Policy Bool Bool := fun tick _ =>
  match tick with
  | 0 => some true
  | 1 => some false
  | _ => none

def repeated : Policy Bool Bool := fun tick _ =>
  match tick with
  | 0 => some false
  | 1 => some false
  | 2 => some true
  | _ => none

abbrev firstRun := execute theory first
abbrev reverseRun := execute theory reverse
abbrev repeatRun := execute theory repeated

theorem first_fair : firstRun.RuleInstanceFair := by
  intro ruleIndex _
  cases ruleIndex
  · exact ⟨0, rfl, by simp [Theory.Enabled, theory]⟩
  · exact ⟨1, rfl, by simp [Theory.Enabled, theory]⟩

theorem reverse_fair : reverseRun.RuleInstanceFair := by
  intro ruleIndex _
  cases ruleIndex
  · exact ⟨1, rfl, by simp [Theory.Enabled, theory]⟩
  · exact ⟨0, rfl, by simp [Theory.Enabled, theory]⟩

theorem repeat_fair : repeatRun.RuleInstanceFair := by
  intro ruleIndex _
  cases ruleIndex
  · exact ⟨0, rfl, by simp [Theory.Enabled, theory]⟩
  · exact ⟨2, rfl, by simp [Theory.Enabled, theory]⟩

def receipts (run : Run theory) (budget : Nat) : List Bool :=
  (List.range budget).filterMap run.selected

theorem every_receipt_is_successful (run : Run theory) (tick : Nat) (ruleIndex : Bool)
    (selected : run.selected tick = some ruleIndex) : run.Fires ruleIndex tick :=
  ⟨selected, by simp [Theory.Enabled, theory]⟩

def cost (run : Run theory) (budget : Nat) : Nat := (receipts run budget).length

theorem same_support_distinct_provenance :
    firstRun.support = reverseRun.support ∧ receipts firstRun 2 ≠ receipts reverseRun 2 := by
  refine ⟨fair_policies_agree firstRun reverseRun first_fair reverse_fair, ?_⟩
  decide +kernel

theorem same_support_distinct_counted_cost :
    firstRun.support = repeatRun.support ∧ cost firstRun 3 = 2 ∧ cost repeatRun 3 = 3 := by
  exact ⟨fair_policies_agree firstRun repeatRun first_fair repeat_fair, by decide +kernel, by decide +kernel⟩

theorem same_current_support_distinct_cost :
    firstRun.facts 3 = repeatRun.facts 3 ∧ cost firstRun 3 ≠ cost repeatRun 3 := by
  constructor
  · ext atom
    cases atom <;> simp [execute, iterate, first, repeated, Theory.step, Theory.Enabled, theory]
  · decide +kernel

theorem ordered_receipts_cannot_descend_to_support :
    ¬ ∃ read : Set Bool → List Bool,
      read firstRun.support = receipts firstRun 2 ∧
        read reverseRun.support = receipts reverseRun 2 := by
  rintro ⟨read, firstReading, reverseReading⟩
  have same := congrArg read same_support_distinct_provenance.1
  rw [firstReading, reverseReading] at same
  exact same_support_distinct_provenance.2 same

theorem counted_cost_cannot_descend_to_current_support :
    ¬ ∃ read : Set Bool → Nat,
      read (firstRun.facts 3) = cost firstRun 3 ∧
        read (repeatRun.facts 3) = cost repeatRun 3 := by
  rintro ⟨read, firstReading, repeatReading⟩
  have same := congrArg read same_current_support_distinct_cost.1
  rw [firstReading, repeatReading] at same
  exact same_current_support_distinct_cost.2 same

/-- Reuse the existing bag/support comparison, including its standard host
finite-set extensionality and deduplication dependencies. -/
theorem support_erases_derivation_multiplicity :
    Multiset.card (AnnotatedHorn.stepBag [theory.rule false, theory.rule true]
      (fun _ => (∅ : Multiset Unit)) true) ≠
      (AnnotatedHorn.stepBag [theory.rule false, theory.rule true]
        (fun _ => (∅ : Multiset Unit)) true).toFinset.card := by
  exact AnnotatedHorn.support_forgets_multiplicity true

end ProvenanceAndCost

end Mettapedia.GSLT.Core.ProgrammableSpaceInferenceControls
