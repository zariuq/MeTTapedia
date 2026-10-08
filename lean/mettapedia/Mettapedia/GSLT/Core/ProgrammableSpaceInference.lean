import Mettapedia.GSLT.Core.AnnotatedHorn
import Mathlib.Data.Set.Lattice

/-!
# Persistent positive inference and exact rule-instance fairness

An instance names one positive rule with a finite ordered body. Instances may
form an infinite type; distinct instances may have the same head and body.
The state observation is fact support. A policy selects an instance or idles;
the guarded step retains old support and adds only an enabled selected head.

Fairness requires a successful firing of every instance that becomes enabled.
An already completed ground instance need not be fired repeatedly. This is a
property of actual instances and states, rather than recurrence of job names.
Every such run has the same eventual support: precisely the finite-proof
closure. No assertion of finite completion or equality of receipts follows.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ProgrammableSpaceInference

open AnnotatedHorn

universe u v

structure Theory (Atom : Type u) (Instance : Type v) where
  seeds : Set Atom
  rule : Instance → DefiniteRule Atom

variable {Atom : Type u} {Instance : Type v}

namespace Theory

variable (theory : Theory Atom Instance)

def Enabled (ruleIndex : Instance) (support : Set Atom) : Prop :=
  ∀ atom ∈ (theory.rule ruleIndex).body, atom ∈ support

theorem enabled_mono (ruleIndex : Instance) {first second : Set Atom}
    (included : first ⊆ second) (enabled : theory.Enabled ruleIndex first) :
    theory.Enabled ruleIndex second :=
  fun atom member => included (enabled atom member)

inductive Derivable : Atom → Prop where
  | seed {atom : Atom} (present : atom ∈ theory.seeds) : Derivable atom
  | rule (ruleIndex : Instance)
      (premises : ∀ atom ∈ (theory.rule ruleIndex).body, Derivable atom) :
      Derivable (theory.rule ruleIndex).head

def closure : Set Atom := theory.Derivable

def Closed (support : Set Atom) : Prop :=
  ∀ ruleIndex, theory.Enabled ruleIndex support → (theory.rule ruleIndex).head ∈ support

theorem seeds_subset_closure : theory.seeds ⊆ theory.closure :=
  fun _ present => .seed present

theorem closure_closed : theory.Closed theory.closure :=
  fun ruleIndex premises => .rule ruleIndex premises

theorem closure_least {support : Set Atom} (seeds : theory.seeds ⊆ support)
    (closed : theory.Closed support) : theory.closure ⊆ support := by
  intro atom derivation
  induction derivation with
  | seed present => exact seeds present
  | rule ruleIndex _ induction => exact closed ruleIndex induction

def step (selected : Option Instance) (support : Set Atom) : Set Atom :=
  support ∪ {atom | ∃ ruleIndex, selected = some ruleIndex ∧
    theory.Enabled ruleIndex support ∧ (theory.rule ruleIndex).head = atom}

@[simp] theorem step_none (support : Set Atom) : theory.step none support = support := by
  ext atom
  simp [step]

theorem step_persistent (selected : Option Instance) (support : Set Atom) :
    support ⊆ theory.step selected support :=
  fun _ present => Or.inl present

theorem step_sound {support : Set Atom} (sound : support ⊆ theory.closure)
    (selected : Option Instance) : theory.step selected support ⊆ theory.closure := by
  intro atom present
  rcases present with old | ⟨ruleIndex, _, enabled, same⟩
  · exact sound old
  · rw [← same]
    exact .rule ruleIndex (fun premise member => sound (enabled premise member))

theorem step_eq_of_closed {support : Set Atom} (closed : theory.Closed support)
    (selected : Option Instance) : theory.step selected support = support := by
  apply Set.Subset.antisymm
  · intro atom present
    rcases present with old | ⟨ruleIndex, _, enabled, same⟩
    · exact old
    · exact same ▸ closed ruleIndex enabled
  · exact theory.step_persistent selected support

end Theory

structure Run (theory : Theory Atom Instance) where
  facts : Nat → Set Atom
  selected : Nat → Option Instance
  initial : facts 0 = theory.seeds
  advance : ∀ tick, facts (tick+1) = theory.step (selected tick) (facts tick)

abbrev Policy (Atom : Type u) (Instance : Type v) :=
  Nat → Set Atom → Option Instance

def iterate (theory : Theory Atom Instance) (policy : Policy Atom Instance) : Nat → Set Atom
  | 0 => theory.seeds
  | tick+1 => theory.step (policy tick (iterate theory policy tick)) (iterate theory policy tick)

def execute (theory : Theory Atom Instance) (policy : Policy Atom Instance) : Run theory where
  facts := iterate theory policy
  selected tick := policy tick (iterate theory policy tick)
  initial := rfl
  advance _ := rfl

namespace Run

variable {theory : Theory Atom Instance} (run : Run theory)

def Fires (ruleIndex : Instance) (tick : Nat) : Prop :=
  run.selected tick = some ruleIndex ∧ theory.Enabled ruleIndex (run.facts tick)

def RuleInstanceFair : Prop :=
  ∀ ruleIndex, (∃ tick, theory.Enabled ruleIndex (run.facts tick)) →
    ∃ tick, run.Fires ruleIndex tick

def RecurrentInstanceFair : Prop :=
  ∀ ruleIndex after, theory.Enabled ruleIndex (run.facts after) →
    ∃ tick, after ≤ tick ∧ run.Fires ruleIndex tick

theorem fair_of_recurrent (recurrent : run.RecurrentInstanceFair) : run.RuleInstanceFair := by
  intro ruleIndex ⟨after, enabled⟩
  obtain ⟨tick, _, fired⟩ := recurrent ruleIndex after enabled
  exact ⟨tick, fired⟩

theorem persistent (tick : Nat) : run.facts tick ⊆ run.facts (tick+1) := by
  rw [run.advance]
  exact theory.step_persistent _ _

theorem monotone {first second : Nat} (later : first ≤ second) :
    run.facts first ⊆ run.facts second := by
  induction later with
  | refl => exact Set.Subset.rfl
  | @step target _ induction =>
    exact fun _ present => run.persistent target (induction present)

theorem seeds_present (tick : Nat) : theory.seeds ⊆ run.facts tick := by
  rw [← run.initial]
  exact run.monotone (Nat.zero_le tick)

theorem sound (tick : Nat) : run.facts tick ⊆ theory.closure := by
  induction tick with
  | zero => rw [run.initial]; exact theory.seeds_subset_closure
  | succ tick induction => rw [run.advance]; exact theory.step_sound induction _

theorem fired_head {ruleIndex : Instance} {tick : Nat} (fired : run.Fires ruleIndex tick) :
    (theory.rule ruleIndex).head ∈ run.facts (tick+1) := by
  rw [run.advance]
  exact Or.inr ⟨ruleIndex, fired.1, fired.2, rfl⟩

def support : Set Atom := {atom | ∃ tick, atom ∈ run.facts tick}

theorem support_sound : run.support ⊆ theory.closure := by
  rintro atom ⟨tick, present⟩
  exact run.sound tick present

theorem finite_premises_available (body : List Atom)
    (available : ∀ atom ∈ body, atom ∈ run.support) :
    ∃ tick, ∀ atom ∈ body, atom ∈ run.facts tick := by
  induction body with
  | nil => exact ⟨0, by simp⟩
  | cons first rest induction =>
    obtain ⟨firstTick, firstPresent⟩ := available first (List.mem_cons_self)
    obtain ⟨restTick, restPresent⟩ := induction
      (fun atom member => available atom (List.mem_cons_of_mem _ member))
    refine ⟨max firstTick restTick, ?_⟩
    intro atom member
    rcases List.mem_cons.mp member with same | inRest
    · subst atom
      exact run.monotone (Nat.le_max_left _ _) firstPresent
    · exact run.monotone (Nat.le_max_right _ _) (restPresent atom inRest)

theorem support_closed (fair : run.RuleInstanceFair) : theory.Closed run.support := by
  intro ruleIndex enabled
  obtain ⟨ready, premises⟩ := run.finite_premises_available (theory.rule ruleIndex).body enabled
  obtain ⟨tick, fired⟩ := fair ruleIndex ⟨ready, premises⟩
  exact ⟨tick+1, run.fired_head fired⟩

theorem support_complete (fair : run.RuleInstanceFair) : theory.closure ⊆ run.support :=
  theory.closure_least (fun _ present => ⟨0, run.initial.symm ▸ present⟩)
    (run.support_closed fair)

theorem support_eq_closure (fair : run.RuleInstanceFair) : run.support = theory.closure :=
  Set.Subset.antisymm run.support_sound (run.support_complete fair)

theorem eventually_iff_derivable (fair : run.RuleInstanceFair) (atom : Atom) :
    (∃ tick, atom ∈ run.facts tick) ↔ theory.Derivable atom := by
  change atom ∈ run.support ↔ atom ∈ theory.closure
  rw [run.support_eq_closure fair]

theorem finite_prefix_exact_iff_closed (tick : Nat) :
    run.facts tick = theory.closure ↔ theory.Closed (run.facts tick) := by
  constructor
  · intro exactSupport
    rw [exactSupport]
    exact theory.closure_closed
  · intro closed
    exact Set.Subset.antisymm (run.sound tick)
      (theory.closure_least (run.seeds_present tick) closed)

theorem closed_prefix_stable {tick : Nat} (closed : theory.Closed (run.facts tick))
    (extra : Nat) : run.facts (tick+extra) = run.facts tick := by
  induction extra with
  | zero => rw [Nat.add_zero]
  | succ extra induction =>
    rw [Nat.add_succ, run.advance, induction]
    exact theory.step_eq_of_closed closed _

theorem idle_prefix_stable {tick : Nat}
    (idle : ∀ later, tick ≤ later → run.selected later = none) (extra : Nat) :
    run.facts (tick+extra) = run.facts tick := by
  induction extra with
  | zero => rw [Nat.add_zero]
  | succ extra induction =>
    rw [Nat.add_succ, run.advance, idle (tick+extra) (Nat.le_add_right _ _),
      theory.step_none, induction]

end Run

theorem fair_policies_agree {theory : Theory Atom Instance} (first second : Run theory)
    (firstFair : first.RuleInstanceFair) (secondFair : second.RuleInstanceFair) :
    first.support = second.support :=
  (first.support_eq_closure firstFair).trans (second.support_eq_closure secondFair).symm

structure DeclaredMeaning (theory : Theory Atom Instance) where
  holds : Set Atom
  seedsSound : theory.seeds ⊆ holds
  rulesSound : theory.Closed holds
  complete : holds ⊆ theory.closure

theorem fair_support_eq_meaning {theory : Theory Atom Instance}
    (meaning : DeclaredMeaning theory) (run : Run theory) (fair : run.RuleInstanceFair) :
    run.support = meaning.holds := by
  rw [run.support_eq_closure fair]
  exact Set.Subset.antisymm (theory.closure_least meaning.seedsSound meaning.rulesSound) meaning.complete

end Mettapedia.GSLT.Core.ProgrammableSpaceInference
