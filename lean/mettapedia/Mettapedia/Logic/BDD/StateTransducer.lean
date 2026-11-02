import Mettapedia.Logic.BDD.StatePredicates

/-!
# Guarded synchronous state transducers

Source rules use the existing pure Boolean guard language. Their relation is
defined by ordinary guard evaluation and simultaneous assignment. Symbolic
predecessors use independently constructed BDD substitution and disjunction.
An executable invariant check certifies that enabled transitions preserve a
declared valid-state domain. Negation and predecessor operations retain that
domain explicitly rather than introducing invalid encoded states.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.BDDCore.StateTransducer

open StatePredicates
open Mettapedia.Machines.GuardConjunctionCompiler (Guard)
open Mettapedia.Machines.GuardEvaluationRegimes (scalar)

structure Rule (n : Nat) where
  guard : Guard (Fin n)
  assign : Fin n → Guard (Fin n)

def Rule.nextState {n : Nat} (rule : Rule n) (state : State n) : State n :=
  fun v => scalar state (rule.assign v)

def Rule.Fires {n : Nat} (rule : Rule n) (before after : State n) : Prop :=
  scalar before rule.guard = true ∧ after = rule.nextState before

def Transition {n : Nat} (rules : List (Rule n)) (before after : State n) : Prop :=
  ∃ rule ∈ rules, rule.Fires before after

def rulePre {n : Nat} (rule : Rule n) (target : Diagram n) : Diagram n :=
  conj (compileGuard rule.guard) (substitute (fun v => compileGuard (rule.assign v)) target.val)

theorem rulePre_eval {n : Nat} (rule : Rule n) (target : Diagram n) (state : State n) :
    (rulePre rule target).val.eval state =
      (scalar state rule.guard && target.val.eval (rule.nextState state)) := by
  simp only [rulePre, conj, apply_eval, compileGuard_eval, substitute_eval]
  rfl

def rawPre {n : Nat} (rules : List (Rule n)) (target : Diagram n) : Diagram n :=
  rules.foldr (fun rule accumulated => disj (rulePre rule target) accumulated) (falsity n)

theorem rawPre_eval {n : Nat} (rules : List (Rule n)) (target : Diagram n) (before : State n) :
    (rawPre rules target).val.eval before = true ↔
      ∃ after, Transition rules before after ∧ target.val.eval after = true := by
  induction rules with
  | nil => simp [rawPre, falsity, Transition]
  | cons rule rest ih =>
    simp only [rawPre, List.foldr_cons, disj, apply_eval, Bool.or_eq_true]
    rw [rulePre_eval]
    change ((scalar before rule.guard && target.val.eval (rule.nextState before)) = true ∨
      (rawPre rest target).val.eval before = true) ↔ _
    rw [ih]
    simp only [Transition, Rule.Fires, List.mem_cons]
    constructor
    · rintro (held | ⟨after, ⟨other, member, enabled, targetEq⟩, result⟩)
      · exact ⟨rule.nextState before, ⟨rule, Or.inl rfl, (Bool.and_eq_true_iff.mp held).1, rfl⟩,
          (Bool.and_eq_true_iff.mp held).2⟩
      · exact ⟨after, ⟨other, Or.inr member, enabled, targetEq⟩, result⟩
    · rintro ⟨after, ⟨other, member | member, enabled, targetEq⟩, result⟩
      · subst other; subst after; exact Or.inl (Bool.and_eq_true_iff.mpr ⟨enabled, result⟩)
      · exact Or.inr ⟨after, ⟨other, member, enabled, targetEq⟩, result⟩

def Relation {n : Nat} (domain : Diagram n) (rules : List (Rule n)) (before after : State n) : Prop :=
  domain.val.eval before = true ∧ Transition rules before after ∧ domain.val.eval after = true

def pre {n : Nat} (domain : Diagram n) (rules : List (Rule n)) (target : Diagram n) : Diagram n :=
  conj domain (rawPre rules (conj domain target))

theorem pre_eval {n : Nat} (domain : Diagram n) (rules : List (Rule n)) (target : Diagram n) (before : State n) :
    (pre domain rules target).val.eval before = true ↔
      ∃ after, Relation domain rules before after ∧ target.val.eval after = true := by
  simp only [pre, conj, apply_eval, Bool.and_eq_true_iff]
  rw [rawPre_eval]
  simp only [apply_eval, Bool.and_eq_true_iff, Relation]
  constructor
  · rintro ⟨valid, after, edge, nextValid, held⟩
    exact ⟨after, ⟨valid, edge, nextValid⟩, held⟩
  · rintro ⟨after, ⟨valid, edge, nextValid⟩, held⟩
    exact ⟨valid, after, edge, nextValid, held⟩

def within {n : Nat} (domain property : Diagram n) : Diagram n := conj domain property
def complement {n : Nat} (domain property : Diagram n) : Diagram n := conj domain (neg property)

def Preserves {n : Nat} (domain : Diagram n) (rule : Rule n) : Prop :=
  ∀ state, domain.val.eval state = true → scalar state rule.guard = true →
    domain.val.eval (rule.nextState state) = true

def checkRule {n : Nat} (domain : Diagram n) (rule : Rule n) : Bool :=
  equivalent (conj domain (rulePre rule (neg domain))) (falsity n)

theorem checkRule_iff {n : Nat} (domain : Diagram n) (rule : Rule n) :
    checkRule domain rule = true ↔ Preserves domain rule := by
  rw [checkRule, equivalent_iff]
  simp only [conj, apply_eval, rulePre_eval, neg, bddNot_eval, falsity, BDD.eval_zero, Preserves]
  constructor
  · intro checked state valid enabled
    have here := checked state
    simp [valid, enabled] at here
    exact here
  · intro preserved state
    cases valid : domain.val.eval state <;> cases enabled : scalar state rule.guard <;>
      simp [valid, enabled, preserved state]

structure Certified (n : Nat) (domain : Diagram n) where
  rules : List (Rule n)
  closed : ∀ rule ∈ rules, Preserves domain rule

def infer {n : Nat} (domain : Diagram n) (rules : List (Rule n)) : Option (Certified n domain) :=
  if checked : rules.all (checkRule domain) then
    some ⟨rules, fun rule member => (checkRule_iff domain rule).mp ((List.all_eq_true.mp checked) rule member)⟩
  else none

theorem valid_transition_not_dropped {n : Nat} {domain : Diagram n} (program : Certified n domain)
    (before after : State n) (valid : domain.val.eval before = true) :
    Relation domain program.rules before after ↔ Transition program.rules before after := by
  constructor
  · exact fun edge => edge.2.1
  · intro edge
    obtain ⟨rule, member, enabled, rfl⟩ := edge
    exact ⟨valid, ⟨rule, member, enabled, rfl⟩, program.closed rule member before valid enabled⟩

/-- This list observer retains the occurrence multiplicity that existential
predecessors intentionally forget. -/
def successors {n : Nat} (rules : List (Rule n)) (state : State n) : List (State n) :=
  rules.filterMap fun rule => if scalar state rule.guard then some (rule.nextState state) else none

def anyEnabled {n : Nat} (rules : List (Rule n)) : Guard (Fin n) :=
  rules.foldr (fun rule guard => .either rule.guard guard) (.constant false)

theorem anyEnabled_eval {n : Nat} (rules : List (Rule n)) (state : State n) :
    scalar state (anyEnabled rules) = rules.any (fun rule => scalar state rule.guard) := by
  induction rules <;> simp_all [anyEnabled, scalar]

def stutterRule {n : Nat} (rules : List (Rule n)) : Rule n :=
  ⟨.neg (anyEnabled rules), fun v => .atom v⟩

def totalize {n : Nat} (rules : List (Rule n)) : List (Rule n) := rules ++ [stutterRule rules]

theorem stutter_preserves {n : Nat} (domain : Diagram n) (rules : List (Rule n)) :
    Preserves domain (stutterRule rules) := by
  intro state valid _
  change domain.val.eval state = true
  exact valid

def Certified.withStuttering {n : Nat} {domain : Diagram n} (program : Certified n domain) : Certified n domain :=
  ⟨totalize program.rules, by
    intro rule member
    rcases List.mem_append.mp member with old | added
    · exact program.closed rule old
    · have same : rule = stutterRule program.rules := List.mem_singleton.mp added
      subst rule
      exact stutter_preserves domain program.rules⟩

theorem totalized_relation {n : Nat} (rules : List (Rule n)) (before after : State n) :
    Transition (totalize rules) before after ↔
      Transition rules before after ∨ (¬ (∃ next, Transition rules before next)) ∧ after = before := by
  simp only [Transition, totalize, List.mem_append, List.mem_singleton]
  simp [Rule.Fires, stutterRule, scalar, anyEnabled_eval]
  aesop

theorem stuttering_has_successor {n : Nat} {domain : Diagram n} (program : Certified n domain)
    (state : State n) (valid : domain.val.eval state = true) :
    ∃ next, Relation domain program.withStuttering.rules state next := by
  classical
  by_cases enabled : ∃ next, Transition program.rules state next
  · obtain ⟨next, edge⟩ := enabled
    refine ⟨next, (valid_transition_not_dropped program.withStuttering state next valid).mpr ?_⟩
    exact (totalized_relation program.rules state next).mpr (Or.inl edge)
  · refine ⟨state, (valid_transition_not_dropped program.withStuttering state state valid).mpr ?_⟩
    exact (totalized_relation program.rules state state).mpr (Or.inr ⟨enabled, rfl⟩)

namespace Controls

def flip : Rule 1 := ⟨.constant true, fun _ => .neg (.atom 0)⟩
def stay : Rule 1 := ⟨.constant true, fun v => .atom v⟩

theorem repeated_rule_has_two_occurrences :
    (successors [stay, stay] (fun _ => false)).length = 2 ∧
    (successors [stay] (fun _ => false)).length = 1 := by decide

theorem relative_complement_excludes_invalid_states :
    (complement (bit (0 : Fin 1)) (falsity 1)).val.eval (fun _ => false) = false ∧
    (neg (falsity 1)).val.eval (fun _ => false) = true := by
  simp [complement, conj, bit, neg, falsity]

theorem invariant_escape_declines : checkRule (bit (0 : Fin 1)) flip = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have escaped := (checkRule_iff _ _).mp accepted (fun _ => true) (by simp [bit]) rfl
  simp [flip, Rule.nextState, scalar, bit] at escaped

end Controls
end Mettapedia.Logic.BDDCore.StateTransducer
