import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRoundsStep

/-!
# A dependency frontier for the actual positive set-store instances

The instance family need not be finite or pre-grounded into a finite Horn
program. An instance is inspected only if it has an empty premise set or
reads a newly arrived row. The invariant accounts for every omitted
instance's outputs. Rounds agree at every stage with the existing immediate
consequence operator, and hence with actual `every` executions of ground
range-restricted propagation programs. This compares sets of rows, not
ordered attempts, duplicate answers, effects or open-row refinements.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRounds.SemiNaive

universe u v
variable {G : Type u} {I : Type v}

structure Frontier (G : Type u) where
  known : Set G
  delta : Set G

def Hot (rule : SetStoreClosure.Instance G) (delta : Set G) : Prop :=
  rule.read = ∅ ∨ ∃ premise ∈ rule.read, premise ∈ delta

def heads (rules : I → SetStoreClosure.Instance G) (state : Frontier G) : Set G :=
  {value | ∃ i, (∀ premise ∈ (rules i).read, premise ∈ state.known) ∧
    Hot (rules i) state.delta ∧ value ∈ (rules i).made}

def round (rules : I → SetStoreClosure.Instance G) (state : Frontier G) : Frontier G :=
  let fresh := heads rules state \ state.known
  ⟨state.known ∪ fresh, fresh⟩

structure Invariant (rules : I → SetStoreClosure.Instance G) (state : Frontier G) : Prop where
  delta_known : state.delta ⊆ state.known
  old_complete : ∀ i, (∀ premise ∈ (rules i).read, premise ∈ state.known) →
    Hot (rules i) state.delta ∨ ∀ value ∈ (rules i).made, value ∈ state.known

theorem initial_invariant (rules : I → SetStoreClosure.Instance G) (seed : Set G) :
    Invariant rules ⟨seed, seed⟩ := by
  classical
  refine ⟨Set.Subset.refl _, fun i enabled => Or.inl ?_⟩
  by_cases empty : (rules i).read = ∅
  · exact Or.inl empty
  · obtain ⟨premise, member⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    exact Or.inr ⟨premise, member, enabled premise member⟩

theorem round_known (rules : I → SetStoreClosure.Instance G) (state : Frontier G)
    (valid : Invariant rules state) :
    (round rules state).known = immediate rules state.known := by
  ext value
  constructor
  · rintro (old | ⟨⟨i, enabled, _, made⟩, _⟩)
    · exact Or.inl old
    · exact Or.inr ⟨i, enabled, made⟩
  · rintro (old | ⟨i, enabled, made⟩)
    · exact Or.inl old
    · rcases valid.old_complete i enabled with hot | old
      · by_cases held : value ∈ state.known
        · exact Or.inl held
        · exact Or.inr ⟨⟨i, enabled, hot, made⟩, held⟩
      · exact Or.inl (old value made)

theorem round_invariant (rules : I → SetStoreClosure.Instance G) (state : Frontier G)
    (valid : Invariant rules state) : Invariant rules (round rules state) := by
  classical
  refine ⟨fun _ member => Or.inr member, fun i enabled => ?_⟩
  by_cases hot : Hot (rules i) (round rules state).delta
  · exact Or.inl hot
  · right
    have oldEnabled : ∀ premise ∈ (rules i).read, premise ∈ state.known := by
      intro premise member
      rcases enabled premise member with old | fresh
      · exact old
      · exact False.elim (hot (Or.inr ⟨premise, member, fresh⟩))
    rw [round_known rules state valid]
    exact fun value made => Or.inr ⟨i, oldEnabled, made⟩

theorem delta_is_fresh (rules : I → SetStoreClosure.Instance G) (state : Frontier G) :
    Disjoint (round rules state).delta state.known := by
  exact Set.disjoint_left.mpr fun _ fresh old => fresh.2 old

def rounds (rules : I → SetStoreClosure.Instance G) (seed : Set G) : Nat → Frontier G
  | 0 => ⟨seed, seed⟩
  | n + 1 => round rules (rounds rules seed n)

theorem rounds_invariant (rules : I → SetStoreClosure.Instance G) (seed : Set G) (n : Nat) :
    Invariant rules (rounds rules seed n) := by
  induction n with
  | zero => exact initial_invariant rules seed
  | succ n ih => exact round_invariant rules _ ih

theorem rounds_eq_stage (rules : I → SetStoreClosure.Instance G) (seed : Set G) (n : Nat) :
    (rounds rules seed n).known = stage rules seed n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (round rules (rounds rules seed n)).known = immediate rules (stage rules seed n)
    rw [round_known rules _ (rounds_invariant rules seed n), ih]

theorem completed_eq_closure [DecidableEq G] (rules : I → SetStoreClosure.Instance G)
    (seed : Finset G) (n : Nat)
    (stopped : immediate rules (rounds rules (seed : Set G) n).known =
      (rounds rules (seed : Set G) n).known) :
    (rounds rules (seed : Set G) n).known = SetStoreClosure.closure rules seed := by
  rw [rounds_eq_stage] at stopped ⊢
  exact (stage_eq_closure_iff_fixed rules seed n).mpr stopped

theorem delta_empty_iff_fixed (rules : I → SetStoreClosure.Instance G) (state : Frontier G)
    (valid : Invariant rules state) :
    (round rules state).delta = ∅ ↔ immediate rules state.known = state.known := by
  rw [← round_known rules state valid]
  constructor
  · intro empty
    change state.known ∪ (heads rules state \ state.known) = state.known
    change heads rules state \ state.known = ∅ at empty
    rw [empty, Set.union_empty]
  · intro fixed
    ext value
    constructor
    · intro fresh
      have member : value ∈ (round rules state).known := Or.inr fresh
      rw [fixed] at member
      exact fresh.2 member
    · intro impossible
      exact False.elim impossible

/-- A closed finite carrier gives a finite stopping round, even when the
ground instance family is infinite. No bound on source terms is imposed. -/
theorem exists_finished [DecidableEq G] (rules : I → SetStoreClosure.Instance G)
    (carrier : Finset G) (closed : SetStoreClosure.Closed rules carrier)
    (seed : Finset G) (inside : seed ⊆ carrier) :
    ∃ n, (rounds rules (seed : Set G) n).known = SetStoreClosure.closure rules seed ∧
      (round rules (rounds rules (seed : Set G) n)).delta = ∅ := by
  obtain ⟨rows, reached, terminal⟩ :=
    SetStoreClosure.exists_terminal rules carrier closed seed inside
  have complete := SetStoreClosure.terminal_eq_closure rules seed reached terminal
  have covered : ∀ value ∈ rows, value ∈ finiteProofs rules (seed : Set G) := by
    intro value member
    rw [finiteProofs_eq_closure, ← complete]
    exact member
  obtain ⟨n, present⟩ := finite_premises_have_a_stage rules (seed : Set G) rows covered
  have stageComplete : stage rules (seed : Set G) n = SetStoreClosure.closure rules seed := by
    apply Set.Subset.antisymm (stage_le_closure rules seed n)
    rw [← complete]
    exact present
  refine ⟨n, (rounds_eq_stage rules (seed : Set G) n).trans stageComplete, ?_⟩
  apply (delta_empty_iff_fixed rules _ (rounds_invariant rules (seed : Set G) n)).mpr
  rw [rounds_eq_stage]
  exact (stage_eq_closure_iff_fixed rules seed n).mp stageComplete

/-! The actual rule syntax supplies the instance family; no finite grounding
table or semantic-adequacy assumption is substituted for it. -/

open Mettapedia.Logic.LP
open OneFrame (Terms)
open SetStoreSyntax (GroundRows Propagates consequence)

variable {signature : LPSignature} [DecidableEq signature.vars]
  [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]
  {P : Program (Terms (Term signature))}

theorem every_run_eq_frontier (slots : signature.vars ≃ Nat) (timing : SetStore.AskTiming)
    (pure : ∀ rule ∈ P, Propagates rule)
    (rules : List (Rule (Terms (Term signature)))) (covers : ∀ rule ∈ P, rule ∈ rules)
    (execution : Nat → Finset (Term signature)) (ground : GroundRows (execution 0))
    (advances : ∀ n, EveryAdvance timing P (execution n) (execution (n + 1))) (n : Nat) :
    (execution n : Set (Term signature)) =
      (rounds (consequence (P := P)) (execution 0 : Set (Term signature)) n).known := by
  exact (every_run_stage slots timing pure rules covers execution ground advances n).2.trans
    (rounds_eq_stage _ _ n).symm

theorem exists_every_frontier_execution (slots : signature.vars ≃ Nat)
    (timing : SetStore.AskTiming) (pure : ∀ rule ∈ P, Propagates rule)
    (rules : List (Rule (Terms (Term signature)))) (covers : ∀ rule ∈ P, rule ∈ rules)
    (seed : Finset (Term signature)) (ground : GroundRows seed) :
    ∃ execution : Nat → Finset (Term signature), execution 0 = seed ∧
      (∀ n, EveryAdvance timing P (execution n) (execution (n + 1))) ∧
      ∀ n, (execution n : Set (Term signature)) =
        (rounds (consequence (P := P)) (seed : Set (Term signature)) n).known := by
  obtain ⟨execution, initial, advances⟩ :=
    exists_every_execution slots timing pure rules covers seed ground
  refine ⟨execution, initial, advances, fun n => ?_⟩
  have same := every_run_eq_frontier slots timing pure rules covers execution
    (initial.symm ▸ ground) advances n
  simpa only [initial] using same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRounds.SemiNaive
