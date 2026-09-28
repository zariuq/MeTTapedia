import Mettapedia.GSLT.Dynamics.MemoizationObserver
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Card

/-!
# Shared subgoals under proof-size budgets

A backward chainer asks a subgoal under a proof-size budget: the call answers
with checked proofs of the goal whose size fits the budget.  Tabling stores
the proofs found for a subgoal and serves later calls from the store.  This
file states when that reuse is exact, and exhibits a wrong answer for each
condition that fails.

* A stored checked proof of size `s` is a witness for every caller in the same
  context whose budget is at least `s` (`witness_serves`).
* The proofs within budget `b` are the proofs within any larger budget `B`
  restricted to size `b` (`within_restrictive`): the budget-weakening
  property.  A subgoal completed at `B` answers every caller with budget
  `b ≤ B` exactly (`completed_serves`).  Above `B` its proofs are sound but
  may be incomplete (`serve_above_completion_incomplete`), so such a caller
  continues the search.
* An observation that changes with the budget does not inherit the law.  A
  stored "no proof within `B`" answers every smaller budget
  (`noProof_downward`) but not a larger one (`noProof_not_upward`), and a
  proof guarded by a bounded negation is not restrictive
  (`negation_guard_not_restrictive`).
* Reuse keys on the whole context.  Keying on the whole context is sound
  (`context_key_sound`); a key that forgets a hypothesis in scope serves a
  goal proved under the hypothesis to a caller without it
  (`hypothesis_blind_key_wrong`).
* A proof stays checked while its dependencies are present
  (`checks_of_deps`), and removing one invalidates it
  (`removed_dependency_invalidates`).
* The table is a set of proofs: a second derivation of a stored proof adds no
  evidence (`record_again`).  A consumer that counts derivations does not
  factor through the proofs (`derivation_count_unsound`), while one that
  counts distinct proofs does (`evidence_count_sound`).
* An answer with answer-local variables is a scheme.  Two reuses of one scheme
  must be instantiated independently: one shared instantiation yields only the
  diagonal of the joint answers (`shared_instantiation_loses_answers`).
* A chainer that asks premises only at smaller budgets, and answers some of
  them from a table whose entries are its own answers, computes exactly what
  the untabled chainer computes (`tabledChain_eq_chain`).  Entries completed at
  larger budgets are such answers once restricted, for a chainer with the
  budget-weakening property (`restricted_entry_agrees`).  An unfolding that
  asks a premise at its own budget is outside the law
  (`sameBudget_not_budgetLocal`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.BudgetedSubgoalReuse

open Mettapedia.GSLT.Dynamics.MemoizationObserver

universe uC uG uP uF

/-! ## Budgeted proofs -/

/-- Checked proofs of goals in contexts, each with a size. -/
structure ProofSystem (Ctx : Type uC) (Goal : Type uG) (Proof : Type uP) where
  checks : Ctx → Proof → Goal → Prop
  size : Proof → ℕ

namespace ProofSystem

variable {Ctx : Type uC} {Goal : Type uG} {Proof : Type uP}
variable (S : ProofSystem Ctx Goal Proof)

/-- The checked proofs of `g` in `c` of size at most `b`: what a complete
search of the subgoal under budget `b` answers. -/
def within (c : Ctx) (g : Goal) (b : ℕ) : Set Proof :=
  {p | S.checks c p g ∧ S.size p ≤ b}

theorem within_mono {c : Ctx} {g : Goal} {b B : ℕ} (h : b ≤ B) :
    S.within c g b ⊆ S.within c g B :=
  fun _ hp => ⟨hp.1, hp.2.trans h⟩

/-- An observation indexed by the budget is restrictive when its value at a
smaller budget is its value at a larger one restricted to that size. -/
def Restrictive (O : ℕ → Set Proof) : Prop :=
  ∀ b B, b ≤ B → O b = O B ∩ {p | S.size p ≤ b}

/-- Budget weakening for checked proofs: the proofs within `b` are the proofs
within `B ≥ b` of size at most `b`. -/
theorem within_restrictive (c : Ctx) (g : Goal) :
    S.Restrictive (S.within c g) := by
  intro b B hbB
  ext p
  constructor
  · intro hp
    exact ⟨⟨hp.1, hp.2.trans hbB⟩, hp.2⟩
  · intro hp
    exact ⟨hp.1.1, hp.2⟩

/-- A restrictive observation computed at `B` serves every smaller budget
exactly by restriction. -/
theorem restrictive_serves {O : ℕ → Set Proof} (hO : S.Restrictive O)
    {b B : ℕ} (hbB : b ≤ B) :
    O B ∩ {p | S.size p ≤ b} = O b :=
  (hO b B hbB).symm

end ProofSystem

/-! ## Table entries -/

/-- A table entry for a subgoal: its context and goal, the proofs found, and
the budget up to which the entry holds every proof, once the subgoal has
completed. -/
structure Entry (Ctx : Type uC) (Goal : Type uG) (Proof : Type uP) where
  ctx : Ctx
  goal : Goal
  proofs : Set Proof
  completedAt : Option ℕ

namespace Entry

variable {Ctx : Type uC} {Goal : Type uG} {Proof : Type uP}
variable (S : ProofSystem Ctx Goal Proof) (e : Entry Ctx Goal Proof)

/-- Every stored proof checks for the entry's goal in its context. -/
def Sound : Prop :=
  ∀ p ∈ e.proofs, S.checks e.ctx p e.goal

/-- A completed entry holds every proof within its completion budget. -/
def Complete : Prop :=
  ∀ B, e.completedAt = some B → S.within e.ctx e.goal B ⊆ e.proofs

/-- The stored proofs a caller with budget `b` may take. -/
def serve (b : ℕ) : Set Proof :=
  {p | p ∈ e.proofs ∧ S.size p ≤ b}

variable {S e}

/-- A stored proof that fits the caller's budget is an answer of the caller's
own search. -/
theorem witness_serves (hs : e.Sound S) {b : ℕ} {p : Proof}
    (hp : p ∈ e.serve S b) : p ∈ S.within e.ctx e.goal b :=
  ⟨hs p hp.1, hp.2⟩

/-- Whatever an entry serves is sound, at any budget. -/
theorem serve_subset (hs : e.Sound S) (b : ℕ) :
    e.serve S b ⊆ S.within e.ctx e.goal b :=
  fun _ hp => witness_serves hs hp

/-- A subgoal completed at `B` answers every caller with budget `b ≤ B`
exactly. -/
theorem completed_serves (hs : e.Sound S) (hc : e.Complete S) {B b : ℕ}
    (hB : e.completedAt = some B) (hbB : b ≤ B) :
    e.serve S b = S.within e.ctx e.goal b := by
  apply Set.Subset.antisymm (serve_subset hs b)
  intro p hp
  exact ⟨hc B hB (S.within_mono hbB hp), hp.2⟩

end Entry

/-! ### A caller above the completion budget -/

/-- Every natural number is a proof of the single goal, of its own size. -/
def natProofs : ProofSystem Unit Unit ℕ where
  checks := fun _ _ _ => True
  size := id

/-- The subgoal completed at budget 1: it holds the proofs 0 and 1. -/
def completedAtOne : Entry Unit Unit ℕ where
  ctx := ()
  goal := ()
  proofs := {p | p ≤ 1}
  completedAt := some 1

theorem completedAtOne_sound : completedAtOne.Sound natProofs :=
  fun _ _ => trivial

theorem completedAtOne_complete : completedAtOne.Complete natProofs := by
  intro B hB p hp
  simp only [completedAtOne, Option.some.injEq] at hB
  subst hB
  exact hp.2

/-- A caller with budget 2 is not answered completely by the subgoal
completed at 1: the proof of size 2 is missing, so that caller continues the
search. -/
theorem serve_above_completion_incomplete :
    completedAtOne.serve natProofs 2 ≠ natProofs.within () () 2 := by
  intro h
  have h2 : (2 : ℕ) ∈ natProofs.within () () 2 := ⟨trivial, le_refl 2⟩
  rw [← h] at h2
  have hle : (2 : ℕ) ≤ 1 := h2.1
  omega

/-! ## Observations that change with the budget -/

namespace ProofSystem

variable {Ctx : Type uC} {Goal : Type uG} {Proof : Type uP}
variable (S : ProofSystem Ctx Goal Proof)

/-- The observation behind a bounded negation: no proof within `b`. -/
def NoProofWithin (c : Ctx) (g : Goal) (b : ℕ) : Prop :=
  S.within c g b = ∅

variable {S}

/-- A stored negative answer serves every smaller budget. -/
theorem noProof_downward {c : Ctx} {g : Goal} {b B : ℕ} (hbB : b ≤ B)
    (h : S.NoProofWithin c g B) : S.NoProofWithin c g b :=
  Set.subset_eq_empty (S.within_mono hbB) h

end ProofSystem

/-- The single proof 3, of size 3. -/
def onlyThree : ProofSystem Unit Unit ℕ where
  checks := fun _ p _ => p = 3
  size := id

/-- A negative answer computed at budget 2 is wrong at budget 3. -/
theorem noProof_not_upward :
    onlyThree.NoProofWithin () () 2 ∧ ¬ onlyThree.NoProofWithin () () 3 := by
  constructor
  · ext p
    refine ⟨fun hp => ?_, fun hp => hp.elim⟩
    have h3 : p = 3 := hp.1
    have h2 : p ≤ 2 := hp.2
    omega
  · intro h
    have h3 : (3 : ℕ) ∈ onlyThree.within () () 3 := ⟨rfl, le_refl 3⟩
    rw [h] at h3
    exact h3

/-- Two goals: `false` has the single proof 0, and `true` the single proof 3.
The first stands for a rule's conclusion, the second for the goal its
bounded negation tests. -/
def guardedProofs : ProofSystem Unit Bool ℕ where
  checks := fun _ p g => if g then p = 3 else p = 0
  size := id

/-- The proofs of the conclusion that a rule with a bounded negation admits:
present only while the negated goal has no proof within the same budget. -/
def negationGuarded (b : ℕ) : Set ℕ :=
  {p | guardedProofs.NoProofWithin () true b ∧ p ∈ guardedProofs.within () false b}

/-- A proof guarded by a bounded negation is not restrictive: the conclusion's
proof 0 is admitted at budget 2 and withdrawn at budget 3, once the negated
goal gains a proof. -/
theorem negation_guard_not_restrictive :
    ¬ guardedProofs.Restrictive negationGuarded := by
  intro h
  have hno2 : guardedProofs.NoProofWithin () true 2 := by
    ext p
    refine ⟨fun hp => ?_, fun hp => hp.elim⟩
    have h3 : p = 3 := hp.1
    have h2 : p ≤ 2 := hp.2
    omega
  have hyes3 : ¬ guardedProofs.NoProofWithin () true 3 := by
    intro h3
    have hmem : (3 : ℕ) ∈ guardedProofs.within () true 3 := ⟨rfl, le_refl 3⟩
    rw [h3] at hmem
    exact hmem
  have h0 : (0 : ℕ) ∈ negationGuarded 2 :=
    ⟨hno2, ⟨rfl, Nat.zero_le 2⟩⟩
  rw [h 2 3 (by decide)] at h0
  exact hyes3 h0.1.1

/-! ## Reuse keys on the whole context -/

section Keys

variable {Ctx : Type uC} {Goal : Type uG} {Proof : Type uP}

/-- Keying reuse on the whole context and goal is sound for the answers at
any budget. -/
theorem context_key_sound (S : ProofSystem Ctx Goal Proof) (b : ℕ) :
    SoundKey (fun x : Ctx × Goal => x) (fun x => S.within x.1 x.2 b) :=
  fun x y (h : x = y) => by subst h; rfl

end Keys

/-- A context of a program version and one hypothesis in scope; the goal is
provable exactly under the hypothesis. -/
def hypothetical : ProofSystem (Unit × Bool) Unit Unit where
  checks := fun c _ _ => c.2 = true
  size := fun _ => 0

/-- A key that keeps the program version and the goal but forgets the
hypothesis. -/
def hypothesisBlindKey (x : (Unit × Bool) × Unit) : Unit × Unit :=
  (x.1.1, x.2)

theorem hypothesisBlindKey_unsound :
    ¬ SoundKey hypothesisBlindKey (fun x => hypothetical.within x.1 x.2 0) := by
  intro h
  have heq : hypothetical.within ((), true) () 0 =
      hypothetical.within ((), false) () 0 :=
    h (((), true), ()) (((), false), ()) rfl
  have hmem : () ∈ hypothetical.within ((), true) () 0 := ⟨rfl, le_refl 0⟩
  rw [heq] at hmem
  exact Bool.noConfusion hmem.1

/-- The hypothesis-blind key serves a goal proved under the hypothesis to a
caller without it. -/
theorem hypothesis_blind_key_wrong :
    ∃ x y,
      lookupOrCompute hypothesisBlindKey (fun x => hypothetical.within x.1 x.2 0)
          (store hypothesisBlindKey (fun x => hypothetical.within x.1 x.2 0)
            Table.empty x) y ≠
        hypothetical.within y.1 y.2 0 :=
  exists_wrong_answer_of_not_soundKey hypothesisBlindKey_unsound

/-! ## Dependencies -/

/-- A proof system over sets of facts in which a proof checks exactly when its
dependencies are present and its own inferences are correct. -/
structure LocalProofSystem (Fact : Type uF) (Goal : Type uG) (Proof : Type uP)
    extends ProofSystem (Set Fact) Goal Proof where
  deps : Proof → Set Fact
  core : Proof → Goal → Prop
  checks_iff : ∀ c p g, checks c p g ↔ deps p ⊆ c ∧ core p g

namespace LocalProofSystem

variable {Fact : Type uF} {Goal : Type uG} {Proof : Type uP}
variable (S : LocalProofSystem Fact Goal Proof)

/-- A stored proof still checks in any context that holds its
dependencies. -/
theorem checks_of_deps {c c' : Set Fact} {p : Proof} {g : Goal}
    (h : S.checks c p g) (hd : S.deps p ⊆ c') : S.checks c' p g :=
  (S.checks_iff c' p g).2 ⟨hd, ((S.checks_iff c p g).1 h).2⟩

/-- Removing one of a proof's dependencies invalidates it. -/
theorem removed_dependency_invalidates {c : Set Fact} {p : Proof} {g : Goal}
    {f : Fact} (hf : f ∈ S.deps p) : ¬ S.checks (c \ {f}) p g := by
  intro h
  have hsub := ((S.checks_iff _ p g).1 h).1 hf
  exact hsub.2 rfl

end LocalProofSystem

/-! ## Evidence is the set of proofs -/

section Evidence

variable {Proof : Type uP}

/-- Recording a proof in the table. -/
def record (table : Set Proof) (p : Proof) : Set Proof := insert p table

/-- A second derivation of a stored proof adds no evidence. -/
theorem record_again (table : Set Proof) (p : Proof) :
    record (record table p) p = record table p :=
  Set.insert_eq_of_mem (Set.mem_insert p table)

variable [DecidableEq Proof]

/-- Counting distinct proofs factors through the evidence: derivation lists
with the same proofs count the same. -/
theorem evidence_count_sound :
    SoundKey (fun l : List Proof => l.toFinset) (fun l => l.toFinset.card) :=
  fun x y (h : x.toFinset = y.toFinset) => by
    show x.toFinset.card = y.toFinset.card
    rw [h]

/-- Counting derivations does not factor through the evidence: deriving one
proof twice doubles the count without adding evidence. -/
theorem derivation_count_unsound (p : Proof) :
    ¬ SoundKey (fun l : List Proof => l.toFinset) List.length := by
  intro h
  have := h [p] [p, p] (by simp)
  simp at this

end Evidence

/-! ## Answer-local variables -/

section Schemes

variable {Inst : Type uF} {Answer : Type uP}

/-- The joint answers of two independent reuses of the scheme `σ`, which
instantiates its answer-local variables by `Inst`. -/
def independentReuses (σ : Inst → Answer) : Set (Answer × Answer) :=
  {q | ∃ v w, q = (σ v, σ w)}

/-- The joint answers when both reuses share one instantiation. -/
def sharedReuses (σ : Inst → Answer) : Set (Answer × Answer) :=
  {q | ∃ v, q = (σ v, σ v)}

theorem shared_subset_independent (σ : Inst → Answer) :
    sharedReuses σ ⊆ independentReuses σ :=
  fun _ ⟨v, hv⟩ => ⟨v, v, hv⟩

/-- Sharing one instantiation between two reuses loses every pair of distinct
instances. -/
theorem shared_instantiation_loses_answers (σ : Inst → Answer) {v w : Inst}
    (hvw : σ v ≠ σ w) :
    (σ v, σ w) ∈ independentReuses σ ∧ (σ v, σ w) ∉ sharedReuses σ := by
  refine ⟨⟨v, w, rfl⟩, ?_⟩
  rintro ⟨u, hu⟩
  simp only [Prod.mk.injEq] at hu
  exact hvw (hu.1.trans hu.2.symm)

end Schemes

/-! ## Tabled chaining equals the search

A backward chainer unfolds a goal at a budget into rule applications whose
premises it asks at the budgets left over.  When every rule application costs
at least one, the premises are asked only at strictly smaller budgets.  Then a
chainer that answers some premises from a table, and searches the others,
computes exactly what the untabled chainer computes, provided every table
entry is the chainer's answer at its own goal and budget.  For an observation
with the budget-weakening property, an entry completed at a larger budget
gives that answer by restriction (`restricted_entry_agrees`). -/

section Chaining

variable {Goal : Type uG} {Proof : Type uP}

/-- One unfolding of a budgeted chainer: the proofs of a goal within a budget,
given how its premises are answered. -/
abbrev Unfolding (Goal : Type uG) (Proof : Type uP) :=
  (Goal → ℕ → Set Proof) → Goal → ℕ → Set Proof

/-- The unfolding asks premises only at budgets below its own: every rule
application costs at least one. -/
def BudgetLocal (F : Unfolding Goal Proof) : Prop :=
  ∀ (O O' : Goal → ℕ → Set Proof) (g : Goal) (b : ℕ),
    (∀ g' b', b' < b → O g' b' = O' g' b') → F O g b = F O' g b

/-- The chainer, premises searched at their smaller budgets. -/
def chain (F : Unfolding Goal Proof) (g : Goal) (b : ℕ) : Set Proof :=
  F (fun g' b' => if _ : b' < b then chain F g' b' else ∅) g b
termination_by b

/-- Every entry of the table is the chainer's answer at its goal and budget. -/
def TableAgrees (F : Unfolding Goal Proof) (T : Goal → ℕ → Option (Set Proof)) :
    Prop :=
  ∀ g b s, T g b = some s → s = chain F g b

/-- The tabled chainer: a premise with an entry is answered from the table,
any other is searched. -/
def tabledChain (F : Unfolding Goal Proof) (T : Goal → ℕ → Option (Set Proof))
    (g : Goal) (b : ℕ) : Set Proof :=
  F (fun g' b' => if _ : b' < b then (T g' b').getD (tabledChain F T g' b') else ∅) g b
termination_by b

theorem tabledChain_eq_chain {F : Unfolding Goal Proof}
    {T : Goal → ℕ → Option (Set Proof)} (hF : BudgetLocal F)
    (hT : TableAgrees F T) (b : ℕ) (g : Goal) :
    tabledChain F T g b = chain F g b := by
  induction b using Nat.strong_induction_on generalizing g with
  | _ b ih =>
    rw [tabledChain, chain]
    apply hF
    intro g' b' hb'
    simp only [dif_pos hb']
    cases hTg : T g' b' with
    | none => simp only [Option.getD_none]; exact ih b' hb' g'
    | some s => simp only [Option.getD_some]; exact hT g' b' s hTg

/-- A table built from entries completed at larger budgets agrees with the
chainer when the chainer's answers have the budget-weakening property. -/
theorem restricted_entry_agrees {F : Unfolding Goal Proof} (size : Proof → ℕ)
    (hrestrict : ∀ g b B, b ≤ B →
      chain F g b = chain F g B ∩ {p | size p ≤ b})
    (completed : Goal → Option ℕ)
    (T : Goal → ℕ → Option (Set Proof))
    (hT : ∀ g b s, T g b = some s →
      ∃ B, completed g = some B ∧ b ≤ B ∧ s = chain F g B ∩ {p | size p ≤ b}) :
    TableAgrees F T := by
  intro g b s hs
  obtain ⟨B, _, hbB, rfl⟩ := hT g b s hs
  exact (hrestrict g b B hbB).symm

/-- A chainer whose one rule extends a proof of the goal by one step: at budget
`b + 1` the proofs are `0` and the successors of the proofs at `b`. -/
def successorUnfolding : Unfolding Unit ℕ := fun O _ b =>
  match b with
  | 0 => ∅
  | b + 1 => insert 0 (Nat.succ '' O () b)

theorem successorUnfolding_budgetLocal : BudgetLocal successorUnfolding := by
  intro O O' g b h
  cases b with
  | zero => rfl
  | succ b =>
    show insert 0 (Nat.succ '' O () b) = insert 0 (Nat.succ '' O' () b)
    rw [h () b (Nat.lt_succ_self b)]

/-- The empty table agrees with every chainer, so the tabled chainer with no
entries is the chainer itself. -/
theorem emptyTable_agrees (F : Unfolding Goal Proof) :
    TableAgrees F (fun _ _ => none) := by
  intro g b s h
  cases h

theorem successor_tabled_empty (b : ℕ) :
    tabledChain successorUnfolding (fun _ _ => none) () b =
      chain successorUnfolding () b :=
  tabledChain_eq_chain successorUnfolding_budgetLocal
    (emptyTable_agrees successorUnfolding) b ()

/-- An unfolding that asks its premise at its own budget is not budget-local:
its value at a budget depends on the answer at that same budget. -/
theorem sameBudget_not_budgetLocal :
    ¬ BudgetLocal (fun (O : Unit → ℕ → Set ℕ) (g : Unit) (b : ℕ) => O g b) := by
  intro h
  have heq : (∅ : Set ℕ) = Set.univ :=
    h (fun _ _ => ∅) (fun _ _ => Set.univ) () 0
      (fun _ b' hb' => absurd hb' (Nat.not_lt_zero b'))
  have hmem : (0 : ℕ) ∈ (Set.univ : Set ℕ) := Set.mem_univ 0
  rw [← heq] at hmem
  exact hmem

/-- nuPLN's two-premise rule shape: from budget `b ≥ 3`, the first premise is
asked at `b - 2`, and the second at the budget its first proof leaves,
`b - (size x + 1)`; the pair costs one more than its parts. -/
def threadedPair (size : Proof → ℕ) (pair : Proof → Proof → Proof)
    (first second : Goal) (O : Goal → ℕ → Set Proof) (b : ℕ) : Set Proof :=
  {p | 3 ≤ b ∧ ∃ x y, x ∈ O first (b - 2) ∧ y ∈ O second (b - (size x + 1)) ∧
    p = pair x y}

/-- Threading the leftover budget keeps every premise below the rule's own
budget, so a chainer built from such rules is budget-local. -/
theorem threadedPair_budgetLocal (size : Proof → ℕ) (pair : Proof → Proof → Proof)
    (first second : Goal) (O O' : Goal → ℕ → Set Proof) (b : ℕ)
    (h : ∀ g' b', b' < b → O g' b' = O' g' b') :
    threadedPair size pair first second O b = threadedPair size pair first second O' b := by
  ext p
  simp only [threadedPair]
  constructor
  · rintro ⟨hb, x, y, hx, hy, rfl⟩
    refine ⟨hb, x, y, ?_, ?_, rfl⟩
    · rw [← h first (b - 2) (by omega)]; exact hx
    · rw [← h second (b - (size x + 1)) (by omega)]; exact hy
  · rintro ⟨hb, x, y, hx, hy, rfl⟩
    refine ⟨hb, x, y, ?_, ?_, rfl⟩
    · rw [h first (b - 2) (by omega)]; exact hx
    · rw [h second (b - (size x + 1)) (by omega)]; exact hy

end Chaining

end Mettapedia.GSLT.Dynamics.BudgetedSubgoalReuse
