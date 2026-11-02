import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.BorrowedSteps

/-!
# Two ways rho programs fail to come to rest

## A persistent send meeting a persistent receive

`c!!(m) | for (x <= c) { d!(x) }` keeps both the message and the receiver at every COMM, so the
same match fires again and again. Read as a bag rule that keeps two atoms and makes one output,
every reachable configuration can step, and after `k` steps there are `k` outputs
(`persistent_never_rests`, `persistent_outputs`). Datalog and CHR fire a rule once per match.
Doing that in the step language needs a predicate query on the rule's own output, a part rho
lacks: the guarded rule fires once and rests (`oncePerMatch_rests`).

## A guard checked after taking

Rholang's patterns are linear: a variable may not occur in two binds of one join, and a join may
not take twice from one channel (`UnexpectedReuseOfNameContextFree`, `ReceiveOnSameChannelsError`
in both reference normalizers). So "two edges that chain" cannot be a pattern; a program takes two
edges, compares them, and sends them back when they do not chain. On a graph with no chain that
program steps forever (`checkAfterTake_never_rests`), while the pattern with a shared variable
rests at once (`pattern_rests`). Both show the same barbs: no path ever appears
(`checkAfterTake_no_path`). The difference is only in coming to rest. Rholang-rs's `where` guards
(2026) check before taking, which removes this failure for guards over the received values.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Weaknesses.Saturation

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence (Rule Reduces)

/-- Nothing can step. -/
def Stuck {A : Type} [DecidableEq A] (Γ : Rule A → Prop) (M : Multiset A) : Prop :=
  ∀ M', ¬ Reduces Γ M M'

/-! ## Persistent send, persistent receive -/

/-- A persistent message, a persistent receiver, and what each COMM makes. -/
inductive Fact where
  | pmsg | prcv | out
  deriving DecidableEq

/-- `c!!(m) | for (x <= c) { d!(x) }`: keep both, make one output. -/
def persistentComm : Rule Fact := ⟨0, {.pmsg, .prcv}, {.out}, fun _ => false⟩

def Persistent (ρ : Rule Fact) : Prop := ρ = persistentComm

/-- The program. -/
def program : Multiset Fact := {.pmsg, .prcv}

/-- The program after `k` COMMs. -/
def after (k : ℕ) : Multiset Fact := program + Multiset.replicate k .out

theorem after_succ (k : ℕ) : after (k + 1) = after k + {Fact.out} := by
  rw [after, after, Multiset.replicate_succ, Multiset.add_cons, add_comm _ ({Fact.out} : Multiset Fact),
    Multiset.singleton_add]

theorem after_step (k : ℕ) : Reduces Persistent (after k) (after (k + 1)) := by
  refine ⟨persistentComm, rfl, ⟨?_, fun _ _ => rfl⟩, ?_⟩
  · simp [persistentComm, Rule.redex, after, program]
  · rw [after_succ]
    simp [Rule.result, persistentComm]

/-- **After `k` COMMs there are `k` outputs.** -/
theorem persistent_outputs (k : ℕ) :
    Relation.ReflTransGen (Reduces Persistent) program (after k) ∧ (after k).count .out = k := by
  refine ⟨?_, by simp [after, program]⟩
  induction k with
  | zero => simpa [after] using Relation.ReflTransGen.refl
  | succ k ih => exact ih.tail (after_step k)

/-- **The program never comes to rest**: every configuration it reaches can step. -/
theorem persistent_never_rests {M : Multiset Fact}
    (run : Relation.ReflTransGen (Reduces Persistent) program M) : ¬ Stuck Persistent M := by
  have kept : program ≤ M := by
    induction run with
    | refl => exact le_rfl
    | tail _ last ih =>
      obtain ⟨ρ, rfl, _, rfl⟩ := last
      simp only [Rule.result, persistentComm, tsub_zero]
      exact ih.trans (Multiset.le_add_right _ _)
  intro stuck
  exact stuck _ ⟨persistentComm, rfl, ⟨by simpa [persistentComm, Rule.redex, program] using kept,
    fun _ _ => rfl⟩, rfl⟩

/-- The same COMM guarded by a predicate query on its own output: fire once per match. -/
def oncePerMatch : Rule Fact := ⟨0, {.pmsg, .prcv}, {.out}, fun a => decide (a = .out)⟩

/-- **Once per match rests after one step.** -/
theorem oncePerMatch_rests :
    Reduces (· = oncePerMatch) program (program + {.out}) ∧
      Stuck (· = oncePerMatch) (program + {.out}) := by
  refine ⟨⟨oncePerMatch, rfl, ⟨by decide, by decide⟩, by decide⟩, ?_⟩
  rintro M' ⟨ρ, rfl, ⟨_, avoids⟩, _⟩
  exact absurd (avoids .out (by decide)) (by decide)

/-! ## A guard checked after taking -/

/-- Edges and paths of a graph. -/
inductive Graph where
  | edge (i j : ℕ)
  | path (i j : ℕ)
  deriving DecidableEq

/-- The pattern with a shared variable: two edges that chain. -/
def chain (x y z : ℕ) : Rule Graph :=
  ⟨{.edge x y, .edge y z}, 0, {.path x z}, fun _ => false⟩

def Pattern (ρ : Rule Graph) : Prop := ∃ x y z, ρ = chain x y z

/-- Take any two edges; if they chain make the path, otherwise send them back. -/
def takeTwo (x y y' z : ℕ) : Rule Graph :=
  if y = y' then ⟨{.edge x y, .edge y' z}, 0, {.path x z}, fun _ => false⟩
  else ⟨{.edge x y, .edge y' z}, 0, {.edge x y, .edge y' z}, fun _ => false⟩

def CheckAfterTake (ρ : Rule Graph) : Prop := ∃ x y y' z, ρ = takeTwo x y y' z

/-- Two edges that do not chain. -/
def graph : Multiset Graph := {.edge 1 2, .edge 3 4}

theorem two_edges_of_le {x y y' z : ℕ} (le : ({.edge x y, .edge y' z} : Multiset Graph) ≤ graph) :
    (x = 1 ∧ y = 2 ∧ y' = 3 ∧ z = 4) ∨ (x = 3 ∧ y = 4 ∧ y' = 1 ∧ z = 2) := by
  have m1 : Graph.edge x y ∈ graph := Multiset.mem_of_le le (by simp)
  have m2 : Graph.edge y' z ∈ graph := Multiset.mem_of_le le (by simp)
  simp only [graph, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton,
    Graph.edge.injEq] at m1 m2
  rcases m1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases m2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd le (by decide)
  · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl, rfl, rfl⟩
  · exact absurd le (by decide)

/-- **The pattern rests at once**: no two edges chain. -/
theorem pattern_rests : Stuck Pattern graph := by
  rintro M' ⟨ρ, ⟨x, y, z, rfl⟩, ⟨le, _⟩, _⟩
  have le' : ({.edge x y, .edge y z} : Multiset Graph) ≤ graph := by
    simpa [chain, Rule.redex] using le
  rcases two_edges_of_le le' with ⟨_, rfl, h, _⟩ | ⟨_, rfl, h, _⟩ <;> omega

/-- Every step of the check-after-take program from the graph returns the graph. -/
theorem checkAfterTake_step {M' : Multiset Graph} (h : Reduces CheckAfterTake graph M') :
    M' = graph := by
  obtain ⟨ρ, ⟨x, y, y', z, rfl⟩, ⟨le, _⟩, rfl⟩ := h
  have le' : ({.edge x y, .edge y' z} : Multiset Graph) ≤ graph := by
    unfold takeTwo at le
    split_ifs at le <;> simpa [Rule.redex] using le
  rcases two_edges_of_le le' with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> decide

/-- **The check-after-take program never comes to rest**: it only ever returns to the graph,
and from the graph it can always step. -/
theorem checkAfterTake_never_rests {M : Multiset Graph}
    (run : Relation.ReflTransGen (Reduces CheckAfterTake) graph M) :
    M = graph ∧ ¬ Stuck CheckAfterTake M := by
  have back : M = graph := by
    induction run with
    | refl => rfl
    | tail _ last ih =>
      subst ih
      exact checkAfterTake_step last
  refine ⟨back, fun stuck => stuck graph ⟨takeTwo 1 2 3 4, ⟨1, 2, 3, 4, rfl⟩, ?_, ?_⟩⟩
  · subst back
    exact ⟨by decide, fun _ _ => rfl⟩
  · subst back
    decide

/-- **Neither program ever shows a path**: they differ only in coming to rest. -/
theorem checkAfterTake_no_path {M : Multiset Graph}
    (run : Relation.ReflTransGen (Reduces CheckAfterTake) graph M) (i j : ℕ) :
    Graph.path i j ∉ M := by
  rw [(checkAfterTake_never_rests run).1]
  simp [graph]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Weaknesses.Saturation
