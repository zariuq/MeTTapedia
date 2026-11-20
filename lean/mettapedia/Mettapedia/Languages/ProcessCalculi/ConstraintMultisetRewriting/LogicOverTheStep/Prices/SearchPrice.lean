import Mettapedia.Logic.ModalMuCalculus
import Mettapedia.Logic.ReverseMathematics.Omniscience

/-!
# The price of search: least and greatest fixpoints

A **search system** gives its steps as explicit lists and decides its goals (`SearchSystem`). Read as a
transition system of the modal μ-calculus (`SearchSystem.lts`: action `false` steps, action `true`
loops exactly at goals), it has two fixpoint properties:

* `Reaches`: `μX. goal ∨ ⟨step⟩X`, "the search succeeds", the least fixpoint;
* `Avoids`: `νX. ¬goal ∧ [step]X`, "the search never succeeds", the greatest fixpoint.

On a search system the least fixpoint is reached at a finite stage: `Reaches` holds exactly when a
bounded search (`within`) succeeds at some bound (`reaches_iff`), and `Avoids` holds exactly when every
bounded search fails (`avoids_iff`). So reaching is a Σ⁰₁ property, found by an unbounded search and
certified by the bound at which it succeeds, and avoiding is its negation (`avoids_iff_not_reaches`),
a Π⁰₁ property, refuted at a finite stage and confirmed by none, but certified by a finite invariant
when one exists (`avoids_of_invariant`).

## The prices, exactly

On the systems built from a binary sequence (`chain`: a line of states, with a goal where the
sequence is `true`):

* **Markov's principle** is "a search that cannot fail forever succeeds": `mp_iff_search`;
* **LPO** is "reaching is decided": `lpo_iff_search`;
* **WLPO** is "avoiding is decided": `wlpo_iff_safety`.

The upper bounds hold on every search system (`reaches_of_not_avoids`, `reaches_decided`,
`avoids_decided`), so each equivalence is exact. A property that is reached at a finite stage, found
by an unbounded search, and not decided, is **groundable**: its logical name is Σ⁰₁, and the principle
that lets a checker trust "it cannot fail forever" is Markov's principle. No theorem here uses
`Classical.choice`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.SearchPrice

open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.Logic.ReverseMathematics.Omniscience

universe u

theorem boolCases (b : Bool) : b = false ∨ b = true := by
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem false_of_not_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases b
  · rfl
  · exact absurd rfl h

/-- **A search system**: steps as explicit lists, goals decided. -/
structure SearchSystem (S : Type u) where
  next : S → List S
  goal : S → Bool

namespace SearchSystem

variable {S : Type u} (G : SearchSystem S)

/-- The transition system: action `false` steps, action `true` loops exactly at goals. -/
def lts : LTS S Bool where
  trans s a t := match a with
    | true => t = s ∧ G.goal s = true
    | false => t ∈ G.next s

/-- **Bounded search**: a goal within `n` steps. -/
def within : ℕ → S → Bool
  | 0, s => G.goal s
  | n + 1, s => G.goal s || (G.next s).any (within n)

end SearchSystem

/-- The goal, as a formula at any depth of binders: a goal loop is possible. -/
def goalF {k : ℕ} : Formula Bool k := .diamond true .tt

/-- **The search succeeds**: `μX. goal ∨ ⟨step⟩X`. -/
def reachF : Formula Bool 0 := Formula.eventually false goalF

/-- **The search never succeeds**: `νX. ¬goal ∧ [step]X`. -/
def avoidF : Formula Bool 0 := Formula.always false (.neg goalF)

variable {S : Type u} (G : SearchSystem S)

/-- The least fixpoint, at a state. -/
def Reaches (s : S) : Prop := satisfies G.lts Env.empty reachF s

/-- The greatest fixpoint, at a state. -/
def Avoids (s : S) : Prop := satisfies G.lts Env.empty avoidF s

theorem goal_sat {k : ℕ} (ρ : Env S k) (t : S) :
    satisfies G.lts ρ goalF t ↔ G.goal t = true := by
  constructor
  · rintro ⟨_, ⟨_, isGoal⟩, _⟩
    exact isGoal
  · intro isGoal
    exact ⟨t, ⟨rfl, isGoal⟩, trivial⟩

theorem extend_zero {k : ℕ} (ρ : Env S k) (X : Set S) : ρ.extend X 0 = X := by
  simp [Env.extend]

/-- The body of the least fixpoint. -/
theorem reach_body_iff (X : Set S) (t : S) :
    satisfies G.lts (Env.empty.extend X) (.disj (Formula.weaken goalF) (.diamond false (.var 0))) t ↔
      G.goal t = true ∨ ∃ t' ∈ G.next t, t' ∈ X := by
  have goalPart : satisfies G.lts (Env.empty.extend X) (Formula.weaken goalF) t ↔ G.goal t = true :=
    goal_sat G (Env.empty.extend X) t
  have stepPart : satisfies G.lts (Env.empty.extend X) (.diamond false (.var 0)) t ↔
      ∃ t' ∈ G.next t, t' ∈ X := by
    constructor
    · rintro ⟨t', step, inside⟩
      refine ⟨t', step, ?_⟩
      have there : t' ∈ (Env.empty.extend X) 0 := inside
      rwa [extend_zero] at there
    · rintro ⟨t', step, inside⟩
      refine ⟨t', step, ?_⟩
      show t' ∈ (Env.empty.extend X) 0
      rwa [extend_zero]
  exact or_congr goalPart stepPart

/-- The body of the greatest fixpoint. -/
theorem avoid_body_iff (X : Set S) (t : S) :
    satisfies G.lts (Env.empty.extend X) (.conj (Formula.weaken (.neg goalF)) (.box false (.var 0))) t ↔
      G.goal t = false ∧ ∀ t' ∈ G.next t, t' ∈ X := by
  have goalPart : satisfies G.lts (Env.empty.extend X) (Formula.weaken (.neg goalF)) t ↔
      G.goal t = false := by
    show ¬ satisfies G.lts (Env.empty.extend X) goalF t ↔ G.goal t = false
    rw [goal_sat]
    constructor
    · exact false_of_not_true
    · intro isFalse isTrue
      rw [isFalse] at isTrue
      exact Bool.noConfusion isTrue
  have stepPart : satisfies G.lts (Env.empty.extend X) (.box false (.var 0)) t ↔
      ∀ t' ∈ G.next t, t' ∈ X := by
    constructor
    · intro all t' step
      have there : t' ∈ (Env.empty.extend X) 0 := all t' step
      rwa [extend_zero] at there
    · intro all t' step
      show t' ∈ (Env.empty.extend X) 0
      rw [extend_zero]
      exact all t' step
  exact and_congr goalPart stepPart

theorem within_succ_true {n : ℕ} {s : S} :
    G.within (n + 1) s = true ↔ G.goal s = true ∨ ∃ t ∈ G.next s, G.within n t = true := by
  show (G.goal s || (G.next s).any (G.within n)) = true ↔ _
  rw [Bool.or_eq_true, List.any_eq_true]

/-- **The least fixpoint is reached at a finite stage**: reaching is a bounded search succeeding. -/
theorem reaches_iff (s : S) : Reaches G s ↔ ∃ n, G.within n s = true := by
  constructor
  · intro reaches
    refine reaches {t | ∃ n, G.within n t = true} ?_
    intro t body
    rcases (reach_body_iff G _ t).mp body with isGoal | ⟨t', step, n, found⟩
    · exact ⟨0, isGoal⟩
    · exact ⟨n + 1, (within_succ_true G).mpr (Or.inr ⟨t', step, found⟩)⟩
  · rintro ⟨n, found⟩ X closedX
    induction n generalizing s with
    | zero => exact closedX s ((reach_body_iff G X s).mpr (Or.inl found))
    | succ n ih =>
      rcases (within_succ_true G).mp found with isGoal | ⟨t, step, foundT⟩
      · exact closedX s ((reach_body_iff G X s).mpr (Or.inl isGoal))
      · exact closedX s ((reach_body_iff G X s).mpr (Or.inr ⟨t, step, ih t foundT⟩))

/-- **The greatest fixpoint is every bounded search failing.** -/
theorem avoids_iff (s : S) : Avoids G s ↔ ∀ n, G.within n s = false := by
  constructor
  · rintro ⟨X, member, invariant⟩ n
    induction n generalizing s with
    | zero => exact ((avoid_body_iff G X s).mp (invariant s member)).1
    | succ n ih =>
      obtain ⟨noGoal, closed⟩ := (avoid_body_iff G X s).mp (invariant s member)
      refine false_of_not_true fun found => ?_
      rcases (within_succ_true G).mp found with isGoal | ⟨t, step, foundT⟩
      · rw [noGoal] at isGoal
        exact Bool.noConfusion isGoal
      · rw [ih t (closed t step)] at foundT
        exact Bool.noConfusion foundT
  · intro never
    refine ⟨{t | ∀ n, G.within n t = false}, never, fun t clear => ?_⟩
    refine (avoid_body_iff G _ t).mpr ⟨clear 0, fun t' step n => ?_⟩
    refine false_of_not_true fun found => ?_
    have atT := clear (n + 1)
    rw [(within_succ_true G).mpr (Or.inr ⟨t', step, found⟩)] at atT
    exact Bool.noConfusion atT

/-- **Avoiding is not reaching**, with no principle. -/
theorem avoids_iff_not_reaches (s : S) : Avoids G s ↔ ¬ Reaches G s := by
  rw [avoids_iff, reaches_iff]
  constructor
  · rintro never ⟨n, found⟩
    rw [never n] at found
    exact Bool.noConfusion found
  · intro notFound n
    exact false_of_not_true fun found => notFound ⟨n, found⟩

/-- **A finite invariant certifies avoidance**: a list of states, goal-free and closed under steps. -/
theorem avoids_of_invariant (I : List S)
    (closed : ∀ t ∈ I, G.goal t = false ∧ ∀ t' ∈ G.next t, t' ∈ I) {s : S} (member : s ∈ I) :
    Avoids G s :=
  ⟨{t | t ∈ I}, member, fun t inside => (avoid_body_iff G _ t).mpr (closed t inside)⟩

/-! ## Upper bounds on every search system -/

/-- **Markov's principle: a search that cannot fail forever succeeds**, on every search system. -/
theorem reaches_of_not_avoids (mp : MP) {s : S} (notAvoids : ¬ Avoids G s) : Reaches G s :=
  (reaches_iff G s).mpr (mp (fun n => G.within n s) fun never => notAvoids ((avoids_iff G s).mpr never))

/-- **LPO decides reaching**, on every search system. -/
theorem reaches_decided (lpo : LPO) (s : S) : Reaches G s ∨ ¬ Reaches G s := by
  rcases lpo fun n => G.within n s with found | never
  · exact Or.inl ((reaches_iff G s).mpr found)
  · exact Or.inr ((avoids_iff_not_reaches G s).mp ((avoids_iff G s).mpr never))

/-- **WLPO decides avoiding**, on every search system. -/
theorem avoids_decided (wlpo : WLPO) (s : S) : Avoids G s ∨ ¬ Avoids G s := by
  rcases wlpo fun n => G.within n s with never | notNever
  · exact Or.inl ((avoids_iff G s).mpr never)
  · exact Or.inr fun avoids => notNever ((avoids_iff G s).mp avoids)

/-! ## Systems built from a binary sequence -/

/-- **The chain of a binary sequence**: state `n` steps to `n + 1` and is a goal where `α n = true`. -/
def chain (α : ℕ → Bool) : SearchSystem ℕ := ⟨fun n => [n + 1], α⟩

theorem chain_within_iff (α : ℕ → Bool) :
    ∀ (k n : ℕ), (chain α).within k n = true ↔ ∃ m, n ≤ m ∧ m ≤ n + k ∧ α m = true
  | 0, n => by
      constructor
      · intro found
        exact ⟨n, le_refl n, le_refl n, found⟩
      · rintro ⟨m, low, high, found⟩
        have same : m = n := by omega
        rw [same] at found
        exact found
  | k + 1, n => by
      rw [within_succ_true]
      constructor
      · rintro (found | ⟨t, step, foundT⟩)
        · exact ⟨n, le_refl n, by omega, found⟩
        · have isNext : t = n + 1 := List.mem_singleton.mp step
          rw [isNext] at foundT
          obtain ⟨m, low, high, found⟩ := (chain_within_iff α k (n + 1)).mp foundT
          exact ⟨m, by omega, by omega, found⟩
      · rintro ⟨m, low, high, found⟩
        rcases Nat.lt_or_ge n m with lt | ge
        · exact Or.inr ⟨n + 1, List.mem_singleton.mpr rfl,
            (chain_within_iff α k (n + 1)).mpr ⟨m, lt, by omega, found⟩⟩
        · have same : m = n := by omega
          rw [same] at found
          exact Or.inl found

/-- On a chain, reaching from the first state is a `true` entry. -/
theorem chain_reaches_iff (α : ℕ → Bool) : Reaches (chain α) 0 ↔ ∃ n, α n = true := by
  rw [reaches_iff]
  constructor
  · rintro ⟨k, found⟩
    obtain ⟨m, _, _, hm⟩ := (chain_within_iff α k 0).mp found
    exact ⟨m, hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, (chain_within_iff α m 0).mpr ⟨m, Nat.zero_le m, by omega, hm⟩⟩

/-- On a chain, avoiding from the first state is a constantly `false` sequence. -/
theorem chain_avoids_iff (α : ℕ → Bool) : Avoids (chain α) 0 ↔ ∀ n, α n = false := by
  rw [avoids_iff_not_reaches, chain_reaches_iff]
  constructor
  · intro none n
    exact false_of_not_true fun found => none ⟨n, found⟩
  · rintro all ⟨n, found⟩
    rw [all n] at found
    exact Bool.noConfusion found

/-- **Markov's principle is exactly "a search that cannot fail forever succeeds".** -/
theorem mp_iff_search : MP ↔ ∀ α : ℕ → Bool, ¬ Avoids (chain α) 0 → Reaches (chain α) 0 := by
  constructor
  · intro mp α notAvoids
    exact reaches_of_not_avoids (chain α) mp notAvoids
  · intro search α notAll
    exact (chain_reaches_iff α).mp (search α fun avoids => notAll ((chain_avoids_iff α).mp avoids))

/-- **LPO is exactly "reaching is decided".** -/
theorem lpo_iff_search : LPO ↔ ∀ α : ℕ → Bool, Reaches (chain α) 0 ∨ ¬ Reaches (chain α) 0 := by
  constructor
  · intro lpo α
    exact reaches_decided (chain α) lpo 0
  · intro decided α
    rcases decided α with reaches | notReaches
    · exact Or.inl ((chain_reaches_iff α).mp reaches)
    · exact Or.inr ((chain_avoids_iff α).mp ((avoids_iff_not_reaches (chain α) 0).mpr notReaches))

/-- **WLPO is exactly "avoiding is decided".** -/
theorem wlpo_iff_safety : WLPO ↔ ∀ α : ℕ → Bool, Avoids (chain α) 0 ∨ ¬ Avoids (chain α) 0 := by
  constructor
  · intro wlpo α
    exact avoids_decided (chain α) wlpo 0
  · intro decided α
    rcases decided α with avoids | notAvoids
    · exact Or.inl ((chain_avoids_iff α).mp avoids)
    · exact Or.inr fun all => notAvoids ((chain_avoids_iff α).mpr all)

/-! ## Controls -/

namespace Controls

/-- Positive control: a sequence with a `true` entry is reached, with the witness found by search. -/
theorem reaches_pulse : Reaches (chain fun n => decide (n = 3)) 0 :=
  (chain_reaches_iff _).mpr ⟨3, rfl⟩

/-- Positive control: the zero sequence is avoided. On a chain every state is new, so no finite
invariant certifies it; the proof reads that every bounded search fails. -/
theorem avoids_zero : Avoids (chain fun _ => false) 0 :=
  (chain_avoids_iff _).mpr fun _ => rfl

/-- Negative control: a finite invariant certifies avoidance on a finite loop. -/
theorem avoids_loop : Avoids (⟨fun _ => [()], fun _ => false⟩ : SearchSystem Unit) () :=
  avoids_of_invariant _ [()] (fun _ _ => ⟨rfl, fun t _ => by cases t; exact List.mem_singleton.mpr rfl⟩)
    (List.mem_singleton.mpr rfl)

/-- Negative control: a pulse is not avoided. -/
theorem not_avoids_pulse : ¬ Avoids (chain fun n => decide (n = 3)) 0 :=
  fun avoids => absurd ((chain_avoids_iff _).mp avoids 3) (by decide)

end Controls

#print axioms reaches_iff
#print axioms avoids_iff
#print axioms avoids_iff_not_reaches
#print axioms avoids_of_invariant
#print axioms reaches_of_not_avoids
#print axioms reaches_decided
#print axioms avoids_decided
#print axioms chain_reaches_iff
#print axioms chain_avoids_iff
#print axioms mp_iff_search
#print axioms lpo_iff_search
#print axioms wlpo_iff_safety
#print axioms Controls.reaches_pulse
#print axioms Controls.avoids_loop
#print axioms Controls.not_avoids_pulse

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.SearchPrice
