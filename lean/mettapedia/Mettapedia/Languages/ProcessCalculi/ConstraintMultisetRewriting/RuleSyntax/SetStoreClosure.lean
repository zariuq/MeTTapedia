import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStore
import Mettapedia.GSLT.OpenEnded.ChaoticIteration

/-!
# Positive propagation in a set store

Each instance has finite read premises and finite conclusions. The rule-syntax
adapter supplies these from ground instances of range-restricted rules.
Here no premise is consumed and no matching operation refines an existing
unknown. Only changes are steps. A terminal reachable set is the least
closure; its existence and termination require a finite closed carrier.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreClosure

open Mettapedia.GSLT.OpenEnded

universe u v

structure Instance (G : Type u) where
  read : Finset G
  made : Finset G

variable {G : Type u} {I : Type v} [DecidableEq G]

def action (r : Instance G) : Set G →o Set G where
  toFun rows := {value | (r.read : Set G) ⊆ rows ∧ value ∈ r.made}
  monotone' _ _ included _ value := ⟨value.1.trans included, value.2⟩

def closure (rules : I → Instance G) (seed : Finset G) : Set G :=
  ChaoticIteration.target (fun i => action (rules i)) (seed : Set G)

def Closed (rules : I → Instance G) (rows : Finset G) : Prop :=
  ∀ i, (rules i).read ⊆ rows → (rules i).made ⊆ rows

def Step (rules : I → Instance G) (rows after : Finset G) : Prop :=
  ∃ i, (rules i).read ⊆ rows ∧ after = SetStore.update id rows ∅ (rules i).made ∧ after ≠ rows

def Terminal (rules : I → Instance G) (rows : Finset G) : Prop :=
  ∀ after, ¬ Step rules rows after

theorem step_subset {rules : I → Instance G} {rows after : Finset G}
    (step : Step rules rows after) : rows ⊆ after := by
  obtain ⟨i, _, rfl, _⟩ := step
  simp [SetStore.update]

theorem step_card_lt {rules : I → Instance G} {rows after : Finset G}
    (step : Step rules rows after) : rows.card < after.card := by
  have subset := step_subset step
  obtain ⟨_, _, _, different⟩ := step
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨subset, different.symm⟩)

theorem terminal_iff_closed (rules : I → Instance G) (rows : Finset G) :
    Terminal rules rows ↔ Closed rules rows := by
  constructor
  · intro terminal i enabled
    have unchanged : SetStore.update id rows ∅ (rules i).made = rows := by
      by_contra different
      exact terminal _ ⟨i, enabled, rfl, different⟩
    simpa only [SetStore.update, Finset.sdiff_empty, Finset.image_id, Finset.union_eq_left] using unchanged
  · intro closed after ⟨i, enabled, result, progress⟩
    exact progress (result.trans (SetStore.update_known rows _ (closed i enabled)))

omit [DecidableEq G] in
theorem closed_action_iff (rules : I → Instance G) (rows : Finset G) :
    Closed rules rows ↔ ∀ i, action (rules i) (rows : Set G) ⊆ (rows : Set G) := by
  constructor
  · intro closed i value ⟨enabled, member⟩
    exact closed i enabled member
  · intro closed i enabled value member
    exact closed i ⟨enabled, member⟩

omit [DecidableEq G] in
theorem seed_subset_closure (rules : I → Instance G) (seed : Finset G) :
    (seed : Set G) ⊆ closure rules seed :=
  (ChaoticIteration.isLeast_target (fun i => action (rules i)) (seed : Set G)).1.1

omit [DecidableEq G] in
theorem closure_closed (rules : I → Instance G) (seed : Finset G) (i : I) :
    action (rules i) (closure rules seed) ⊆ closure rules seed :=
  (ChaoticIteration.isLeast_target (fun i => action (rules i)) (seed : Set G)).1.2 i

theorem step_le_closure (rules : I → Instance G) (seed : Finset G) {rows after : Finset G}
    (inside : (rows : Set G) ⊆ closure rules seed) (step : Step rules rows after) :
    (after : Set G) ⊆ closure rules seed := by
  obtain ⟨i, enabled, rfl, _⟩ := step
  simp only [SetStore.update, Finset.sdiff_empty, Finset.image_id, Finset.coe_union]
  intro value member
  rcases member with old | made
  · exact inside old
  · exact closure_closed rules seed i ⟨fun _ member => inside (enabled member), made⟩

theorem reachable_le_closure (rules : I → Instance G) (seed : Finset G) {rows : Finset G}
    (run : Relation.ReflTransGen (Step rules) seed rows) : (rows : Set G) ⊆ closure rules seed := by
  induction run with
  | refl => exact seed_subset_closure rules seed
  | tail _ step ih => exact step_le_closure rules seed ih step

theorem reachable_contains_seed {rules : I → Instance G} {seed rows : Finset G}
    (run : Relation.ReflTransGen (Step rules) seed rows) : seed ⊆ rows := by
  induction run with
  | refl => exact Finset.Subset.refl _
  | tail _ step ih => exact ih.trans (step_subset step)

/-- No termination premise is hidden in uniqueness of an outcome that exists. -/
theorem terminal_eq_closure (rules : I → Instance G) (seed : Finset G) {rows : Finset G}
    (run : Relation.ReflTransGen (Step rules) seed rows) (terminal : Terminal rules rows) :
    (rows : Set G) = closure rules seed := by
  apply Set.Subset.antisymm (reachable_le_closure rules seed run)
  exact (ChaoticIteration.isLeast_target (fun i => action (rules i)) (seed : Set G)).2
    ⟨reachable_contains_seed run, (closed_action_iff rules rows).mp ((terminal_iff_closed rules rows).mp terminal)⟩

theorem terminal_unique (rules : I → Instance G) (seed : Finset G) {first second : Finset G}
    (firstRun : Relation.ReflTransGen (Step rules) seed first) (firstEnd : Terminal rules first)
    (secondRun : Relation.ReflTransGen (Step rules) seed second) (secondEnd : Terminal rules second) :
    first = second := by
  apply Finset.coe_injective
  exact (terminal_eq_closure rules seed firstRun firstEnd).trans
    (terminal_eq_closure rules seed secondRun secondEnd).symm

theorem step_stays_inside (rules : I → Instance G) (carrier : Finset G)
    (closed : Closed rules carrier) {rows after : Finset G} (inside : rows ⊆ carrier)
    (step : Step rules rows after) : after ⊆ carrier := by
  obtain ⟨i, enabled, rfl, _⟩ := step
  simpa [SetStore.update] using Finset.union_subset inside (closed i (enabled.trans inside))

/-- Finite closure gives an actual terminating execution, even for an infinite rule index. -/
theorem exists_terminal (rules : I → Instance G) (carrier : Finset G)
    (closed : Closed rules carrier) (seed : Finset G) (inside : seed ⊆ carrier) :
    ∃ rows, Relation.ReflTransGen (Step rules) seed rows ∧ Terminal rules rows := by
  classical
  have find : ∀ n (rows : Finset G), carrier.card - rows.card = n → rows ⊆ carrier →
      ∃ after, Relation.ReflTransGen (Step rules) rows after ∧ Terminal rules after := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro rows measure subset
      by_cases terminal : Terminal rules rows
      · exact ⟨rows, .refl, terminal⟩
      · obtain ⟨after, step⟩ : ∃ after, Step rules rows after := by
          simpa only [Terminal, not_forall, not_not] using terminal
        have laterSubset := step_stays_inside rules carrier closed subset step
        have card := step_card_lt step
        have bound := Finset.card_le_card laterSubset
        have smaller : carrier.card - after.card < n := by omega
        obtain ⟨last, run, terminal⟩ := ih _ smaller after rfl laterSubset
        exact ⟨last, .head step run, terminal⟩
  exact find _ seed rfl inside

/-- A finite input alone is insufficient; the finite carrier must be closed. -/
theorem no_infinite_run (rules : I → Instance G) (carrier : Finset G)
    (closed : Closed rules carrier) (run : ℕ → Finset G) (inside : run 0 ⊆ carrier) :
    ¬ ∀ n, Step rules (run n) (run (n + 1)) := by
  intro steps
  have bound : ∀ n, run n ⊆ carrier ∧ n + (run 0).card ≤ (run n).card := by
    intro n
    induction n with
    | zero => exact ⟨inside, by omega⟩
    | succ n ih =>
      refine ⟨step_stays_inside rules carrier closed ih.1 (steps n), ?_⟩
      have larger := step_card_lt (steps n)
      omega
  have contradiction := bound (carrier.card + 1)
  have card := Finset.card_le_card contradiction.1
  omega

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreClosure
