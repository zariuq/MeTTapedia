import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FairSearch
import Mettapedia.GSLT.Core.ObservedBisimulation

/-!
# Proof identity for fair search: reachability is too coarse, bisimulation sees what fairness needs

`FairSearch` shows that completeness of fair search is not decided by which stores are reachable:
the take race and the repaired race reach the same stores, and only the repaired one proves in
every fair run. What separates them is the branching property **"from every reachable state a state
with the proof stays reachable"** (`AlwaysPossibly`, `AG EF`).

* Two search programs side by side form one GSLT whose terms are stores of either program
  (`pairGSLT`), observed by which occurrences a store holds (`pairObserved`).
* **Observed bisimilarity preserves `AlwaysPossibly`** (`alwaysPossibly_of_bisimilar`), for every
  observed GSLT: paths transfer along a bisimulation both ways (`multiStep_forward`,
  `multiStep_backward`).
* **So the two races are not bisimilar** (`races_not_bisimilar`): the repaired race keeps the proof
  possible from every reachable store (`repair_alwaysPossibly`), the take race does not
  (`take_not_alwaysPossibly`).

`search_identity_is_branching` puts the four facts together. An identity of proof searches that is
to respect completeness under fairness cannot be the set of reachable configurations; observed
bisimulation, the identity of `Race.Generic`, is fine enough to see the difference.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FairSearchIdentity

open Mettapedia.GSLT (GSLT ObservedGSLT)
open MeTTaCalculus.OccurrenceCommits (Commit Enabled fire)
open FairSearch FairSearch.Controls

universe u v

/-! ## Observed bisimilarity preserves `AlwaysPossibly` -/

section Preservation

variable {S : GSLT} (obs : ObservedGSLT S)

/-- **From every reachable term, a term showing `a` stays reachable** (`AG EF a`). -/
def AlwaysPossibly (a : obs.Atom) (t : S.Term) : Prop :=
  ∀ t', S.MultiStep t t' → ∃ t'', S.MultiStep t' t'' ∧ obs.observes a t''

variable {obs}

theorem multiStep_forward {R : S.Term → S.Term → Prop} (bis : obs.IsBisimulation R) :
    ∀ {t t' : S.Term}, S.MultiStep t t' → ∀ {u : S.Term}, R t u → ∃ u', S.MultiStep u u' ∧ R t' u'
  | _, _, .refl _, u, rel => ⟨u, .refl u, rel⟩
  | _, _, .step first rest, _, rel => by
      obtain ⟨u₁, step₁, rel₁⟩ := bis.1.1 rel first
      obtain ⟨u', steps, rel'⟩ := multiStep_forward bis rest rel₁
      exact ⟨u', .step step₁ steps, rel'⟩

theorem multiStep_backward {R : S.Term → S.Term → Prop} (bis : obs.IsBisimulation R) :
    ∀ {u u' : S.Term}, S.MultiStep u u' → ∀ {t : S.Term}, R t u → ∃ t', S.MultiStep t t' ∧ R t' u'
  | _, _, .refl _, t, rel => ⟨t, .refl t, rel⟩
  | _, _, .step first rest, _, rel => by
      obtain ⟨t₁, step₁, rel₁⟩ := bis.1.2 rel first
      obtain ⟨t', steps, rel'⟩ := multiStep_backward bis rest rel₁
      exact ⟨t', .step step₁ steps, rel'⟩

/-- **Observed bisimilarity preserves `AlwaysPossibly`.** -/
theorem alwaysPossibly_of_bisimilar {t u : S.Term} (bisimilar : obs.Bisimilar t u) {a : obs.Atom}
    (holds : AlwaysPossibly obs a u) : AlwaysPossibly obs a t := by
  obtain ⟨R, bis, rel⟩ := bisimilar
  intro t' steps
  obtain ⟨u', usteps, rel'⟩ := multiStep_forward bis steps rel
  obtain ⟨u'', more, seen⟩ := holds u' usteps
  obtain ⟨t'', tmore, rel''⟩ := multiStep_backward bis more rel'
  exact ⟨t'', tmore, (bis.2 rel'' a).mpr seen⟩

end Preservation

/-! ## Two search programs as one GSLT -/

section Pair

variable {O : Type u} [DecidableEq O] {L : Type v} (label : O → L)

/-- A store rewrites by firing an enabled commit of the program. -/
abbrev rewritesOf (program : Set (Commit O L)) (s s' : Finset O) : Prop :=
  ∃ c, c ∈ program ∧ Enabled label s c ∧ s' = fire s c

/-- **Two search programs side by side**: a term is a store of the first or of the second, and each
rewrites by its own program. -/
def pairGSLT (first second : Set (Commit O L)) : GSLT where
  Term := Finset O ⊕ Finset O
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites t t' := match t, t' with
    | .inl s, .inl s' => rewritesOf label first s s'
    | .inr s, .inr s' => rewritesOf label second s s'
    | _, _ => False
  rewrites_resp_left := by
    intro t t' u same step
    cases same
    exact ⟨u, step, rfl⟩
  rewrites_resp_right := by
    intro t u u' step same
    cases same
    exact step

/-- A store is observed by the occurrences it holds. -/
def pairObserved (first second : Set (Commit O L)) : ObservedGSLT (pairGSLT label first second) where
  Atom := O
  observes o t := match t with
    | .inl s => o ∈ s
    | .inr s => o ∈ s

end Pair

/-! ## The two races -/

/-- The take race and the repaired race, side by side. -/
abbrev races : GSLT := pairGSLT (id : ℕ → ℕ) takeRace repairRace

abbrev racesObserved : ObservedGSLT races := pairObserved (id : ℕ → ℕ) takeRace repairRace

/-- From the take race's dead end nothing moves. -/
theorem dead_end_stuck {t₀ t : races.Term} (steps : races.MultiStep t₀ t) (start : t₀ = .inl {1}) :
    t = .inl {1} := by
  cases steps with
  | refl => exact start
  | @step _ next _ first _ =>
      exfalso
      subst start
      cases next with
      | inl s' =>
          obtain ⟨c, member, enabled, -⟩ := (first : rewritesOf id takeRace {1} s')
          rcases member with rfl | rfl
          · exact absurd enabled (by decide)
          · exact absurd enabled (by decide)
      | inr s' => exact (first : False)

/-- **The take race does not keep the proof possible**: it reaches its dead end. -/
theorem take_not_alwaysPossibly : ¬ AlwaysPossibly racesObserved (2 : ℕ) (.inl {0}) := by
  intro holds
  have result : fire {0} wrongTake = {1} := by decide
  have reach : races.MultiStep (.inl {0}) (.inl {1}) := by
    rw [← result]
    exact .step (show races.Step (.inl {0}) (.inl (fire {0} wrongTake)) from
      (⟨wrongTake, Or.inl rfl, by decide, rfl⟩ : rewritesOf id takeRace {0} (fire {0} wrongTake)))
      (.refl _)
  obtain ⟨t'', steps, seen⟩ := holds _ reach
  rw [dead_end_stuck steps rfl] at seen
  have absent : (2 : ℕ) ∈ ({1} : Finset ℕ) := seen
  exact absurd absent (by decide)

/-- The repaired race stays among its three stores. -/
theorem repair_multiStep_store {t t' : races.Term} (steps : races.MultiStep t t') :
    ∀ {s : Finset ℕ}, t = .inr s → RaceStore s → ∃ s', t' = .inr s' ∧ RaceStore s' := by
  induction steps with
  | refl t => exact fun {s} same store => ⟨s, same, store⟩
  | @step t next t' first _ ih =>
      intro s same store
      subst same
      cases next with
      | inl s' => exact (first : False).elim
      | inr s' =>
          obtain ⟨c, member, enabled, rfl⟩ := (first : rewritesOf id repairRace s s')
          apply ih rfl
          rcases repair_step store member enabled with ⟨-, h | h⟩ | ⟨-, h⟩
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
          · exact Or.inr (Or.inr h)

/-- **The repaired race keeps the proof possible from every reachable store.** -/
theorem repair_alwaysPossibly : AlwaysPossibly racesObserved (2 : ℕ) (.inr {0}) := by
  intro t' steps
  obtain ⟨s', rfl, store⟩ := repair_multiStep_store steps rfl (Or.inl rfl)
  rcases store with rfl | rfl | rfl
  · refine ⟨.inr (fire {0} rightTake), .step (show races.Step (.inr {0}) (.inr (fire {0} rightTake)) from
      (⟨rightTake, Or.inr (Or.inl rfl), by decide, rfl⟩ :
        rewritesOf id repairRace {0} (fire {0} rightTake))) (.refl _), ?_⟩
    show (2 : ℕ) ∈ fire {0} rightTake
    decide
  · refine ⟨.inr (fire {1} repair), .step (show races.Step (.inr {1}) (.inr (fire {1} repair)) from
      (⟨repair, Or.inr (Or.inr rfl), by decide, rfl⟩ :
        rewritesOf id repairRace {1} (fire {1} repair))) (.refl _), ?_⟩
    show (2 : ℕ) ∈ fire {1} repair
    decide
  · exact ⟨.inr {2}, .refl _, (by decide : (2 : ℕ) ∈ ({2} : Finset ℕ))⟩

/-- **The two races are not bisimilar.** -/
theorem races_not_bisimilar : ¬ racesObserved.Bisimilar (.inl {0}) (.inr {0}) := fun bisimilar =>
  take_not_alwaysPossibly (alwaysPossibly_of_bisimilar bisimilar repair_alwaysPossibly)

/-- **The identity of proof searches must be branching.** The two races reach the same stores, yet
they are not bisimilar, and exactly one keeps the proof possible from every reachable store, the
property that completeness under fairness rests on (`FairSearch.Controls.repair_fair_proves`,
`FairSearch.Controls.race_stronglyFair`). -/
theorem search_identity_is_branching :
    (∀ s, (commitSystem id takeRace).Reachable {0} s ↔ (commitSystem id repairRace).Reachable {0} s) ∧
      ¬ racesObserved.Bisimilar (.inl {0}) (.inr {0}) ∧
      ¬ AlwaysPossibly racesObserved (2 : ℕ) (.inl {0}) ∧
      AlwaysPossibly racesObserved (2 : ℕ) (.inr {0}) :=
  ⟨race_reachable_iff, races_not_bisimilar, take_not_alwaysPossibly, repair_alwaysPossibly⟩

#print axioms multiStep_forward
#print axioms multiStep_backward
#print axioms alwaysPossibly_of_bisimilar
#print axioms dead_end_stuck
#print axioms take_not_alwaysPossibly
#print axioms repair_multiStep_store
#print axioms repair_alwaysPossibly
#print axioms races_not_bisimilar
#print axioms search_identity_is_branching

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FairSearchIdentity
