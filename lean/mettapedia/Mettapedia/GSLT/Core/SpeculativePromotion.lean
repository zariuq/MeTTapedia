import Mettapedia.GSLT.Core.RegionQueries

/-!
# Deciding versus acting: promotion of speculative results

A live firing takes a row atomically when its guard holds at commit (`atomicFire`). A two-phase
protocol decides at a snapshot and acts later (`twoPhaseFire`), after a history of other events
(`replay`).

* **(P1)** The atomic take of a cheapest row takes a row that is minimal in the store it fired
  against (`atomicFire_cheapest_correct`), and on a nonempty store some row can be taken
  (`atomicFire_cheapest_exists`).
* **(P2)** Validating only that the chosen row is still present can commit a row that is not the
  cheapest: 7 is chosen from `{7, 9}`, 5 arrives, 7 is taken (`presentOnly_commits_non_cheapest`).
* **(P3)** Re-checking at commit the presence of the row and the predicate query that could defeat
  the choice, "no present row is cheaper" (`cheapestRecheck`), makes the promoted results exactly
  the atomic firing's admissible results at the commit store (`cheapest_promoted_iff_atomic`); in
  general, re-checking the guard does (`promoted_iff_atomic`).
* **(P4)** Write skew: two departures, each decided while the other person is on duty and validated
  take-only, both commit and leave nobody on duty (`write_skew`). With the re-check the second is
  refused, and every re-checked sequence of commits preserves each invariant the atomic firings
  preserve (`commitAll_recheck_preserves`, `commitAll_someoneElse_ne_zero`); take-only validation
  does not (`presentOnly_not_preserves`).
* **(P5)** Firings in a forked simulation store leave the live store unchanged
  (`simFire_live`, `simFires_live`), and commute with live events (`simFire_liveReplay_comm`).
* **(P6)** A guard that is a positive `existsQuery` is stable under growth of the store
  (`existsQuery_mono`, `growthStable_existsQuery`), so promotion needs no predicate re-check while
  the store only grows (`presentOnly_sound_of_growthStable`, `presentOnly_sound_of_inserts`). The
  cheapest-row guard is not stable under growth (`not_growthStable_cheapest`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.SpeculativePromotion

open Mettapedia.GSLT.Core.RegionQueries

universe u v w

/-! ## Deciding versus acting: promotion of speculative results -/

section Promotion

variable {Row : Type u} [DecidableEq Row]

/-- A guard decides, at a store, whether a row may be taken. -/
abbrev Guard (Row : Type u) := Multiset Row → Row → Bool

/-- A validation runs at commit, on the live store and the chosen row. -/
abbrev Validation (Row : Type u) := Multiset Row → Row → Bool

/-- **The atomic guarded take.** Against the store it fires on, it takes `r` when `r` is present
and the guard holds there, in one step. -/
def atomicFire (guard : Guard Row) (S : Multiset Row) (r : Row) : Option (Multiset Row) :=
  if r ∈ S ∧ guard S r = true then some (S.erase r) else none

theorem atomicFire_eq_some_iff {guard : Guard Row} {S S' : Multiset Row} {r : Row} :
    atomicFire guard S r = some S' ↔ (r ∈ S ∧ guard S r = true) ∧ S.erase r = S' := by
  unfold atomicFire
  split_ifs with h <;> simp [h]

/-- Events of the live store between a snapshot and a commit. -/
inductive Event (Row : Type u) where
  | insert (r : Row)
  | take (r : Row)

/-- The effect of one event on a store. -/
def Event.apply : Event Row → Multiset Row → Multiset Row
  | .insert r, S => r ::ₘ S
  | .take r, S => S.erase r

/-- The store after a history of events. -/
def replay (es : List (Event Row)) (S : Multiset Row) : Multiset Row :=
  es.foldl (fun S e => e.apply S) S

/-- **Two-phase promotion.** The row is chosen by the guard at the snapshot `S₀`; at commit, against
the live store `S₁`, the validation runs and the row is taken. -/
def twoPhaseFire (guard : Guard Row) (validate : Validation Row) (S₀ S₁ : Multiset Row)
    (r : Row) : Option (Multiset Row) :=
  if (r ∈ S₀ ∧ guard S₀ r = true) ∧ validate S₁ r = true then some (S₁.erase r) else none

theorem twoPhaseFire_eq_some_iff {guard : Guard Row} {validate : Validation Row}
    {S₀ S₁ S' : Multiset Row} {r : Row} :
    twoPhaseFire guard validate S₀ S₁ r = some S' ↔
      ((r ∈ S₀ ∧ guard S₀ r = true) ∧ validate S₁ r = true) ∧ S₁.erase r = S' := by
  unfold twoPhaseFire
  split_ifs with h <;> simp [h]

/-- Take-only validation: the chosen row is still present. -/
def presentOnly : Validation Row := fun S r => decide (r ∈ S)

/-- Re-check validation: the chosen row is present and the guard holds at commit. -/
def recheck (guard : Guard Row) : Validation Row := fun S r => decide (r ∈ S) && guard S r

/-! ### (P1) The atomic take of a cheapest row -/

variable {C : Type v} [LinearOrder C]

/-- The guard "`r` is a cheapest row": the `forall` query "every row costs at least `r`". -/
def cheapest (cost : Row → C) : Guard Row :=
  fun S r => forallQuery (fun r' => decide (cost r ≤ cost r')) S

omit [DecidableEq Row] in
theorem cheapest_eq_true_iff {cost : Row → C} {S : Multiset Row} {r : Row} :
    cheapest cost S r = true ↔ ∀ r' ∈ S, cost r ≤ cost r' := by
  rw [cheapest, forallQuery_eq_true_iff]
  simp

/-- **(P1)** The atomic take of a cheapest row is correct at commit: the taken row is present and
minimal in the store it fired against, and the result is that store without it. -/
theorem atomicFire_cheapest_correct {cost : Row → C} {S S' : Multiset Row} {r : Row}
    (h : atomicFire (cheapest cost) S r = some S') :
    r ∈ S ∧ (∀ r' ∈ S, cost r ≤ cost r') ∧ S' = S.erase r := by
  obtain ⟨⟨hr, hg⟩, rfl⟩ := atomicFire_eq_some_iff.mp h
  exact ⟨hr, cheapest_eq_true_iff.mp hg, rfl⟩

/-- On a nonempty store, some cheapest row can be taken. -/
theorem atomicFire_cheapest_exists (cost : Row → C) {S : Multiset Row} (h : S ≠ 0) :
    ∃ r, atomicFire (cheapest cost) S r = some (S.erase r) := by
  obtain ⟨r, hr, hmin⟩ := Multiset.exists_min_image cost h
  exact ⟨r, atomicFire_eq_some_iff.mpr ⟨⟨hr, cheapest_eq_true_iff.mpr hmin⟩, rfl⟩⟩

/-! ### (P2) Take-only validation commits a row that is not the cheapest -/

/-- **(P2)** 7 is chosen as the cheapest of `{7, 9}`, 5 is inserted, and take-only validation lets
7 be taken although 5 is cheaper; the atomic take refuses 7 at that store. -/
theorem presentOnly_commits_non_cheapest :
    twoPhaseFire (cheapest id) presentOnly ({7, 9} : Multiset ℕ)
        (replay [.insert 5] {7, 9}) 7 = some {5, 9} ∧
      existsQuery (fun r => decide (r < 7)) (replay [.insert 5] ({7, 9} : Multiset ℕ)) = true ∧
      atomicFire (cheapest id) (replay [.insert 5] ({7, 9} : Multiset ℕ)) 7 = none := by
  decide

/-- Take-only validation is not sound for the cheapest-row guard. -/
theorem presentOnly_not_sound :
    ¬ ∀ (S₀ S₁ S' : Multiset ℕ) (r : ℕ),
      twoPhaseFire (cheapest id) presentOnly S₀ S₁ r = some S' →
        atomicFire (cheapest id) S₁ r = some S' := by
  intro h
  have := h _ _ _ _ presentOnly_commits_non_cheapest.1
  rw [presentOnly_commits_non_cheapest.2.2] at this
  nomatch this

/-! ### (P3) Sound promotion -/

/-- **Re-checking the guard makes promotion sound**, whatever happened between snapshot and
commit: a promoted result is an admissible result of the atomic firing at the commit store. -/
theorem twoPhaseFire_recheck_sound {guard : Guard Row} {S₀ S₁ S' : Multiset Row} {r : Row}
    (h : twoPhaseFire guard (recheck guard) S₀ S₁ r = some S') :
    atomicFire guard S₁ r = some S' := by
  obtain ⟨⟨-, hv⟩, rfl⟩ := twoPhaseFire_eq_some_iff.mp h
  simp only [recheck, Bool.and_eq_true, decide_eq_true_eq] at hv
  exact atomicFire_eq_some_iff.mpr ⟨hv, rfl⟩

/-- Every admissible atomic result is promoted, from a snapshot where the choice was made. -/
theorem twoPhaseFire_recheck_complete {guard : Guard Row} {S₁ S' : Multiset Row} {r : Row}
    (h : atomicFire guard S₁ r = some S') : twoPhaseFire guard (recheck guard) S₁ S₁ r = some S' := by
  obtain ⟨hv, rfl⟩ := atomicFire_eq_some_iff.mp h
  exact twoPhaseFire_eq_some_iff.mpr ⟨⟨hv, by simp [recheck, hv.1, hv.2]⟩, rfl⟩

/-- **(P3, general form)** With the re-check, the promoted results at a commit store are exactly
the atomic firing's admissible results there. -/
theorem promoted_iff_atomic {guard : Guard Row} {S₁ S' : Multiset Row} {r : Row} :
    (∃ S₀, twoPhaseFire guard (recheck guard) S₀ S₁ r = some S') ↔
      atomicFire guard S₁ r = some S' :=
  ⟨fun ⟨_, h⟩ => twoPhaseFire_recheck_sound h, fun h => ⟨S₁, twoPhaseFire_recheck_complete h⟩⟩

/-- The re-check that promotion of a cheapest choice needs: the chosen row is present, and the
predicate query that could defeat the choice, "no present row is cheaper", holds. -/
def cheapestRecheck (cost : Row → C) : Validation Row :=
  fun S r => decide (r ∈ S) && noneQuery (fun r' => decide (cost r' < cost r)) S

/-- The presence-and-`none` re-check is the re-check of the cheapest-row guard. -/
theorem cheapestRecheck_eq_recheck (cost : Row → C) :
    cheapestRecheck cost = recheck (cheapest cost) := by
  funext S r
  simp only [cheapestRecheck, recheck, cheapest, noneQuery_eq_forallQuery_not]
  congr 1
  congr 1
  funext r'
  rw [← decide_not]
  exact decide_eq_decide.mpr not_lt

/-- **(P3)** Validating at commit the chosen row's presence and "no present row is cheaper" makes
the two-phase results exactly the atomic firing's admissible results at the commit store. -/
theorem cheapest_promoted_iff_atomic {cost : Row → C} {S₁ S' : Multiset Row} {r : Row} :
    (∃ S₀, twoPhaseFire (cheapest cost) (cheapestRecheck cost) S₀ S₁ r = some S') ↔
      atomicFire (cheapest cost) S₁ r = some S' := by
  rw [cheapestRecheck_eq_recheck]
  exact promoted_iff_atomic

/-- With the re-check, the P2 history is refused. -/
theorem cheapestRecheck_refuses :
    twoPhaseFire (cheapest id) (cheapestRecheck id) ({7, 9} : Multiset ℕ)
      (replay [.insert 5] {7, 9}) 7 = none := by
  decide

/-! ### (P4) Write skew -/

/-- The departure guard: the leaver may go while someone else is on duty, an `exists` query. -/
def someoneElse : Guard Row := fun S r => existsQuery (fun r' => decide (r' ≠ r)) S

/-- Every atomic departure leaves someone on duty. -/
theorem atomicFire_someoneElse_ne_zero {S S' : Multiset Row} {r : Row}
    (h : atomicFire someoneElse S r = some S') : S' ≠ 0 := by
  obtain ⟨⟨-, hg⟩, rfl⟩ := atomicFire_eq_some_iff.mp h
  obtain ⟨r', hr', hne⟩ := (existsQuery_eq_true_iff _).mp hg
  exact ne_zero_of_mem ((Multiset.mem_erase_of_ne (by simpa using hne)).mpr hr')

/-- Take-only validation never sees a conflict between takes of distinct rows. -/
theorem presentOnly_after_take_of_ne {S : Multiset Row} {r₁ r₂ : Row} (hne : r₂ ≠ r₁)
    (hr : r₂ ∈ S) : presentOnly (S.erase r₁) r₂ = true := by
  simpa [presentOnly] using (Multiset.mem_erase_of_ne hne).mpr hr

/-- Commit proposals one after another against the live store; each proposal is a snapshot and the
row chosen there, and a refused proposal leaves the store unchanged. -/
def commitAll (guard : Guard Row) (validate : Validation Row) :
    List (Multiset Row × Row) → Multiset Row → Multiset Row
  | [], S => S
  | (S₀, r) :: ps, S => commitAll guard validate ps ((twoPhaseFire guard validate S₀ S r).getD S)

/-- **Re-checked promotion preserves every invariant that the atomic firings preserve**, in any
order of commits and from any snapshots. -/
theorem commitAll_recheck_preserves {guard : Guard Row} {Inv : Multiset Row → Prop}
    (preserved : ∀ S r, Inv S → r ∈ S → guard S r = true → Inv (S.erase r))
    (ps : List (Multiset Row × Row)) {S : Multiset Row} (h : Inv S) :
    Inv (commitAll guard (recheck guard) ps S) := by
  induction ps generalizing S with
  | nil => exact h
  | cons p ps ih =>
      obtain ⟨S₀, r⟩ := p
      apply ih
      rcases hf : twoPhaseFire guard (recheck guard) S₀ S r with _ | S'
      · exact h
      · obtain ⟨⟨hr, hg⟩, rfl⟩ := atomicFire_eq_some_iff.mp (twoPhaseFire_recheck_sound hf)
        exact preserved S r h hr hg

/-- Re-checked departures never leave nobody on duty. -/
theorem commitAll_someoneElse_ne_zero (ps : List (Multiset Row × Row)) {S : Multiset Row}
    (h : S ≠ 0) : commitAll someoneElse (recheck someoneElse) ps S ≠ 0 :=
  commitAll_recheck_preserves (Inv := fun S => S ≠ 0) (fun _ _ _ hr hg =>
    atomicFire_someoneElse_ne_zero (atomicFire_eq_some_iff.mpr ⟨⟨hr, hg⟩, rfl⟩)) ps h

/-- Two people on a roster. -/
inductive Staff where
  | alice
  | bob
  deriving DecidableEq

/-- **(P4) Write skew.** From the snapshot `{alice, bob}`, "alice leaves while bob is on duty" and
"bob leaves while alice is on duty" are each validated take-only, both commit, and nobody is left
on duty. With the re-check, the second is refused. -/
theorem write_skew :
    let roster : Multiset Staff := {.alice, .bob}
    twoPhaseFire someoneElse presentOnly roster roster .alice = some {.bob} ∧
      twoPhaseFire someoneElse presentOnly roster {.bob} .bob = some 0 ∧
      commitAll someoneElse presentOnly [(roster, .alice), (roster, .bob)] roster = 0 ∧
      twoPhaseFire someoneElse (recheck someoneElse) roster roster .alice = some {.bob} ∧
      twoPhaseFire someoneElse (recheck someoneElse) roster {.bob} .bob = none ∧
      commitAll someoneElse (recheck someoneElse) [(roster, .alice), (roster, .bob)] roster =
        {.bob} := by
  decide

/-- Take-only validation does not preserve the on-duty invariant. -/
theorem presentOnly_not_preserves :
    ¬ ∀ (ps : List (Multiset Staff × Staff)) (S : Multiset Staff), S ≠ 0 →
      commitAll someoneElse presentOnly ps S ≠ 0 := by
  intro h
  exact h _ _ (by decide) write_skew.2.2.1

/-! ### (P5) Confinement -/

/-- A live store and a forked simulation store. -/
structure Worlds (Row : Type u) where
  live : Multiset Row
  sim : Multiset Row

/-- Fork a simulation store from the live store. -/
def Worlds.fork (S : Multiset Row) : Worlds Row := ⟨S, S⟩

/-- An atomic firing in the simulation store. -/
def Worlds.simFire (guard : Guard Row) (r : Row) (w : Worlds Row) : Worlds Row :=
  { w with sim := (atomicFire guard w.sim r).getD w.sim }

/-- A history of events on the live store. -/
def Worlds.liveReplay (es : List (Event Row)) (w : Worlds Row) : Worlds Row :=
  { w with live := replay es w.live }

/-- **(P5)** A simulated firing leaves the live store unchanged. -/
@[simp] theorem simFire_live (guard : Guard Row) (r : Row) (w : Worlds Row) :
    (w.simFire guard r).live = w.live := rfl

/-- Any sequence of simulated firings leaves the live store unchanged. -/
theorem simFires_live (guard : Guard Row) (rs : List Row) (w : Worlds Row) :
    (rs.foldl (fun w r => w.simFire guard r) w).live = w.live := by
  induction rs generalizing w with
  | nil => rfl
  | cons r rs ih => exact (ih _).trans (simFire_live guard r w)

/-- Simulated firings commute with live events. -/
theorem simFire_liveReplay_comm (guard : Guard Row) (r : Row) (es : List (Event Row))
    (w : Worlds Row) : (w.simFire guard r).liveReplay es = (w.liveReplay es).simFire guard r :=
  rfl

/-! ### (P6) The fast path for growth-stable guards -/

/-- A guard is stable under growth when a store that keeps every row and gains some keeps the
guard true. -/
def GrowthStable (guard : Guard Row) : Prop :=
  ∀ S T r, S ⊆ T → guard S r = true → guard T r = true

omit [DecidableEq Row] in
/-- **A positive `exists` guard is stable under growth.** -/
theorem growthStable_existsQuery (p : Row → Row → Bool) :
    GrowthStable (fun S r => existsQuery (p r) S) :=
  fun _ _ r h => existsQuery_mono (p r) h

omit [DecidableEq Row] in
/-- A positive `exists` stays true while the rows of its region only grow. -/
theorem existsQuery_of_region_grows (p : Row → Bool) {S T : Multiset Row}
    (h : ∀ r ∈ S, p r = true → r ∈ T) (hS : existsQuery p S = true) :
    existsQuery p T = true := by
  obtain ⟨r, hr, hp⟩ := (existsQuery_eq_true_iff p).mp hS
  exact (existsQuery_eq_true_iff p).mpr ⟨r, h r hr hp, hp⟩

/-- **(P6)** For a growth-stable guard, take-only validation is sound while the store only grows:
the promoted result is an admissible result of the atomic firing at the commit store. -/
theorem presentOnly_sound_of_growthStable {guard : Guard Row} (hg : GrowthStable guard)
    {S₀ S₁ S' : Multiset Row} {r : Row} (grows : S₀ ⊆ S₁)
    (h : twoPhaseFire guard presentOnly S₀ S₁ r = some S') : atomicFire guard S₁ r = some S' := by
  obtain ⟨⟨⟨-, hguard⟩, hv⟩, rfl⟩ := twoPhaseFire_eq_some_iff.mp h
  exact atomicFire_eq_some_iff.mpr ⟨⟨by simpa [presentOnly] using hv, hg _ _ _ grows hguard⟩, rfl⟩

/-- A history of inserts only grows the store. -/
theorem le_replay_of_inserts {es : List (Event Row)} (h : ∀ e ∈ es, ∃ r, e = .insert r)
    (S : Multiset Row) : S ≤ replay es S := by
  induction es generalizing S with
  | nil => exact le_rfl
  | cons e es ih =>
      obtain ⟨r, rfl⟩ := h e (List.mem_cons_self ..)
      exact (Multiset.le_cons_self S r).trans (ih (fun e he => h e (List.mem_cons_of_mem _ he)) _)

/-- Under a history of inserts, a growth-stable guard needs no validation at all beyond the
choice made at the snapshot. -/
theorem presentOnly_sound_of_inserts {guard : Guard Row} (hg : GrowthStable guard)
    {S₀ : Multiset Row} {es : List (Event Row)} (h : ∀ e ∈ es, ∃ r, e = .insert r) {r : Row}
    (chosen : r ∈ S₀ ∧ guard S₀ r = true) :
    twoPhaseFire guard presentOnly S₀ (replay es S₀) r = some ((replay es S₀).erase r) ∧
      atomicFire guard (replay es S₀) r = some ((replay es S₀).erase r) := by
  have grows := Multiset.subset_of_le (le_replay_of_inserts h S₀)
  have fired : twoPhaseFire guard presentOnly S₀ (replay es S₀) r =
      some ((replay es S₀).erase r) :=
    twoPhaseFire_eq_some_iff.mpr ⟨⟨chosen, by simpa [presentOnly] using grows chosen.1⟩, rfl⟩
  exact ⟨fired, presentOnly_sound_of_growthStable hg grows fired⟩

/-- The cheapest-row guard is not stable under growth: it is a `forall` query. -/
theorem not_growthStable_cheapest : ¬ GrowthStable (cheapest (id : ℕ → ℕ)) := by
  intro h
  have := h {7} {5, 7} 7 (by simp) (by decide)
  exact absurd this (by decide)

/-- The departure guard is stable under growth; write skew needed a take in the history. -/
theorem growthStable_someoneElse : GrowthStable (someoneElse (Row := Row)) :=
  growthStable_existsQuery fun r r' => decide (r' ≠ r)

end Promotion

end Mettapedia.GSLT.Core.SpeculativePromotion

#print axioms Mettapedia.GSLT.Core.SpeculativePromotion.atomicFire_cheapest_correct
#print axioms Mettapedia.GSLT.Core.SpeculativePromotion.atomicFire_cheapest_exists
#print axioms Mettapedia.GSLT.Core.SpeculativePromotion.presentOnly_commits_non_cheapest
#print axioms Mettapedia.GSLT.Core.SpeculativePromotion.presentOnly_not_sound
#print axioms Mettapedia.GSLT.Core.SpeculativePromotion.twoPhaseFire_recheck_sound
#print axioms Mettapedia.GSLT.Core.SpeculativePromotion.twoPhaseFire_recheck_complete
#print axioms Mettapedia.GSLT.Core.SpeculativePromotion.promoted_iff_atomic
#print axioms Mettapedia.GSLT.Core.SpeculativePromotion.cheapestRecheck_eq_recheck
#print axioms Mettapedia.GSLT.Core.SpeculativePromotion.cheapest_promoted_iff_atomic
#print axioms Mettapedia.GSLT.Core.SpeculativePromotion.cheapestRecheck_refuses
#print axioms Mettapedia.GSLT.Core.SpeculativePromotion.atomicFire_someoneElse_ne_zero
#print axioms Mettapedia.GSLT.Core.SpeculativePromotion.presentOnly_after_take_of_ne
#print axioms Mettapedia.GSLT.Core.SpeculativePromotion.commitAll_recheck_preserves
#print axioms Mettapedia.GSLT.Core.SpeculativePromotion.commitAll_someoneElse_ne_zero
#print axioms Mettapedia.GSLT.Core.SpeculativePromotion.write_skew
#print axioms Mettapedia.GSLT.Core.SpeculativePromotion.presentOnly_not_preserves
#print axioms Mettapedia.GSLT.Core.SpeculativePromotion.simFires_live
#print axioms Mettapedia.GSLT.Core.SpeculativePromotion.simFire_liveReplay_comm
#print axioms Mettapedia.GSLT.Core.SpeculativePromotion.growthStable_existsQuery
#print axioms Mettapedia.GSLT.Core.SpeculativePromotion.existsQuery_of_region_grows
#print axioms Mettapedia.GSLT.Core.SpeculativePromotion.presentOnly_sound_of_growthStable
#print axioms Mettapedia.GSLT.Core.SpeculativePromotion.le_replay_of_inserts
#print axioms Mettapedia.GSLT.Core.SpeculativePromotion.presentOnly_sound_of_inserts
#print axioms Mettapedia.GSLT.Core.SpeculativePromotion.not_growthStable_cheapest
#print axioms Mettapedia.GSLT.Core.SpeculativePromotion.growthStable_someoneElse

#print axioms Mettapedia.GSLT.Core.SpeculativePromotion.simFire_live
