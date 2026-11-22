import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.UnionInter
import Mathlib.Data.Multiset.Filter
import Mathlib.Tactic
import Mettapedia.GSLT.Logic.BagRelativePushout

/-!
# The borrowed-context transition system of commits over bags

Two programs are the same when no environment can tell them apart. An environment is something
that runs *beside* a program, so the first thing an equivalence needs is a transition system in
which a program's steps say what they need from beside them. This module builds that system for
ground commits, the firings of `transform`.

## The level: bags of labels

A behavioural equivalence compares stores by what they contain, not by which identities their
occurrences carry: two stores with the same bag of labels must be equivalent. So this module
works over bags of labels (`Multiset R`). The commits of the occurrence model project onto the
rules here through their labels (`CommitProjection`).

## Rules

A ground **rule** (`Rule`) takes a bag, keeps a bag, makes a bag, and queries some regions. In
normal form a predicate query sees exactly what the rule uses inside the region, so a rule's
application conditions are one predicate, `closed`, the union of the regions it queries: their
world must be closed.
A rule is **enabled** at a bag `M` when what it takes and keeps is in `M` and nothing else of `M`
lies in a closed region (`Rule.Enabled`); equivalently, each closed region of `M` holds exactly
what the rule uses there (`Rule.enabled_iff_filter`). Absence is a closed region in which the rule
uses nothing; counts, folds, uniqueness and the completeness queries of `every` are closed regions in
which it uses what it saw. A rule is **positive** when it closes no region.

## The borrowed-context step

`ρ.Step M ⟨J, F⟩ M'` (`Rule.Step`) says: placed beside an environment that supplies `J` and
whose remaining part avoids `F`, the bag `M` fires `ρ` and becomes `M'` (plus that remaining part).

* **The label borrows the least context.** `J = redex - M`, what the rule uses and `M` lacks. Every
  environment in which the rule fires at `M` contains `J`, and its remaining part avoids the closed
  regions (`Rule.Enabled.least`). In the category of bag contexts the square
  `M + J = redex + (M - redex)` is an idem pushout: its legs share nothing
  (`Rule.label_isIdemPushout`, through `BagRelativePushout.isIdemPushout_bag`). So `J` is the
  Leifer–Milner label of the reaction.
* **The label also reports the closed regions** (`F = closed`). A predicate query is not monotone:
  one more occurrence inside its region disables it. So the step holds in exactly the environments
  `J + E` with `E` avoiding `F` (`Rule.Step.enabled_with`, `Rule.Step.of_enabled_with`), and the
  label must say so. A step holds in every larger environment exactly when its rule is positive
  (`Rule.step_unconditional_iff`). This is the borrowed-context reading of the waking theorems of
  the reactive module, now as a transition system rather than a property of guards: positive commits
  are woken by arrivals, the others by arrivals under a condition on the rest of the environment.
* **Steps lift into contexts and split out of them.** A labelled step of `M` is a labelled step of
  `M + C` with the label shrunk by `C`, when the part of `C` not borrowed avoids the condition
  (`Rule.Step.lift`); every labelled step of `M + C` arises in this way from the least step of `M`
  (`Rule.Step.split`). These two facts are what make the equivalences of `Bisimulation`
  compositional.
* **Reduction is the step with nothing borrowed** (`reduces_iff_step_zero`): a closed system is a
  bag beside an empty environment.

## Controls

`Controls` uses a lock and a token. A reader of the token, parked at the empty bag, borrows the
token, unconditionally; a step guarded by the absence of the lock borrows nothing and reports the
lock's region; beside a lock it does not fire, and it fires once the lock is gone, which is the
environment's own step (`Controls.absence_label`, `Controls.absence_blocked_by_lock`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence

universe u

variable {R : Type u} [DecidableEq R]

/-! ## Bag arithmetic -/

section BagArith

/-- Equalities and inequalities of bags, coordinate by coordinate. -/
macro "bag_count" : tactic =>
  `(tactic| (simp only [Multiset.count_add, Multiset.count_sub, Multiset.count_inter,
      Multiset.count_union, Multiset.count_zero] at *; omega))

theorem frame_split (X C l : Multiset R) : X + C - l = (X - l) + (C - (l - X)) := by
  ext x; bag_count

theorem label_square (M l : Multiset R) : M + (l - M) = l + (M - l) := by
  ext x; bag_count

theorem label_frame_inter (M l : Multiset R) : (l - M) ∩ (M - l) = 0 := by
  ext x; bag_count

theorem le_add_label (M l E : Multiset R) : l ≤ M + (l - M) + E := by
  rw [Multiset.le_iff_count]; intro x; bag_count

theorem add_label_sub (M l E : Multiset R) : M + (l - M) + E - l = (M - l) + E := by
  ext x; bag_count

theorem add_label_sub' (M l : Multiset R) : M + (l - M) - l = M - l := by
  ext x; bag_count

theorem le_add_label' (M l : Multiset R) : l ≤ M + (l - M) := by
  rw [Multiset.le_iff_count]; intro x; bag_count

theorem sub_add_eq_sub_sub (l X C : Multiset R) : l - (X + C) = (l - X) - C := by
  ext x; bag_count

theorem result_add_frame {A T : Multiset R} (sub : T ≤ A) (D Mk : Multiset R) :
    A + D - T + Mk = (A - T + Mk) + D := by
  ext x
  have := Multiset.le_iff_count.mp sub x
  bag_count

theorem lift_bag (M C l : Multiset R) :
    M + C + ((l - M) - C) = (M + (l - M)) + (C - (l - M)) := by
  ext x; bag_count

theorem label_le_add (M C l : Multiset R) (sub : l ≤ M + C) : l - M ≤ C := by
  rw [Multiset.le_iff_count] at sub ⊢
  intro x
  have := sub x
  bag_count

end BagArith

/-! ## Avoiding a region -/

/-- A bag avoids a region when none of its labels lies in it. -/
def Avoids (M : Multiset R) (F : R → Bool) : Prop := ∀ x ∈ M, F x = false

instance (M : Multiset R) (F : R → Bool) : Decidable (Avoids M F) :=
  inferInstanceAs (Decidable (∀ x ∈ M, F x = false))

omit [DecidableEq R] in
@[simp] theorem avoids_zero (F : R → Bool) : Avoids (0 : Multiset R) F := by
  intro x member; simp at member

omit [DecidableEq R] in
theorem avoids_add {A B : Multiset R} {F : R → Bool} :
    Avoids (A + B) F ↔ Avoids A F ∧ Avoids B F := by
  simp only [Avoids, Multiset.mem_add]
  exact ⟨fun h => ⟨fun x m => h x (Or.inl m), fun x m => h x (Or.inr m)⟩,
    fun h x m => m.elim (h.1 x) (h.2 x)⟩

omit [DecidableEq R] in
theorem Avoids.mono {A B : Multiset R} {F : R → Bool} (sub : A ≤ B) (avoids : Avoids B F) :
    Avoids A F := fun x member => avoids x (Multiset.mem_of_le sub member)

omit [DecidableEq R] in
theorem Avoids.weaken {A : Multiset R} {F G : R → Bool} (avoids : Avoids A F)
    (weaker : ∀ x ∈ A, G x = true → F x = true) : Avoids A G := by
  intro x member
  cases hG : G x
  · rfl
  · have := weaker x member hG
    rw [avoids x member] at this
    exact absurd this (by decide)

omit [DecidableEq R] in
theorem avoids_iff_filter {A : Multiset R} {F : R → Bool} :
    Avoids A F ↔ A.filter (fun x => F x = true) = 0 := by
  rw [Multiset.filter_eq_nil]
  simp [Avoids]

omit [DecidableEq R] in
/-- Every bag avoids the empty region. -/
theorem avoids_none (A : Multiset R) : Avoids A (fun _ => false) := fun _ _ => rfl

/-! ## Rules -/

/-- A ground rule: what it takes, keeps and makes, and the union of the regions it queries. -/
structure Rule (R : Type u) where
  take : Multiset R
  keep : Multiset R
  make : Multiset R
  closed : R → Bool

namespace Rule

/-- What a rule uses: what it takes and what it keeps. -/
def redex (ρ : Rule R) : Multiset R := ρ.take + ρ.keep

/-- A rule is positive when it queries no region. -/
def Positive (ρ : Rule R) : Prop := ∀ x, ρ.closed x = false

/-- A rule is enabled at a bag: what it uses is there, and nothing else lies in a region it
queries. -/
def Enabled (ρ : Rule R) (M : Multiset R) : Prop := ρ.redex ≤ M ∧ Avoids (M - ρ.redex) ρ.closed

/-- Firing: remove what is taken, add what is made. -/
def result (ρ : Rule R) (M : Multiset R) : Multiset R := M - ρ.take + ρ.make

omit [DecidableEq R] in
theorem take_le_redex (ρ : Rule R) : ρ.take ≤ ρ.redex := Multiset.le_add_right _ _

omit [DecidableEq R] in
theorem keep_le_redex (ρ : Rule R) : ρ.keep ≤ ρ.redex := Multiset.le_add_left _ _

/-- **The meaning of the closed regions.** A rule is enabled exactly when what it uses is present and
each region it queries holds exactly what the rule uses there. -/
theorem enabled_iff_filter (ρ : Rule R) (M : Multiset R) :
    ρ.Enabled M ↔ ρ.redex ≤ M ∧
      M.filter (fun x => ρ.closed x = true) = ρ.redex.filter (fun x => ρ.closed x = true) := by
  constructor
  · rintro ⟨sub, avoids⟩
    refine ⟨sub, ?_⟩
    have split : M = ρ.redex + (M - ρ.redex) := (add_tsub_cancel_of_le sub).symm
    rw [split, Multiset.filter_add, avoids_iff_filter.mp avoids, add_zero]
  · rintro ⟨sub, sameRegion⟩
    refine ⟨sub, avoids_iff_filter.mpr ?_⟩
    have split : M = ρ.redex + (M - ρ.redex) := (add_tsub_cancel_of_le sub).symm
    have := sameRegion
    rw [split, Multiset.filter_add] at this
    exact (add_eq_left.mp this)

/-- A positive rule is enabled exactly when what it uses is present. -/
theorem enabled_iff_of_positive {ρ : Rule R} (positive : ρ.Positive) (M : Multiset R) :
    ρ.Enabled M ↔ ρ.redex ≤ M :=
  ⟨fun e => e.1, fun sub => ⟨sub, fun x _ => positive x⟩⟩

/-- Firing at a bag that contains the redex: what is kept and made, plus the frame. -/
theorem result_eq_frame {ρ : Rule R} {M : Multiset R} (sub : ρ.redex ≤ M) :
    ρ.result M = (M - ρ.redex) + ρ.keep + ρ.make := by
  unfold result
  ext x
  have := Multiset.le_iff_count.mp sub x
  simp only [redex, Multiset.count_add, Multiset.count_sub] at *
  omega

end Rule

/-- Reduction in a closed system: some rule of `Γ` is enabled and fires. -/
def Reduces (Γ : Rule R → Prop) (M M' : Multiset R) : Prop :=
  ∃ ρ, Γ ρ ∧ ρ.Enabled M ∧ M' = ρ.result M

/-! ## Labels and the borrowed-context step -/

/-- A label: the context a step borrows and the regions the rest of the environment must avoid. -/
structure Label (R : Type u) where
  borrow : Multiset R
  closed : R → Bool

namespace Rule

/-- **The borrowed-context step of a rule.** Beside an environment that supplies `ℓ.borrow` and
whose rest avoids `ℓ.closed`, the bag `M` fires the rule and becomes `M'` (plus that rest). The
borrowed bag is the least one, what the rule uses and `M` lacks; the frame of `M` must avoid the
closed regions. -/
def Step (ρ : Rule R) (M : Multiset R) (ℓ : Label R) (M' : Multiset R) : Prop :=
  ℓ.borrow = ρ.redex - M ∧ ℓ.closed = ρ.closed ∧ Avoids (M - ρ.redex) ρ.closed ∧
    M' = ρ.result (M + ℓ.borrow)

variable {ρ : Rule R} {M M' : Multiset R} {J : Multiset R} {F : R → Bool}

/-- The step of a rule at a bag is determined: its label and its result. -/
theorem step_iff_enabled :
    ρ.Step M ⟨J, F⟩ M' ↔ J = ρ.redex - M ∧ F = ρ.closed ∧ ρ.Enabled (M + J) ∧
      M' = ρ.result (M + J) := by
  constructor
  · rintro ⟨hJ, hF, avoids, hM⟩
    subst hJ
    refine ⟨rfl, hF, ⟨?_, ?_⟩, hM⟩
    · exact le_add_label' M ρ.redex
    · rw [add_label_sub']; exact avoids
  · rintro ⟨hJ, hF, ⟨_, avoids⟩, hM⟩
    subst hJ
    refine ⟨rfl, hF, ?_, hM⟩
    rw [add_label_sub'] at avoids; exact avoids

/-- A rule has a step at every bag whose frame avoids its closed regions. -/
theorem step_of_frame (avoids : Avoids (M - ρ.redex) ρ.closed) :
    ρ.Step M ⟨ρ.redex - M, ρ.closed⟩ (ρ.result (M + (ρ.redex - M))) :=
  ⟨rfl, rfl, avoids, rfl⟩

/-- **The label is honoured by every environment that supplies it and avoids its condition**: in the
environment `J + E` with `E` avoiding `F`, the rule is enabled and fires to `M'` plus `E`. -/
theorem Step.enabled_with (step : ρ.Step M ⟨J, F⟩ M') {E : Multiset R} (avoidsE : Avoids E F) :
    ρ.Enabled (M + J + E) ∧ ρ.result (M + J + E) = M' + E := by
  obtain ⟨hJ, hF, avoids, hM⟩ := step
  simp only at hJ hF hM
  subst hJ hF hM
  refine ⟨⟨le_add_label M ρ.redex E, ?_⟩, ?_⟩
  · rw [add_label_sub]
    exact avoids_add.mpr ⟨avoids, avoidsE⟩
  · unfold result
    rw [result_add_frame ((ρ.take_le_redex).trans (le_add_label' M ρ.redex))]

/-- **And only those environments**: the label is the least context, and the rest of any enabling
environment avoids the closed regions. -/
theorem Enabled.least {C : Multiset R} (enabled : ρ.Enabled (M + C)) :
    ρ.redex - M ≤ C ∧ Avoids (M - ρ.redex) ρ.closed ∧ Avoids (C - (ρ.redex - M)) ρ.closed := by
  obtain ⟨sub, avoids⟩ := enabled
  rw [frame_split] at avoids
  exact ⟨label_le_add M C ρ.redex sub, (avoids_add.mp avoids).1, (avoids_add.mp avoids).2⟩

/-- **Steps characterize enabling in context.** The rule fires at `M` beside `C` exactly when `M`
has the rule's step, `C` supplies its label and the rest of `C` avoids its condition; the result is
the step's result plus that rest. -/
theorem enabled_with_iff {C : Multiset R} :
    ρ.Enabled (M + C) ↔ Avoids (M - ρ.redex) ρ.closed ∧ ρ.redex - M ≤ C ∧
      Avoids (C - (ρ.redex - M)) ρ.closed := by
  constructor
  · intro enabled
    obtain ⟨sub, frame, rest⟩ := enabled.least
    exact ⟨frame, sub, rest⟩
  · rintro ⟨frame, sub, rest⟩
    have step := step_of_frame frame
    have := (step.enabled_with rest).1
    rwa [add_assoc, add_tsub_cancel_of_le sub] at this

theorem result_with {C : Multiset R} (sub : ρ.redex - M ≤ C) :
    ρ.result (M + C) = ρ.result (M + (ρ.redex - M)) + (C - (ρ.redex - M)) := by
  unfold result
  have hC : M + C = M + (ρ.redex - M) + (C - (ρ.redex - M)) := by
    rw [add_assoc, add_tsub_cancel_of_le sub]
  rw [hC, result_add_frame ((ρ.take_le_redex).trans (le_add_label' M ρ.redex))]

/-- **Lifting a step into a context.** A step of `M` is a step of `M + C`: the context supplies
what it can of the label, and the part of `C` not borrowed must avoid the condition. -/
theorem Step.lift (step : ρ.Step M ⟨J, F⟩ M') {C : Multiset R} (avoidsRest : Avoids (C - J) F) :
    ρ.Step (M + C) ⟨J - C, F⟩ (M' + (C - J)) := by
  obtain ⟨hJ, hF, avoids, hM⟩ := step
  simp only at hJ hF hM
  subst hJ hF hM
  refine ⟨(sub_add_eq_sub_sub _ _ _).symm, rfl, ?_, ?_⟩
  · rw [frame_split]
    exact avoids_add.mpr ⟨avoids, avoidsRest⟩
  · simp only
    unfold result
    rw [lift_bag, result_add_frame ((ρ.take_le_redex).trans
      (le_add_label' M ρ.redex))]

/-- **Splitting a step out of a context.** Every step of `M + C` arises from the least step of `M`
by lifting. -/
theorem Step.split {C : Multiset R} {X : Multiset R} (step : ρ.Step (M + C) ⟨J, F⟩ X) :
    ρ.Step M ⟨ρ.redex - M, F⟩ (ρ.result (M + (ρ.redex - M))) ∧ J = (ρ.redex - M) - C ∧
      Avoids (C - (ρ.redex - M)) F ∧ X = ρ.result (M + (ρ.redex - M)) + (C - (ρ.redex - M)) := by
  obtain ⟨hJ, hF, avoids, hX⟩ := step
  simp only at hJ hF hX
  subst hJ hF hX
  rw [frame_split] at avoids
  refine ⟨⟨rfl, rfl, (avoids_add.mp avoids).1, rfl⟩, sub_add_eq_sub_sub _ _ _,
    (avoids_add.mp avoids).2, ?_⟩
  unfold result
  rw [sub_add_eq_sub_sub, lift_bag, result_add_frame ((ρ.take_le_redex).trans
    (le_add_label' M ρ.redex))]

/-- **A step holds in every larger environment exactly when its rule is positive.** A rule that
queries a region has, for any label in that region, an environment that supplies the borrowed
context and still disables it. -/
theorem step_unconditional_iff (step : ρ.Step M ⟨J, F⟩ M') :
    (∀ E : Multiset R, ρ.Enabled (M + J + E)) ↔ ρ.Positive := by
  constructor
  · intro always x
    cases hx : ρ.closed x
    · rfl
    · exfalso
      obtain ⟨hJ, -, -, -⟩ := step
      simp only at hJ
      subst hJ
      have := (always {x}).2
      rw [add_label_sub] at this
      have := this x (Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self x)))
      rw [hx] at this
      exact absurd this (by decide)
  · intro positive E
    exact (step.enabled_with (F := F) (fun x _ => by
      obtain ⟨-, hF, -, -⟩ := step
      simp only at hF
      rw [hF]
      exact positive x)).1

open CategoryTheory in
/-- **The label is the Leifer–Milner least label.** The square `M + J = redex + frame` is an idem
pushout in the category of bag contexts: its legs, the borrowed context and the frame, share
nothing. -/
theorem label_isIdemPushout (ρ : Rule R) (M : Multiset R) :
    Mettapedia.GSLT.RelativePushout.IsIdemPushout
      (Mettapedia.GSLT.BagRelativePushout.bag M) (Mettapedia.GSLT.BagRelativePushout.bag ρ.redex)
      (Mettapedia.GSLT.BagRelativePushout.bag (ρ.redex - M))
      (Mettapedia.GSLT.BagRelativePushout.bag (M - ρ.redex))
      (by rw [Mettapedia.GSLT.BagRelativePushout.bag_comp,
            Mettapedia.GSLT.BagRelativePushout.bag_comp, label_square]) :=
  Mettapedia.GSLT.BagRelativePushout.isIdemPushout_bag _ _ _ _ _ (label_frame_inter M ρ.redex)

end Rule

/-- The borrowed-context transition system of a rule set. -/
def BStep (Γ : Rule R → Prop) (M : Multiset R) (ℓ : Label R) (M' : Multiset R) : Prop :=
  ∃ ρ, Γ ρ ∧ ρ.Step M ℓ M'

/-- **Reduction is the step that borrows nothing.** -/
theorem reduces_iff_step_zero {Γ : Rule R → Prop} {M M' : Multiset R} :
    Reduces Γ M M' ↔ ∃ F, BStep Γ M ⟨0, F⟩ M' := by
  constructor
  · rintro ⟨ρ, member, enabled, rfl⟩
    refine ⟨ρ.closed, ρ, member, ?_⟩
    have hJ : ρ.redex - M = 0 := tsub_eq_zero_of_le enabled.1
    exact ⟨hJ.symm, rfl, enabled.2, by simp⟩
  · rintro ⟨F, ρ, member, step⟩
    obtain ⟨hJ, hF, enabled, hM⟩ := Rule.step_iff_enabled.mp step
    exact ⟨ρ, member, by simpa using enabled, by simpa using hM⟩

/-- A step that borrows nothing, beside a rest that avoids its condition, is a reduction of the whole. -/
theorem BStep.reduces_with {Γ : Rule R → Prop} {M M' E : Multiset R} {F : R → Bool}
    (step : BStep Γ M ⟨0, F⟩ M') (avoids : Avoids E F) : Reduces Γ (M + E) (M' + E) := by
  obtain ⟨ρ, member, step⟩ := step
  obtain ⟨enabled, result⟩ := step.enabled_with avoids
  exact ⟨ρ, member, by simpa using enabled, by simpa using result.symm⟩

/-! ## Controls -/

namespace Controls

/-- A token, a lock, and an output. -/
inductive Atom where
  | tok
  | lock
  | out
  deriving DecidableEq, Repr

open Atom

/-- The region of locks. -/
def isLock : Atom → Bool
  | lock => true
  | _ => false

/-- Read the token, make an output. -/
def reader : Rule Atom := ⟨0, {tok}, {out}, fun _ => false⟩

/-- Make an output when no lock is present. -/
def unlessLocked : Rule Atom := ⟨0, 0, {out}, isLock⟩

/-- Positive control: parked at the empty bag, the reader borrows the token and nothing else, with no
condition on the rest of the environment. -/
theorem reader_label :
    reader.Step 0 ⟨{tok}, fun _ => false⟩ {tok, out} ∧ reader.Positive :=
  ⟨⟨by decide, rfl, avoids_zero _, by decide⟩, fun _ => rfl⟩

/-- **The absence step borrows nothing and reports the lock's region.** -/
theorem absence_label : unlessLocked.Step 0 ⟨0, isLock⟩ {out} :=
  ⟨by decide, rfl, avoids_zero _, by decide⟩

/-- **Negative control: beside a lock the absence step does not fire.** The rest of the environment
does not avoid the reported region. Once the environment's own step removes the lock, the step fires
beside what is left. -/
theorem absence_blocked_by_lock :
    ¬ unlessLocked.Enabled (0 + 0 + {lock}) ∧ unlessLocked.Enabled (0 + 0 + 0) := by
  refine ⟨fun enabled => ?_, (absence_label.enabled_with (avoids_zero _)).1⟩
  have := enabled.2 lock (by decide)
  exact absurd this (by decide)

/-- The absence step is not unconditional: its rule is not positive. -/
theorem absence_conditional : ¬ unlessLocked.Positive := fun positive => by
  have := positive lock
  exact absurd this (by decide)

/-- **Step, negative**: parked beside a lock, the absence rule has no step with the lock's region
as its condition: the rest of the environment does not avoid it. (`absence_label` is the positive
control.) -/
theorem absence_step_blocked_by_lock :
    ¬ unlessLocked.Step ({lock} : Multiset Atom) ⟨0, isLock⟩ {lock, out} := fun step =>
  absurd step.2.2.1 (by decide)

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence
