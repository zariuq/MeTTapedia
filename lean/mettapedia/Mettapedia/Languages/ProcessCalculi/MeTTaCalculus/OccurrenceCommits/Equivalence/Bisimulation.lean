import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.BorrowedSteps
import Mettapedia.Languages.MeTTa.TransformComposition

/-!
# Bisimulation over borrowed contexts, contextual equivalence, and where they differ

Over the borrowed-context transition system of `BorrowedSteps` this module defines two
equivalences and compares them.

## The parameters

* `Γ`, the rule set: every ground commit the program text allows.
* `Adm`, the **admissible** labels: what an environment may place beside a program. This is where
  rights enter. Contexts that hold only some names supply only labels at those names; a restricted
  name `ν n` is a name no admissible label mentions. Every result below is relative to `Adm`.
* `obs`, the **barbs**: a family of observable regions; a bag shows barb `i` when one of its labels
  lies in `obs i` (one barb per public channel, for instance).

## Contextual equivalence

`Contextual Γ Adm obs` is reduction-closed barbed congruence: the largest symmetric relation that
preserves barbs, matches each reduction by a reduction, and is closed under adding any admissible
context (`IsContextual`). It is the meaning of "no admissible environment can tell them apart". With
every label admissible and no barbs it is the saturated bisimilarity of the 10/25 composition
module, for the reduction relation of the rules (`contextual_iff_saturated`).

## The labelled bisimulation

`Bisimilar Γ Adm obs` plays only the borrowed-context steps. A challenge is a labelled step
`M —(J, F)→ M'` with an admissible label; the answer is a step of `N + J` that borrows nothing
more, under a condition `G` weaker than `F` on admissible labels, to some `N'` related to `M'`
(`IsBisimulation`). The challenger's labels are the least contexts; the answerer may use any rule
the supplied context enables (the semi-saturated game of Bonchi, König and Montanari), and its
condition must hold wherever the challenger's does.

* **It is an equivalence** (`bisimilar_refl`, `Bisimilar.symm`, `Bisimilar.trans`).
* **It is a congruence for parallel composition with admissible contexts**
  (`Bisimilar.add_context`), for every rule set, predicate queries included.
* **It is antitone in the admissible class and the barbs** (`Bisimilar.restrict`): fewer
  environments, or fewer observations, can only identify more. Restriction of a name and contexts
  scoped to a set of rights are admissible classes, so this is congruence for `ν` and for
  region-scoped contexts.
* **It is sound** (`contextual_of_bisimilar`): bisimilar bags are contextually equivalent; it refines
  the saturated bisimilarity of the composition module (`saturatedBisimilar_of_bisimilar`).
* **It is complete on the positive fragment** (`bisimilar_iff_contextual_of_positive`): when no
  rule has a predicate query, the least labels lose nothing.
* **It is the largest conditional congruence** (`bisimilar_iff_conditional`): the largest
  symmetric, barb-preserving relation closed under admissible contexts that matches every
  reduction *valid beside any rest avoiding its condition* by one under a weaker condition.
  Contextual equivalence is the same with closed reductions, which carry no condition; so the two
  differ exactly by the comparison of conditions.

## Absence and predicate queries: what a label must report

Predicate queries are not monotone: an occurrence added beside a program can disable its step. Two
consequences:

* **A label must report the closed regions.** If the answer's condition is not compared with the
  challenger's, the resulting "bisimilarity" relates a plain step with an absence-guarded one and is
  not preserved by adding the guarded region's label (`Gaps`, `Controls.blind_not_congruence`). The
  condition is a negative application condition on the rest of the environment, as in the borrowed
  contexts with negative conditions of Rangel, König and Ehrig.
* **A label need not report removals.** An absence step woken by a removal is the environment's
  own step followed by the program's labelled step, whose condition is checked against the
  environment as it is then (`BorrowedSteps`, `Controls.absence_blocked_by_lock`). The congruence
  proof splits every step of a composite into the least step of one side (`Rule.Step.split`), so a
  removal in the context is a step of the composite like any other.

## The gap, with predicate queries

Completeness fails once rules have predicate queries (`Gaps`, `Controls.else_gap`): a choice that
fires one branch when `x` is absent and the other, reading `x`, when it is present, both making `q`,
is contextually equivalent to a plain step to `q`, and not bisimilar to it. To answer the plain
step's unconditional label, the guarded side must decide the predicate query, and either branch
alone carries a condition (absence of `x`) or a borrowing (`x` itself) the challenger did not have.
A complete game must let the answer depend on the environment beyond the label; this is the
saturated game, which the minimal labels refine but do not replace.

Matching labels literally (answering with the same label from the answerer's own transitions, as
Leifer and Milner do) is incomplete even without predicate queries (`Gaps`,
`Controls.catalyst_gap`): a rule that uses a catalyst has a label the other side never shows, though
every environment sees the same reductions.

## The 10/25 join

A lone `a` and the empty bag are bisimilar for the plain reaction relation (composition module,
`bisimilarity_not_congruence`). They are neither contextually equivalent nor bisimilar here: beside
`b` the first reacts and the second does not (`Controls.join_separated`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence

universe u v

variable {R : Type u} [DecidableEq R]

/-! ## Transition-system lemmas -/

section Steps

variable {Γ : Rule R → Prop}

/-- A labelled step, lifted into a context. -/
theorem BStep.lift {M M' J : Multiset R} {F : R → Bool} (step : BStep Γ M ⟨J, F⟩ M')
    {C : Multiset R} (avoids : Avoids (C - J) F) :
    BStep Γ (M + C) ⟨J - C, F⟩ (M' + (C - J)) := by
  obtain ⟨ρ, member, step⟩ := step
  exact ⟨ρ, member, step.lift avoids⟩

/-- A labelled step, with its borrowed context supplied: a step that borrows nothing. -/
theorem BStep.absorb {M M' J : Multiset R} {F : R → Bool} (step : BStep Γ M ⟨J, F⟩ M') :
    BStep Γ (M + J) ⟨0, F⟩ M' := by
  have := step.lift (C := J) (by simp)
  simpa using this

/-- A step that borrows nothing, lifted beside a rest that avoids its condition. -/
theorem BStep.lift_zero {M M' : Multiset R} {F : R → Bool} (step : BStep Γ M ⟨0, F⟩ M')
    {C : Multiset R} (avoids : Avoids C F) : BStep Γ (M + C) ⟨0, F⟩ (M' + C) := by
  have := step.lift (C := C) (by simpa using avoids)
  simpa using this

/-- A labelled step of a composite, split into the least step of one side. -/
theorem BStep.split {M C X J : Multiset R} {F : R → Bool} (step : BStep Γ (M + C) ⟨J, F⟩ X) :
    ∃ JM M', BStep Γ M ⟨JM, F⟩ M' ∧ J = JM - C ∧ Avoids (C - JM) F ∧ X = M' + (C - JM) := by
  obtain ⟨ρ, member, step⟩ := step
  obtain ⟨least, hJ, avoids, hX⟩ := step.split
  exact ⟨_, _, ⟨ρ, member, least⟩, hJ, avoids, hX⟩

end Steps

/-! ## Admissible contexts, conditions and barbs -/

/-- A bag the environment can supply: every label admissible. -/
def Admissible (Adm : R → Prop) (C : Multiset R) : Prop := ∀ x ∈ C, Adm x

omit [DecidableEq R] in
@[simp] theorem admissible_zero (Adm : R → Prop) : Admissible Adm (0 : Multiset R) := by
  intro x member; simp at member

omit [DecidableEq R] in
theorem Admissible.mono {Adm : R → Prop} {A B : Multiset R} (sub : A ≤ B) (adm : Admissible Adm B) :
    Admissible Adm A := fun x member => adm x (Multiset.mem_of_le sub member)

omit [DecidableEq R] in
theorem admissible_add {Adm : R → Prop} {A B : Multiset R} :
    Admissible Adm (A + B) ↔ Admissible Adm A ∧ Admissible Adm B := by
  simp only [Admissible, Multiset.mem_add]
  exact ⟨fun h => ⟨fun x m => h x (Or.inl m), fun x m => h x (Or.inr m)⟩,
    fun h x m => m.elim (h.1 x) (h.2 x)⟩

theorem Admissible.sub {Adm : R → Prop} {A : Multiset R} (adm : Admissible Adm A) (B : Multiset R) :
    Admissible Adm (A - B) := adm.mono (Multiset.sub_le_self _ _)

/-- A condition `G` is weaker than `F` on admissible labels: every admissible label `G` closes, `F`
closes too. So an admissible environment that avoids `F` avoids `G`. -/
def Weaker (Adm : R → Prop) (G F : R → Bool) : Prop := ∀ x, Adm x → G x = true → F x = true

omit [DecidableEq R] in
theorem Weaker.refl (Adm : R → Prop) (F : R → Bool) : Weaker Adm F F := fun _ _ h => h

omit [DecidableEq R] in
theorem Weaker.trans {Adm : R → Prop} {H G F : R → Bool} (first : Weaker Adm H G)
    (second : Weaker Adm G F) : Weaker Adm H F := fun x adm h => second x adm (first x adm h)

omit [DecidableEq R] in
theorem Weaker.avoids {Adm : R → Prop} {G F : R → Bool} (weaker : Weaker Adm G F) {C : Multiset R}
    (adm : Admissible Adm C) (avoids : Avoids C F) : Avoids C G :=
  avoids.weaken fun x member h => weaker x (adm x member) h

omit [DecidableEq R] in
theorem Weaker.mono {Adm Adm' : R → Prop} (sub : ∀ x, Adm' x → Adm x) {G F : R → Bool}
    (weaker : Weaker Adm G F) : Weaker Adm' G F := fun x adm h => weaker x (sub x adm) h

omit [DecidableEq R] in
/-- The empty condition is weaker than every condition. -/
theorem weaker_none (Adm : R → Prop) (F : R → Bool) : Weaker Adm (fun _ => false) F :=
  fun _ _ h => by simp at h

/-- A bag shows a barb: one of its labels lies in the observable region. -/
def Barb (region : R → Prop) (M : Multiset R) : Prop := ∃ x ∈ M, region x

omit [DecidableEq R] in
theorem barb_add {region : R → Prop} {M C : Multiset R} :
    Barb region (M + C) ↔ Barb region M ∨ Barb region C := by
  simp only [Barb, Multiset.mem_add]
  constructor
  · rintro ⟨x, member | member, h⟩
    · exact Or.inl ⟨x, member, h⟩
    · exact Or.inr ⟨x, member, h⟩
  · rintro (⟨x, member, h⟩ | ⟨x, member, h⟩)
    · exact ⟨x, Or.inl member, h⟩
    · exact ⟨x, Or.inr member, h⟩

/-! ## The labelled bisimulation -/

section Game

variable (Γ : Rule R → Prop) (Adm : R → Prop) {ι : Type v} (obs : ι → R → Prop)

/-- **A bisimulation over borrowed contexts.** Symmetric; preserves every barb; a challenge is a
labelled step with an admissible label, answered by a step of the other side beside the borrowed
context that borrows nothing more, under a weaker condition. -/
structure IsBisimulation (B : Multiset R → Multiset R → Prop) : Prop where
  symm : ∀ ⦃M N⦄, B M N → B N M
  barb : ∀ ⦃M N⦄, B M N → ∀ i, Barb (obs i) M → Barb (obs i) N
  step : ∀ ⦃M N⦄, B M N → ∀ ⦃J F M'⦄, Admissible Adm J → BStep Γ M ⟨J, F⟩ M' →
    ∃ G N', Weaker Adm G F ∧ BStep Γ (N + J) ⟨0, G⟩ N' ∧ B M' N'

/-- Bisimilar: related by some bisimulation. -/
def Bisimilar (M N : Multiset R) : Prop := ∃ B, IsBisimulation Γ Adm obs B ∧ B M N

/-- **Contextual equivalence**: reduction-closed barbed congruence for admissible contexts. -/
structure IsContextual (B : Multiset R → Multiset R → Prop) : Prop where
  symm : ∀ ⦃M N⦄, B M N → B N M
  barb : ∀ ⦃M N⦄, B M N → ∀ i, Barb (obs i) M → Barb (obs i) N
  reduce : ∀ ⦃M N⦄, B M N → ∀ ⦃M'⦄, Reduces Γ M M' → ∃ N', Reduces Γ N N' ∧ B M' N'
  context : ∀ ⦃M N⦄, B M N → ∀ ⦃C⦄, Admissible Adm C → B (M + C) (N + C)

/-- Contextually equivalent: related by some contextual relation. -/
def Contextual (M N : Multiset R) : Prop := ∃ B, IsContextual Γ Adm obs B ∧ B M N

end Game

section Theory

variable {Γ : Rule R → Prop} {Adm : R → Prop} {ι : Type v} {obs : ι → R → Prop}

/-- Equality is a bisimulation. -/
theorem isBisimulation_eq : IsBisimulation Γ Adm obs (· = ·) where
  symm := fun _ _ h => h.symm
  barb := by rintro M N rfl i h; exact h
  step := by
    rintro M N rfl J F M' _ step
    exact ⟨F, M', Weaker.refl _ _, step.absorb, rfl⟩

theorem bisimilar_refl (M : Multiset R) : Bisimilar Γ Adm obs M M := ⟨_, isBisimulation_eq, rfl⟩

theorem Bisimilar.symm {M N : Multiset R} (h : Bisimilar Γ Adm obs M N) : Bisimilar Γ Adm obs N M := by
  obtain ⟨B, bisim, related⟩ := h
  exact ⟨B, bisim, bisim.symm related⟩

/-- Bisimilarity is itself a bisimulation. -/
theorem isBisimulation_bisimilar : IsBisimulation Γ Adm obs (Bisimilar Γ Adm obs) where
  symm := fun _ _ h => h.symm
  barb := by
    rintro M N ⟨B, bisim, related⟩
    exact bisim.barb related
  step := by
    rintro M N ⟨B, bisim, related⟩ J F M' adm step
    obtain ⟨G, N', weaker, answer, related'⟩ := bisim.step related adm step
    exact ⟨G, N', weaker, answer, B, bisim, related'⟩

/-- **Bisimilarity is a congruence for parallel composition with admissible contexts.** -/
theorem Bisimilar.add_context {M N : Multiset R} (h : Bisimilar Γ Adm obs M N) {C : Multiset R}
    (adm : Admissible Adm C) : Bisimilar Γ Adm obs (M + C) (N + C) := by
  refine ⟨fun X Y => ∃ M₀ N₀ C₀, Bisimilar Γ Adm obs M₀ N₀ ∧ Admissible Adm C₀ ∧
      X = M₀ + C₀ ∧ Y = N₀ + C₀, ⟨?_, ?_, ?_⟩, ⟨M, N, C, h, adm, rfl, rfl⟩⟩
  · rintro X Y ⟨M₀, N₀, C₀, similar, adm₀, rfl, rfl⟩
    exact ⟨N₀, M₀, C₀, similar.symm, adm₀, rfl, rfl⟩
  · rintro X Y ⟨M₀, N₀, C₀, similar, adm₀, rfl, rfl⟩ i shows
    rcases barb_add.mp shows with left | right
    · exact barb_add.mpr (Or.inl (isBisimulation_bisimilar.barb similar i left))
    · exact barb_add.mpr (Or.inr right)
  · rintro X Y ⟨M₀, N₀, C₀, similar, adm₀, rfl, rfl⟩ J F X' admJ step
    obtain ⟨JM, M', least, hJ, avoidsRest, hX⟩ := step.split
    subst hJ hX
    -- The least label of `M₀` is supplied by the context and the label together.
    have leJM : JM ≤ C₀ + (JM - C₀) := by
      rw [Multiset.le_iff_count]; intro x
      simp only [Multiset.count_add, Multiset.count_sub]; omega
    have admJM : Admissible Adm JM := (admissible_add.mpr ⟨adm₀, admJ⟩).mono leJM
    obtain ⟨G, N', weaker, answer, related⟩ := isBisimulation_bisimilar.step similar admJM least
    have admRest : Admissible Adm (C₀ - JM) := adm₀.sub JM
    have lifted := answer.lift_zero (weaker.avoids admRest avoidsRest)
    have bag : N₀ + JM + (C₀ - JM) = N₀ + C₀ + (JM - C₀) := by
      ext x; simp only [Multiset.count_add, Multiset.count_sub]; omega
    rw [bag] at lifted
    exact ⟨G, N' + (C₀ - JM), weaker, lifted, M', N', C₀ - JM, related, admRest, rfl, rfl⟩

/-- **Bisimilarity is transitive.** -/
theorem Bisimilar.trans {M N P : Multiset R} (first : Bisimilar Γ Adm obs M N)
    (second : Bisimilar Γ Adm obs N P) : Bisimilar Γ Adm obs M P := by
  refine ⟨fun X Z => ∃ Y, Bisimilar Γ Adm obs X Y ∧ Bisimilar Γ Adm obs Y Z, ⟨?_, ?_, ?_⟩,
    ⟨N, first, second⟩⟩
  · rintro X Z ⟨Y, xy, yz⟩
    exact ⟨Y, yz.symm, xy.symm⟩
  · rintro X Z ⟨Y, xy, yz⟩ i shows
    exact isBisimulation_bisimilar.barb yz i (isBisimulation_bisimilar.barb xy i shows)
  · rintro X Z ⟨Y, xy, yz⟩ J F X' admJ step
    obtain ⟨G, Y', weakerG, answerY, relatedXY⟩ := isBisimulation_bisimilar.step xy admJ step
    obtain ⟨JY, Y₁, leastY, hJY, avoidsY, hY'⟩ := answerY.split
    have leJY : JY ≤ J := by
      rw [Multiset.le_iff_count]; intro x
      have := congrArg (Multiset.count x) hJY
      simp only [Multiset.count_sub, Multiset.count_zero] at this; omega
    have admJY : Admissible Adm JY := admJ.mono leJY
    obtain ⟨H, Z₁, weakerH, answerZ, relatedYZ⟩ := isBisimulation_bisimilar.step yz admJY leastY
    have admRest : Admissible Adm (J - JY) := admJ.sub JY
    have lifted := answerZ.lift_zero (weakerH.avoids admRest avoidsY)
    have bag : Z + JY + (J - JY) = Z + J := by
      rw [add_assoc, add_tsub_cancel_of_le leJY]
    rw [bag] at lifted
    refine ⟨H, Z₁ + (J - JY), weakerH.trans weakerG, lifted, Y', relatedXY, ?_⟩
    rw [hY']
    exact relatedYZ.add_context admRest

/-- **Antitone in the admissible class and the barbs.** A bisimulation for more environments and
more barbs is one for fewer: restriction of a name and region-scoped contexts only identify more. -/
theorem IsBisimulation.restrict {B : Multiset R → Multiset R → Prop} (bisim : IsBisimulation Γ Adm obs B)
    {Adm' : R → Prop} (subAdm : ∀ x, Adm' x → Adm x) {ι' : Type v} (barbs : ι' → ι) :
    IsBisimulation Γ Adm' (fun i => obs (barbs i)) B where
  symm := bisim.symm
  barb := fun _ _ related i => bisim.barb related (barbs i)
  step := by
    intro M N related J F M' adm step
    obtain ⟨G, N', weaker, answer, related'⟩ :=
      bisim.step related (fun x member => subAdm x (adm x member)) step
    exact ⟨G, N', weaker.mono subAdm, answer, related'⟩

theorem Bisimilar.restrict {M N : Multiset R} (h : Bisimilar Γ Adm obs M N) {Adm' : R → Prop}
    (subAdm : ∀ x, Adm' x → Adm x) {ι' : Type v} (barbs : ι' → ι) :
    Bisimilar Γ Adm' (fun i => obs (barbs i)) M N := by
  obtain ⟨B, bisim, related⟩ := h
  exact ⟨B, bisim.restrict subAdm barbs, related⟩

/-- Contextual equivalence is itself contextual. -/
theorem isContextual_contextual : IsContextual Γ Adm obs (Contextual Γ Adm obs) where
  symm := by
    rintro M N ⟨B, ctx, related⟩
    exact ⟨B, ctx, ctx.symm related⟩
  barb := by
    rintro M N ⟨B, ctx, related⟩
    exact ctx.barb related
  reduce := by
    rintro M N ⟨B, ctx, related⟩ M' reduces
    obtain ⟨N', reducesN, related'⟩ := ctx.reduce related reduces
    exact ⟨N', reducesN, B, ctx, related'⟩
  context := by
    rintro M N ⟨B, ctx, related⟩ C adm
    exact ⟨B, ctx, ctx.context related adm⟩

/-- **Soundness.** Bisimilar bags are contextually equivalent. -/
theorem contextual_of_bisimilar {M N : Multiset R} (h : Bisimilar Γ Adm obs M N) :
    Contextual Γ Adm obs M N := by
  refine ⟨Bisimilar Γ Adm obs, ⟨fun _ _ h => h.symm, ?_, ?_, fun _ _ h _ adm => h.add_context adm⟩, h⟩
  · exact isBisimulation_bisimilar.barb
  · intro M N similar M' reduces
    obtain ⟨F, step⟩ := reduces_iff_step_zero.mp reduces
    obtain ⟨G, N', -, answer, related⟩ := isBisimulation_bisimilar.step similar (admissible_zero Adm) step
    exact ⟨N', reduces_iff_step_zero.mpr ⟨G, by simpa using answer⟩, related⟩

/-- A rule set is positive when none of its rules has a predicate query. -/
def PositiveRules (Γ : Rule R → Prop) : Prop := ∀ ρ, Γ ρ → ρ.Positive

/-- **Completeness on the positive fragment.** Without predicate queries, contextually equivalent
bags are bisimilar: the least labels lose nothing. -/
theorem bisimilar_of_contextual (positive : PositiveRules Γ) {M N : Multiset R}
    (h : Contextual Γ Adm obs M N) : Bisimilar Γ Adm obs M N := by
  refine ⟨Contextual Γ Adm obs, ⟨isContextual_contextual.symm, isContextual_contextual.barb, ?_⟩, h⟩
  intro M N equivalent J F M' adm step
  have inContext := isContextual_contextual.context equivalent adm
  obtain ⟨N', reducesN, related⟩ := isContextual_contextual.reduce inContext
    (reduces_iff_step_zero.mpr ⟨F, step.absorb⟩)
  obtain ⟨ρ, member, enabled, rfl⟩ := reducesN
  refine ⟨ρ.closed, ρ.result (N + J), fun x _ h => ?_, ?_, related⟩
  · rw [positive ρ member x] at h; exact absurd h (by decide)
  · exact ⟨ρ, member, (tsub_eq_zero_of_le enabled.1).symm, rfl, enabled.2, by simp⟩

theorem bisimilar_iff_contextual_of_positive (positive : PositiveRules Γ) {M N : Multiset R} :
    Bisimilar Γ Adm obs M N ↔ Contextual Γ Adm obs M N :=
  ⟨contextual_of_bisimilar, bisimilar_of_contextual positive⟩

/-! ## A characterization: the congruence that matches conditional reductions -/

variable (Γ Adm obs) in
/-- **A conditional congruence**: symmetric, preserves barbs, closed under admissible contexts, and
matches each step that borrows nothing (a reduction valid beside any rest avoiding its condition) by
such a step under a weaker condition. Contextual equivalence asks the same with closed reductions
only, which carry no condition to compare. -/
structure IsConditional (B : Multiset R → Multiset R → Prop) : Prop where
  symm : ∀ ⦃M N⦄, B M N → B N M
  barb : ∀ ⦃M N⦄, B M N → ∀ i, Barb (obs i) M → Barb (obs i) N
  step : ∀ ⦃M N F M'⦄, B M N → BStep Γ M ⟨0, F⟩ M' →
    ∃ G N', Weaker Adm G F ∧ BStep Γ N ⟨0, G⟩ N' ∧ B M' N'
  context : ∀ ⦃M N⦄, B M N → ∀ ⦃C⦄, Admissible Adm C → B (M + C) (N + C)

/-- A conditional congruence is contained in bisimilarity. -/
theorem bisimilar_of_conditional {B : Multiset R → Multiset R → Prop} (cond : IsConditional Γ Adm obs B)
    {M N : Multiset R} (related : B M N) : Bisimilar Γ Adm obs M N := by
  refine ⟨B, ⟨cond.symm, cond.barb, ?_⟩, related⟩
  intro M N rel J F M' adm step
  exact cond.step (cond.context rel adm) step.absorb

/-- **Bisimilarity over borrowed contexts is the largest conditional congruence.** -/
theorem bisimilar_iff_conditional {M N : Multiset R} :
    Bisimilar Γ Adm obs M N ↔ ∃ B, IsConditional Γ Adm obs B ∧ B M N := by
  refine ⟨fun h => ⟨Bisimilar Γ Adm obs, ⟨fun _ _ h => h.symm, isBisimulation_bisimilar.barb, ?_,
    fun _ _ h _ adm => h.add_context adm⟩, h⟩, fun ⟨B, cond, related⟩ => bisimilar_of_conditional cond related⟩
  intro M N F M' similar step
  obtain ⟨G, N', weaker, answer, related⟩ := isBisimulation_bisimilar.step similar (admissible_zero Adm) step
  exact ⟨G, N', weaker, by simpa using answer, related⟩

end Theory

/-! ## Against the saturated bisimilarity of the composition module -/

section Saturated

open Mettapedia.Languages.MeTTa.TransformComposition

variable {Γ : Rule R → Prop} {ι : Type v} {obs : ι → R → Prop}

/-- **The least labels refine the saturated game.** With every label admissible, bisimilarity over
borrowed contexts implies saturated bisimilarity of the reduction relation, which quantifies over
every context at every step. -/
theorem saturatedBisimilar_of_bisimilar {M N : Multiset R}
    (h : Bisimilar Γ (fun _ => True) obs M N) : SaturatedBisimilar (Reduces Γ) M N := by
  refine ⟨Bisimilar Γ (fun _ => True) obs, ?_, h⟩
  have half : ∀ X Y, Bisimilar Γ (fun _ => True) obs X Y → ∀ J X', Saturated (Reduces Γ) X J X' →
      ∃ Y', Saturated (Reduces Γ) Y J Y' ∧ Bisimilar Γ (fun _ => True) obs X' Y' := by
    intro X Y similar J X' reduces
    unfold Saturated at reduces ⊢
    obtain ⟨F, step⟩ := reduces_iff_step_zero.mp reduces
    obtain ⟨JX, X₁, least, hJ, avoids, hX⟩ := step.split
    have leJX : JX ≤ J := by
      rw [Multiset.le_iff_count]; intro x
      have := congrArg (Multiset.count x) hJ
      simp only [Multiset.count_sub, Multiset.count_zero] at this; omega
    obtain ⟨G, Y₁, weaker, answer, related⟩ :=
      isBisimulation_bisimilar.step similar (fun _ _ => trivial) least
    have lifted := answer.lift_zero (weaker.avoids (fun _ _ => trivial) avoids)
    rw [add_assoc, add_tsub_cancel_of_le leJX] at lifted
    refine ⟨Y₁ + (J - JX), reduces_iff_step_zero.mpr ⟨G, lifted⟩, ?_⟩
    rw [hX]
    exact related.add_context (fun _ _ => trivial)
  intro X Y similar J
  exact ⟨half X Y similar J, fun Y' stepY => by
    obtain ⟨X', stepX, related⟩ := half Y X similar.symm J Y' stepY
    exact ⟨X', stepX, related.symm⟩⟩

/-- **With every label admissible and no barbs, contextual equivalence is the saturated
bisimilarity** of the reduction relation. -/
theorem contextual_iff_saturated {M N : Multiset R} :
    Contextual Γ (fun _ => True) (Empty.elim : Empty → R → Prop) M N ↔
      SaturatedBisimilar (Reduces Γ) M N := by
  constructor
  · rintro ⟨B, ctx, related⟩
    refine ⟨B, fun X Y relXY J => ⟨fun X' stepX => ?_, fun Y' stepY => ?_⟩, related⟩
    · obtain ⟨Y', stepY, rel⟩ := ctx.reduce (ctx.context relXY (fun _ _ => trivial)) stepX
      exact ⟨Y', stepY, rel⟩
    · obtain ⟨X', stepX, rel⟩ := ctx.reduce (ctx.symm (ctx.context relXY (fun _ _ => trivial))) stepY
      exact ⟨X', stepX, ctx.symm rel⟩
  · intro h
    refine ⟨SaturatedBisimilar (Reduces Γ), ⟨?_, fun _ _ _ i => i.elim, ?_, ?_⟩, h⟩
    · rintro X Y ⟨B, bisim, related⟩
      refine ⟨fun P Q => B Q P, fun P Q relPQ J => ⟨fun P' stepP => ?_, fun Q' stepQ => ?_⟩, related⟩
      · obtain ⟨Q', stepQ, rel⟩ := (bisim Q P relPQ J).2 P' stepP
        exact ⟨Q', stepQ, rel⟩
      · obtain ⟨P', stepP, rel⟩ := (bisim Q P relPQ J).1 Q' stepQ
        exact ⟨P', stepP, rel⟩
    · rintro X Y ⟨B, bisim, related⟩ X' reduces
      obtain ⟨Y', stepY, rel⟩ := (bisim X Y related 0).1 X' (by unfold Saturated; simpa using reduces)
      exact ⟨Y', by unfold Saturated at stepY; simpa using stepY, B, bisim, rel⟩
    · intro X Y similar C _
      exact saturated_congruence (Reduces Γ) similar C

end Saturated

/-! ## Controls -/

namespace Controls

/-! ### The 10/25 join -/

section Join

open Mettapedia.Languages.MeTTa.TransformComposition
open Mettapedia.Languages.MeTTa.TransformComposition.JoinAtom

/-- The join as a rule: take `a` and `b`, make `c`. -/
def joinRule : Rule JoinAtom := ⟨{a, b}, 0, {c}, fun _ => false⟩

/-- The rule set with the join alone. -/
def joinRules : Rule JoinAtom → Prop := fun ρ => ρ = joinRule

/-- The reduction relation of the join rule is the composition module's `joinStep`. -/
theorem reduces_join_iff (M N : Multiset JoinAtom) : Reduces joinRules M N ↔ joinStep M N := by
  constructor
  · rintro ⟨ρ, rfl, ⟨sub, -⟩, rfl⟩
    exact ⟨by simpa [joinRule, Rule.redex] using sub, by simp [joinRule, Rule.result]⟩
  · rintro ⟨sub, rfl⟩
    exact ⟨joinRule, rfl, ⟨by simpa [joinRule, Rule.redex] using sub, fun _ _ => rfl⟩,
      by simp [joinRule, Rule.result]⟩

/-- **The 10/25 counterexample, separated.** A lone `a` and the empty bag are bisimilar for the
plain reaction relation, and they are neither contextually equivalent nor bisimilar over borrowed
contexts, for any admissible class containing `b` and any barbs. -/
theorem join_separated {ι : Type v} (obs : ι → JoinAtom → Prop) (Adm : JoinAtom → Prop) (admB : Adm b) :
    Mettapedia.Languages.MeTTa.TransformComposition.Bisimilar joinStep {a} 0 ∧ ¬ Contextual joinRules Adm obs {a} 0 ∧
      ¬ Bisimilar joinRules Adm obs {a} 0 := by
  have notCtx : ¬ Contextual joinRules Adm obs {a} 0 := by
    rintro ⟨B, ctx, related⟩
    have inContext := ctx.context related (C := {b}) (by simpa [Admissible] using admB)
    obtain ⟨N', reduces, -⟩ := ctx.reduce inContext
      ((reduces_join_iff _ _).mpr ⟨by decide, rfl⟩)
    obtain ⟨sub, -⟩ := (reduces_join_iff _ _).mp reduces
    exact absurd sub (by decide)
  refine ⟨?_, notCtx, fun h => notCtx (contextual_of_bisimilar h)⟩
  exact bisimilarity_not_congruence.1

/-- **Reduction, negative**: a lone `a` does not reduce: the join needs `a` and `b` at once.
(`reduces_join_iff` gives the positive controls.) -/
theorem lone_a_irreducible (N : Multiset JoinAtom) : ¬ Reduces joinRules ({a} : Multiset JoinAtom) N := by
  rintro ⟨ρ, rfl, enabled, -⟩
  exact absurd enabled.1 (by decide)

/-- **Admissible, positive**: an environment that supplies `a` and `b` and never `c` is admissible
for "anything but `c`". -/
theorem admissible_without_c : Admissible (fun x : JoinAtom => x ≠ c) {a, b} := by
  unfold Admissible; decide

/-- **Admissible, negative**: an environment that supplies `c` is not. -/
theorem not_admissible_with_c : ¬ Admissible (fun x : JoinAtom => x ≠ c) {a, c} := by
  unfold Admissible; decide

end Join

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence
