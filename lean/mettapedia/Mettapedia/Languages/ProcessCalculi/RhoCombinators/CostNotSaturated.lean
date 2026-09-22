/-
# Cost is not a concept on the behavioural quotient

§5 asks what runtime-grown names do to the existing cost account, and names the
premise to check: that account's `saturated_of_classifier` requires a predicate
**constant on merged bisimilarity classes**, and a quotient classifier can exist
only for such a predicate.

The name-growth results already showed the first premise failing — a cost
account decorating a fixed term structure loses its carrier when names are built
at runtime. This file settles the second, and the answer is sharper than
expected: **cost is not saturated at all**, independently of name growth.

The counterexample is small and does not need the constructors:

```
    kk a        and        kk a | kk a
```

Neither can step: a discarder with no message beside it has no partner, and two
of them have no partner either. So neither has any transition, and the
observations they offer are the same — both interact only at `a`, and an
observation of which names a soup interacts at cannot count copies. They are
therefore bisimilar. Their atom counts are 1 and 2.

So the predicate "this soup has at most one atom" separates two bisimilar terms.
`cost_not_saturated` is that, and `no_cost_classifier` is the consequence via
`saturated_of_classifier` run backwards: no classifier on the quotient can agree
with a cost predicate, because a classifier forces saturation and cost is not
saturated.

## What this means for the cost account

The obstruction is not about this calculus and not about the constructors. Cost
counts atoms; bisimilarity cannot see atoms it can never make react. Any cost
account phrased as a predicate on behavioural classes is asking for something
that does not exist, and the fix is not a better classifier — it is to stop
asking cost to factor through the quotient.

Read with the name-growth finding the picture is complete and negative in two
independent ways: the sizes cost must compare are not bounded by the program
(`comparison_cost_unbounded`), and cost is not a property of behaviour
(`cost_not_saturated`). Neither is a defect of the combinator target; both are
facts about what cost is.

`atomCount_not_congruence_invariant` is the negative control in the other
direction, and it fails: cost *is* invariant under structural congruence, since
congruence is component equality. So the obstruction is exactly bisimilarity,
not equivalence in general — which is the useful part.
-/
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Inertness
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.NameGrowth
import Mettapedia.GSLT.Core.ObservedBisimulation

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb
open Mettapedia.GSLT

/-! ## The calculus as an observed system -/

/-- A soup with nothing speaking is inert: every rule needs a partner offering a
value. -/
theorem no_step_of_no_speaker {t : Comb}
    (h : ∀ x ∈ components t, speakSubjects x = []) :
    ∀ t', ¬ Step Cong t t' := by
  refine no_step_of_not_hasMatchingPair ?_
  rintro ⟨listener, -, speaker, hspeaker, heard, -, spoken, hspoken, -⟩
  rw [h speaker hspeaker] at hspoken
  exact absurd hspoken (List.not_mem_nil)

/-- The combinator calculus as a generalized labelled transition system:
structural congruence as its equations, and reduction as its rewrites. -/
def combGSLT : GSLT where
  Term := Comb
  equations :=
    { r := Cong
      iseqv := ⟨Cong.refl, fun h => Cong.symm h, fun h₁ h₂ => Cong.trans h₁ h₂⟩ }
  rewrites := Step Cong
  rewrites_resp_left := fun hcong step =>
    ⟨_, Step.congruent (Cong.symm hcong) step (Cong.refl _), Cong.refl _⟩
  rewrites_resp_right := fun step hcong => Step.congruent (Cong.refl _) step hcong

/-- What a soup lets an observer see: the names it interacts at.  An observation
of which names are in play cannot count how many atoms are in play at one of
them, which is the whole of the obstruction below. -/
def subjectObservation : ObservedGSLT combGSLT where
  Atom := Comb
  observes name soup :=
    ∃ atom ∈ components soup,
      name ∈ listenSubjects atom ∨ name ∈ speakSubjects atom

/-! ## Two bisimilar soups of different size -/

/-- Neither a discarder nor two of them can step. -/
theorem discarder_inert (a : Comb) : ∀ t, ¬ Step Cong (kk a) t := by
  refine no_step_of_no_speaker ?_
  intro x hx
  simp only [components, Multiset.mem_singleton] at hx
  subst hx; rfl

theorem two_discarders_inert (a : Comb) :
    ∀ t, ¬ Step Cong (par (kk a) (kk a)) t := by
  refine no_step_of_no_speaker ?_
  intro x hx
  simp only [components, Multiset.mem_add, Multiset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> rfl

/-- They offer the same observations: both interact exactly at `a`. -/
theorem discarders_same_observations (a name : Comb) :
    subjectObservation.observes name (kk a)
      ↔ subjectObservation.observes name (par (kk a) (kk a)) := by
  constructor
  · rintro ⟨atom, hatom, hname⟩
    refine ⟨atom, ?_, hname⟩
    simp only [components, Multiset.mem_add, Multiset.mem_singleton] at hatom ⊢
    exact Or.inl hatom
  · rintro ⟨atom, hatom, hname⟩
    refine ⟨atom, ?_, hname⟩
    simp only [components, Multiset.mem_add, Multiset.mem_singleton] at hatom ⊢
    rcases hatom with rfl | rfl <;> rfl

/-- **One discarder and two are bisimilar.**  Both are deadlocked and both
interact at the same name, so nothing an observer can do tells them apart. -/
theorem discarders_bisimilar (a : Comb) :
    subjectObservation.Bisimilar (kk a) (par (kk a) (kk a)) := by
  refine ⟨fun left right =>
    (left = kk a ∨ left = par (kk a) (kk a)) ∧
      (right = kk a ∨ right = par (kk a) (kk a)), ⟨⟨?_, ?_⟩, ?_⟩,
    ⟨Or.inl rfl, Or.inr rfl⟩⟩
  · rintro left right ⟨hleft, -⟩ target step
    rcases hleft with rfl | rfl
    · exact absurd step (discarder_inert a target)
    · exact absurd step (two_discarders_inert a target)
  · rintro left right ⟨-, hright⟩ target step
    rcases hright with rfl | rfl
    · exact absurd step (discarder_inert a target)
    · exact absurd step (two_discarders_inert a target)
  · rintro left right ⟨hleft, hright⟩ name
    rcases hleft with rfl | rfl <;> rcases hright with rfl | rfl
    · exact Iff.rfl
    · exact discarders_same_observations a name
    · exact (discarders_same_observations a name).symm
    · exact Iff.rfl

/-! ## The consequence -/

/-- **Cost is not saturated.**  The predicate "at most one atom" separates two
bisimilar soups, so it is not constant on behavioural classes. -/
theorem cost_not_saturated :
    ¬ subjectObservation.Saturated (fun soup => atomCount soup ≤ 1) := by
  intro saturated
  have transported := saturated (discarders_bisimilar nil)
  have small : atomCount (kk nil) ≤ 1 := by
    simp [atomCount, componentList]
  have large : ¬ atomCount (par (kk nil) (kk nil)) ≤ 1 := by
    simp [atomCount, componentList]
  exact large (transported.mp small)

/-- **So no classifier on the behavioural quotient computes cost.**  A quotient
classifier forces saturation, and cost is not saturated, so the cost account
cannot be phrased as a concept on merged bisimilarity classes. -/
theorem no_cost_classifier
    (classifier : subjectObservation.Class → Prop)
    (correct : ∀ soup, classifier (subjectObservation.toClass soup)
      ↔ atomCount soup ≤ 1) : False :=
  cost_not_saturated
    (subjectObservation.saturated_of_classifier _ classifier correct)

/-- **The obstruction is bisimilarity specifically, not equivalence in
general.**  Cost *is* invariant under structural congruence, because congruence
is equality of component bags.  So the right reading is not that cost is badly
behaved but that it is a property of the soup rather than of its behaviour. -/
theorem atomCount_congruence_invariant {p q : Comb} (h : Cong p q) :
    atomCount p = atomCount q := by
  have components := cong_components h
  rw [components_eq_coe, components_eq_coe] at components
  simpa only [atomCount, Multiset.coe_card] using congrArg Multiset.card components

end Mettapedia.Languages.ProcessCalculi.RhoCombinators
