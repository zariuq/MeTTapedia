import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.RoundTwoPresentations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceSteps

/-!
# Multi-firing steps of the base layer are rounds

`Race.StepMoves` is the multi-firing step in the Petri-net sense over the base layer: a nonempty word of
offered firings, pairwise statically independent (`AnnotatedRuns.StaticIndependent`: no checks, queries
that do not depend on the solution, footprints trace independent at every solution and configuration),
executable in order. Its five choices are those of `AnnotatedRuns.Round` with one difference in the
guards: a firing of the static fragment has no checks, and its queries do not depend on the solution,
neither in their region nor in what they accept. This module places it among the rounds.

* **`compatible_of_static`**: statically independent firings are compatible at every configuration.
* **`round_of_static`**: an executable word of pairwise statically independent firings is a round of the
  base layer; so the firings of every multi-firing step form a round (`round_of_stepMoves`).
* **`stepMoves_of_admitsOwn`**: conversely, a bag of positive rules admitted on its own at an embedded
  state, keeping labels, whose images are offered and pairwise statically independent, is one
  multi-firing step, to the configuration its images reach.
* **`admitsOwn_of_stepMoves`**: a multi-firing step whose firings are the images of members with jointly
  fresh openings and one seen set per collect pattern is a bag admitted on its own, whose members keep
  labels.

The static fragment is strictly smaller than the rounds: a teller and a firing whose guard `Y = Y`
ignores the tell form a round and are not statically independent
(`AnnotatedRuns.RoundControls.contextual_strictly_coarser`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.Rounds

open OneFrame (Terms frames ext embed)
open JointFirings (OneMember bagOf)
open Scope (Positive)

universe uT uS uO uL

section Petri

variable {T : Type uT} {S : Type uS} (A : SubstitutionAction T S) {O : Type uO} [DecidableEq O]

/-- **Statically independent firings are compatible at every configuration.** -/
theorem compatible_of_static {label : O → T} {f g : AnnotatedRuns.Firing T S O}
    (independent : AnnotatedRuns.StaticIndependent label f g) (C : Configuration T O) :
    AnnotatedRuns.Compatible A label C f g := by
  obtain ⟨fStatic, gStatic, apart⟩ := independent
  have trace := apart A.identity C
  refine ⟨⟨trace.1.1, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rintro (kept | ⟨_, member, _⟩)
    · exact trace.1.2.1 (Or.inl kept)
    · simp [Selection.commit] at member
  · rintro (kept | ⟨_, member, _⟩)
    · exact trace.1.2.2 (Or.inl kept)
    · simp [Selection.commit] at member
  · intro check member
    rw [fStatic.checks] at member
    cases member
  · intro check member
    rw [gStatic.checks] at member
    cases member
  · intro query member σ _ o written
    exact apart.symm.writesOutside σ query member o (by simpa [Selection.commit] using written)
  · intro query member σ _ o written
    exact apart.writesOutside σ query member o (by simpa [Selection.commit] using written)

/-- **An executable word of pairwise statically independent firings is a round of the base layer.** -/
theorem round_of_static {label : O → T} {C : Configuration T O} {w : List (AnnotatedRuns.Firing T S O)}
    (independent : w.Pairwise (AnnotatedRuns.StaticIndependent label))
    (executable : AnnotatedRuns.Executable A label C w) : AnnotatedRuns.Round A label C w := by
  refine ⟨fun f inside => ?_, AnnotatedRuns.Executable.joint A label executable,
    independent.imp fun static => compatible_of_static A static C⟩
  obtain ⟨u, v, rfl⟩ := List.append_of_mem inside
  exact (Race.step_order_irrelevant A label independent List.perm_middle executable).1.1

/-- **The firings of every multi-firing step of the base layer form a round there.** -/
theorem round_of_stepMoves {L : Type uL} {offers : L → AnnotatedRuns.Firing T S O → Prop}
    {label : O → T} {C D : Configuration T O} {M : Multiset L}
    (step : Race.StepMoves A label offers C M D) :
    ∃ w : List (L × AnnotatedRuns.Firing T S O), w ≠ [] ∧ (∀ x ∈ w, offers x.1 x.2) ∧
      AnnotatedRuns.Round A label C (w.map Prod.snd) ∧ M = (↑(w.map Prod.fst) : Multiset L) ∧
      D = AnnotatedRuns.follow label C (w.map Prod.snd) := by
  obtain ⟨w, nonempty, offered, independent, executable, labels, reached⟩ := step
  exact ⟨w, nonempty, offered, round_of_static A independent executable, labels, reached⟩

variable {P : Program (Terms T)}

/-- **A bag of positive rules admitted on its own at an embedded state, keeping labels, whose images are
offered and pairwise statically independent, is one multi-firing step of the base layer.** -/
theorem stepMoves_of_admitsOwn {L : Type uL} {offers : L → AnnotatedRuns.Firing T S O → Prop}
    {label : O → T} {C : Configuration T O} {l : List (OneMember A O P)} (labels : OneMember A O P → L)
    (own : JointFirings.Bag.AdmitsOwn (frames A) (embed label C) (bagOf A l))
    (keeps : ∀ m ∈ l, KeepsLabels A label m) (positive : ∀ m ∈ l, Positive m.rule)
    (nonempty : l ≠ []) (offered : ∀ m ∈ l, offers (labels m) (baseFiring A m))
    (independent : (image A l).Pairwise (AnnotatedRuns.StaticIndependent label)) :
    Race.StepMoves A label offers C (↑(l.map labels) : Multiset L)
      (AnnotatedRuns.follow label C (image A l)) := by
  have word : (l.map fun m => (labels m, baseFiring A m)).map Prod.snd = image A l :=
    List.map_map.trans rfl
  have names : (l.map fun m => (labels m, baseFiring A m)).map Prod.fst = l.map labels :=
    List.map_map.trans rfl
  refine ⟨l.map fun m => (labels m, baseFiring A m), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro empty
    exact nonempty (List.map_eq_nil_iff.mp empty)
  · intro x inside
    obtain ⟨m, inM, rfl⟩ := List.mem_map.mp inside
    exact offered m inM
  · rw [word]
    exact independent
  · rw [word]
    exact (round_image_of_positive A own keeps positive).executable A label
  · rw [names]
  · rw [word]

/-- **The firings of a multi-firing step (pairwise statically independent, executable in order), when
they are the images of members with jointly fresh openings and one seen set per collect pattern, are a
bag admitted on its own; its members keep labels.** -/
theorem admitsOwn_of_stepMoves {L : Type uL} {label : O → T} {C : Configuration T O}
    {l : List (OneMember A O P)} {w : List (L × AnnotatedRuns.Firing T S O)}
    (independent : (w.map Prod.snd).Pairwise (AnnotatedRuns.StaticIndependent label))
    (executable : AnnotatedRuns.Executable A label C (w.map Prod.snd))
    (images : w.map Prod.snd = image A l)
    (fresh : JointFirings.Bag.Fresh (frames A) (embed label C) (bagOf A l))
    (collect : ∀ m ∈ l, m.rule.collect.length = m.seen.length) :
    JointFirings.Bag.AdmitsOwn (frames A) (embed label C) (bagOf A l) ∧
      ∀ m ∈ l, KeepsLabels A label m := by
  have round := round_of_static A independent executable
  rw [images] at round
  exact admitsOwn_of_round A round fresh collect

end Petri

#print axioms compatible_of_static
#print axioms round_of_static
#print axioms round_of_stepMoves
#print axioms stepMoves_of_admitsOwn
#print axioms admitsOwn_of_stepMoves

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.Rounds
