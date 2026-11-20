import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.StepConcepts
import Mettapedia.GSLT.Core.StepFree

/-!
# Which modalities carry types across the step

A type survives a modality when the possibility, or the necessity, of a type is a type again
(`possibility`, `necessity`).

* **The forward modalities carry the types of bisimilarity** (`bisimClosed_possibility`,
  `bisimClosed_necessity`): on every system, possibility and successor necessity of a class closed
  under bisimilarity are closed under bisimilarity. So the types of the infinitary formulas survive
  them (`iconcept_possibility`, `iconcept_necessity`); on the step, OSLF's possibility and successor
  necessity over the firings carry them (`step_possibility_isConcept`,
  `step_necessity_isConcept`). Under Hennessy–Milner adequacy the types of the finitary formulas
  survive them too (`concept_possibility_of_adequate`, `concept_necessity_of_adequate`), in
  particular on the first-order step under every finite program.
* **Not the finitary types in general** (`endless_possibility_control`): on the tree's
  counterexample to finitary adequacy, the endless state alone is a type of the finitary formulas,
  and the states with a successor in it are not.
* **Not the past** (`Past.predecessor_control`): on a three-state system where `0` steps to `1`
  and `1`, `2` are stuck, the states other than `0` form a class closed under bisimilarity, and the
  states all of whose predecessors lie in it do not: `1` has the predecessor `0`, `2` has none, and
  they are bisimilar. Bisimulation transfers moves forward, not backward; predecessor necessity is
  OSLF's box over the reduction span (`Past.predecessorNecessity_eq`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Survival

open Set
open Mettapedia.Cybernetics.DistinctionCalculus.Exclusion
open Mettapedia.GSLT Mettapedia.GSLT.HennessyMilner
open Mettapedia.OSLF.Framework.DerivedModalities
open FragmentsOfTheStep.TransitionMaps
open ObserverConcepts InfinitaryAdequacy StepConcepts StepSpan

universe u uAtom uLabel uO uT uH uOcc uS uF

section Systems

variable {S : GSLT.{u}} (M : System.{uAtom, uLabel} S)

/-- **Possibility**: some successor under the label lies in the class. -/
def possibility (l : M.Label) (A : Set S.Term) : Set S.Term := {x | ∃ x', M.act l x x' ∧ x' ∈ A}

/-- **Successor necessity**: every successor under the label lies in the class. -/
def necessity (l : M.Label) (A : Set S.Term) : Set S.Term := {x | ∀ x', M.act l x x' → x' ∈ A}

/-- **Possibility carries bisimulation types.** -/
theorem bisimClosed_possibility {A : Set S.Term} (closed : BisimClosed M A) (l : M.Label) :
    BisimClosed M (possibility M l A) := by
  rintro x ⟨x', step, inA⟩ y ⟨R, bisimulation, related⟩
  obtain ⟨y', step', related'⟩ := bisimulation.1 related l step
  exact ⟨y', step', closed x' inA y' ⟨R, bisimulation, related'⟩⟩

/-- **Successor necessity carries bisimulation types.** -/
theorem bisimClosed_necessity {A : Set S.Term} (closed : BisimClosed M A) (l : M.Label) :
    BisimClosed M (necessity M l A) := by
  rintro x all y ⟨R, bisimulation, related⟩ y' step
  obtain ⟨x', step', related'⟩ := bisimulation.2.1 related l step
  exact closed x' (all x' step') y' ⟨R, bisimulation, related'⟩

/-- The types of the infinitary formulas survive possibility. -/
theorem iconcept_possibility {A : Set S.Term} (concept : IsConcept (Apart (iformulas M)) A)
    (l : M.Label) : IsConcept (Apart (iformulas M)) (possibility M l A) :=
  (isConcept_iformulas_iff M _).mpr
    (bisimClosed_possibility M ((isConcept_iformulas_iff M A).mp concept) l)

/-- The types of the infinitary formulas survive successor necessity. -/
theorem iconcept_necessity {A : Set S.Term} (concept : IsConcept (Apart (iformulas M)) A)
    (l : M.Label) : IsConcept (Apart (iformulas M)) (necessity M l A) :=
  (isConcept_iformulas_iff M _).mpr
    (bisimClosed_necessity M ((isConcept_iformulas_iff M A).mp concept) l)

/-- Under adequacy the types of the finitary formulas survive possibility. -/
theorem concept_possibility_of_adequate
    (adequate : ∀ x y, M.LogicallyEquivalent x y ↔ M.Bisimilar x y) {A : Set S.Term}
    (concept : IsConcept (Apart (formulas M)) A) (l : M.Label) :
    IsConcept (Apart (formulas M)) (possibility M l A) :=
  (isConcept_formulas_iff_bisimClosed M adequate _).mpr
    (bisimClosed_possibility M ((isConcept_formulas_iff_bisimClosed M adequate A).mp concept) l)

/-- Under adequacy the types of the finitary formulas survive successor necessity. -/
theorem concept_necessity_of_adequate
    (adequate : ∀ x y, M.LogicallyEquivalent x y ↔ M.Bisimilar x y) {A : Set S.Term}
    (concept : IsConcept (Apart (formulas M)) A) (l : M.Label) :
    IsConcept (Apart (formulas M)) (necessity M l A) :=
  (isConcept_formulas_iff_bisimClosed M adequate _).mpr
    (bisimClosed_necessity M ((isConcept_formulas_iff_bisimClosed M adequate A).mp concept) l)

end Systems

/-! ## On the step: OSLF's modalities over the firings -/

section Step

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} {X : Interface.Frames Tm Hom}
  {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (P : Interface.Step X O State Firing) {Atom : Type} (observes : Atom → State → Prop)

theorem firing_possibility_iff (A : Set State) (s : State) :
    derivedDiamond (firingSpan P) (· ∈ A) s ↔ s ∈ possibility (stepSystem P observes) () A :=
  (Iff.of_eq (congrFun (firing_diamond_eq P _) s)).trans (diamond_iff _ _ _)

theorem firing_necessity_iff (A : Set State) (s : State) :
    derivedForwardBox (firingSpan P) (· ∈ A) s ↔ s ∈ necessity (stepSystem P observes) () A :=
  (Iff.of_eq (congrFun (firing_forwardBox_eq P _) s)).trans (forwardBox_iff _ _ _)

/-- **OSLF's possibility over the step's firings carries the types of the infinitary formulas.** -/
theorem step_possibility_isConcept {A : Set State}
    (concept : IsConcept (Apart (iformulas (stepSystem P observes))) A) :
    IsConcept (Apart (iformulas (stepSystem P observes)))
      {s | derivedDiamond (firingSpan P) (· ∈ A) s} := by
  refine (isConcept_iformulas_iff (stepSystem P observes) _).mpr ?_
  intro x member y bisimilar
  have closed := (isConcept_iformulas_iff (stepSystem P observes) _).mp
    (iconcept_possibility (stepSystem P observes) concept ())
  exact (firing_possibility_iff P observes A y).mpr
    (closed x ((firing_possibility_iff P observes A x).mp member) y bisimilar)

/-- **OSLF's successor necessity over the step's firings carries them.** -/
theorem step_necessity_isConcept {A : Set State}
    (concept : IsConcept (Apart (iformulas (stepSystem P observes))) A) :
    IsConcept (Apart (iformulas (stepSystem P observes)))
      {s | derivedForwardBox (firingSpan P) (· ∈ A) s} := by
  refine (isConcept_iformulas_iff (stepSystem P observes) _).mpr ?_
  intro x member y bisimilar
  have closed := (isConcept_iformulas_iff (stepSystem P observes) _).mp
    (iconcept_necessity (stepSystem P observes) concept ())
  exact (firing_necessity_iff P observes A y).mpr
    (closed x ((firing_necessity_iff P observes A x).mp member) y bisimilar)

end Step

/-! ## Control: a finitary type whose possibility is not one -/

section Endless

open ImageFinitenessNecessary

theorem sat_after_iff_runs (k : ℕ) (s : St) :
    hm.sat (Formula.after (List.replicate k ()) .top) s ↔ Runs k s := by
  induction k generalizing s with
  | zero => exact Iff.rfl
  | succ k ih =>
      show (∃ t, ImageFinitenessNecessary.Step s t ∧
          hm.sat (Formula.after (List.replicate k ()) .top) t) ↔
        ∃ t, ImageFinitenessNecessary.Step s t ∧ Runs k t
      exact exists_congr fun t => and_congr_right fun _ => ih t

/-- From the endless state the only successor is itself. -/
theorem endless_step {t : St} (step : ImageFinitenessNecessary.Step St.endless t) :
    t = St.endless := by
  cases step
  rfl

/-- **The endless state alone is a type of the finitary formulas.** -/
theorem endless_singleton_isConcept : IsConcept (Apart (formulas hm)) {St.endless} := by
  refine (isConcept_formulas_iff hm _).mpr ?_
  rintro x rfl y equivalent
  have stuckAfter : ∀ s : St, ImageFinitenessNecessary.Step s (St.chain 0) →
      hm.sat (.dia () (.neg (.dia () .top))) s := fun s step =>
    ⟨St.chain 0, step, fun ⟨t, next, _⟩ => by
      have chainStep : ImageFinitenessNecessary.Step (St.chain 0) t := next
      cases chainStep⟩
  have notEndless : ¬ hm.sat (.dia () (.neg (.dia () .top))) St.endless := by
    rintro ⟨t, step, stuck⟩
    rw [endless_step step] at stuck
    exact stuck ⟨St.endless, ImageFinitenessNecessary.Step.endlessLoop, trivial⟩
  cases y with
  | left => exact absurd ((equivalent _).mpr
      (stuckAfter St.left (ImageFinitenessNecessary.Step.leftChain 0))) notEndless
  | right => exact absurd ((equivalent _).mpr
      (stuckAfter St.right (ImageFinitenessNecessary.Step.rightChain 0))) notEndless
  | chain n =>
      have there := (equivalent (Formula.after (List.replicate (n + 1) ()) .top)).mp
        ((sat_after_iff_runs (n + 1) St.endless).mpr (runs_endless (n + 1)))
      exact absurd ((sat_after_iff_runs (n + 1) (St.chain n)).mp there) (not_runs_chain n)
  | endless => rfl

/-- **Control: without adequacy a finitary type need not survive possibility.** -/
theorem endless_possibility_control :
    IsConcept (Apart (formulas hm)) {St.endless} ∧
      ¬ IsConcept (Apart (formulas hm)) (possibility hm () {St.endless}) := by
  refine ⟨endless_singleton_isConcept, fun concept => ?_⟩
  have atRight : St.right ∈ possibility hm () {St.endless} :=
    ⟨St.endless, ImageFinitenessNecessary.Step.rightEndless, rfl⟩
  obtain ⟨t, step, isEndless⟩ := (isConcept_formulas_iff hm _).mp concept St.right atRight St.left
    (hm.logicallyEquivalent_symm logically_equivalent)
  have leftStep : ImageFinitenessNecessary.Step St.left t := step
  cases leftStep
  cases isEndless

end Endless

/-! ## Control: the past -/

namespace Past

/-- **Three states**: `0` steps to `1`; `1` and `2` are stuck. -/
def past : System.{0, 0} (GSLT.stepFree (Fin 3)) where
  Atom := Empty
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := Unit
  act _ a b := a = 0 ∧ b = 1
  act_resp_left := by
    intro _ left right target same step
    have equal : left = right := same
    subst equal
    exact ⟨target, step, rfl⟩
  act_resp_right := by
    intro _ source target target' step same
    have equal : target = target' := same
    subst equal
    exact step

/-- The states other than `0`. -/
def notStart : Set (Fin 3) := {s | s ≠ 0}

/-- **Predecessor necessity**: every predecessor lies in the class. -/
def predecessorNecessity (A : Set (Fin 3)) : Set (Fin 3) := {s | ∀ p, past.act () p s → p ∈ A}

/-- It is OSLF's box over the reduction span. -/
theorem predecessorNecessity_eq (A : Set (Fin 3)) :
    predecessorNecessity A = {s | derivedBox (span (past.act ())) (· ∈ A) s} := by
  ext s
  exact (box_iff _ _ _).symm

/-- The stuck states are bisimilar. -/
theorem stuck_bisimilar : past.Bisimilar 1 2 := by
  refine ⟨fun a b => a ≠ 0 ∧ b ≠ 0, ⟨?_, ?_, ?_⟩, by decide, by decide⟩
  · rintro a b ⟨notA, _⟩ _ a' step
    exact absurd step.1 notA
  · rintro a b ⟨_, notB⟩ _ b' step
    exact absurd step.1 notB
  · intro _ _ _ atom
    exact atom.elim

theorem notStart_bisimClosed : BisimClosed past notStart := by
  intro x notX y ⟨R, bisimulation, related⟩ isStart
  have start : y = 0 := isStart
  subst start
  obtain ⟨x', step, _⟩ := bisimulation.2.1 related () (show past.act () 0 1 from ⟨rfl, rfl⟩)
  exact notX step.1

/-- **Control: predecessor necessity does not carry bisimulation types.** -/
theorem predecessor_control :
    BisimClosed past notStart ∧ past.Bisimilar 1 2 ∧
      (2 : Fin 3) ∈ predecessorNecessity notStart ∧ (1 : Fin 3) ∉ predecessorNecessity notStart ∧
      ¬ BisimClosed past (predecessorNecessity notStart) := by
  have two : (2 : Fin 3) ∈ predecessorNecessity notStart := by
    intro p step
    exact absurd step.2 (by decide)
  have one : (1 : Fin 3) ∉ predecessorNecessity notStart := by
    intro all
    exact all 0 ⟨rfl, rfl⟩ rfl
  refine ⟨notStart_bisimClosed, stuck_bisimilar, two, one, fun closed => ?_⟩
  exact one (closed 2 two 1 (past.bisimilar_symm stuck_bisimilar))

end Past

#print axioms bisimClosed_possibility
#print axioms bisimClosed_necessity
#print axioms iconcept_possibility
#print axioms iconcept_necessity
#print axioms concept_possibility_of_adequate
#print axioms concept_necessity_of_adequate
#print axioms step_possibility_isConcept
#print axioms step_necessity_isConcept
#print axioms endless_singleton_isConcept
#print axioms endless_possibility_control
#print axioms Past.predecessorNecessity_eq
#print axioms Past.predecessor_control

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Survival
