import Mettapedia.GSLT.Core.OperationalReadback
import Mettapedia.CategoryTheory.GeneralizedOpenMaps

/-!
# An operational correspondence is a path bisimulation of the sum of the two systems

`OperationalCorrespondence source target` relates the states of two systems: a target step is read back as no
source step or one (`readStep`), and a source step is realized by a finite target path (`forward`).
`Mettapedia.CategoryTheory.GeneralizedOpenMaps` states path bisimulation over one system with a step, a
saturated step and observations (`BisimulationKit`, `PathWitness`): a symmetric relation that matches a step by
a saturated step (`GOpen`) and preserves observations.

* **The sum of two systems** (`SumStep`, `sumKit`): states of either system; a step is a step of one of them; a
  saturated step is a finite path of steps; the observation is each system's own, over one type of
  observations.
* **A correspondence that agrees on the observation is a path bisimulation of the sum** (`pathWitness`,
  `pathBisim_of_related`): the relation, closed under symmetry on the sum (`sumRelation`). A source step is
  matched by the target path of `forward`; a target step by no source step or one.
* **The converse needs the source's paths** (`correspondence_of_pathWitness`): a path bisimulation of the sum is
  a correspondence from the transitive closure of the source.
* **Control** (`skipping_pathBisim`, `skipping_not_readback`): the source `0 → 1 → 2` and the target `0 → 2`,
  observing whether the state is `2`. The relation `0 ~ 0`, `1 ~ 0`, `2 ~ 2` is a path bisimulation of the sum,
  and no readback that agrees on the observation relates `0` and `0`: the target step `0 → 2` is matched only by
  the source path `0 → 1 → 2`, of length two. The other way round is a correspondence (`expanding`): one source
  step `0 → 2` is realized by the target path `0 → 1 → 2`, whose first step is read back as no step.

## Open maps

Joyal, Nielsen and Winskel (Bisimulation from open maps, Information and Computation 127(2), 1996) call a
morphism of models open when it lifts paths with respect to a chosen subcategory of path shapes. For transition
systems with finite sequences of transitions as paths, the open morphisms are those whose graph is a
bisimulation, and two rooted systems are joined by a span of open maps exactly when they are strongly bisimilar.
Matching a step by a path, as `GOpen` does, is the weak variant (Fiore, Cattani and Winskel, Weak bisimulation
and open maps, LICS 1999), which needs path shapes up to silent steps. An `OperationalCorrespondence` is a
relation, not a morphism. Read as the span `source ← related → target`, its readback lifts each target step to a
source path of length at most one, and its realization lifts each source step to a target path of any length:
it is closer to the weak notion, and strict only on the target side. This module proves the statements above
about the minimal path-bisimulation core; it constructs no category of models and no open map.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IndexedOperational.CorrespondencePathWitness

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.CategoryTheory.GeneralizedOpenMaps
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)

universe uS uT uO

/-! ## The sum of two systems -/

section Sum

variable (source : GSLT.{uS}) (target : GSLT.{uT})

/-- **A step of the sum of two systems**: a step of one of them. -/
def SumStep : source.Term ⊕ target.Term → source.Term ⊕ target.Term → Prop
  | .inl a, .inl b => source.Step a b
  | .inr t, .inr u => target.Step t u
  | _, _ => False

/-- **The observation on the sum**: each system's own. -/
def sumObservable {Obs : Type uO} (sourceObs : source.Term → Obs → Prop) (targetObs : target.Term → Obs → Prop) :
    source.Term ⊕ target.Term → Obs → Prop
  | .inl a, o => sourceObs a o
  | .inr t, o => targetObs t o

/-- **The kit of the sum**, over one type of observations: a saturated step is a finite path of steps. -/
def sumKit (Obs : Type uO) (sourceObs : source.Term → Obs → Prop) (targetObs : target.Term → Obs → Prop) :
    BisimulationKit (source.Term ⊕ target.Term) Obs where
  step := SumStep source target
  stepStar := Relation.ReflTransGen (SumStep source target)
  step_sub_star := fun stepped => Relation.ReflTransGen.single stepped
  observable := sumObservable source target sourceObs targetObs

/-- **A relation between the two systems, on the sum**, closed under symmetry. -/
def sumRelation (related : source.Term → target.Term → Prop) :
    source.Term ⊕ target.Term → source.Term ⊕ target.Term → Prop
  | .inl a, .inr t => related a t
  | .inr t, .inl a => related a t
  | _, _ => False

end Sum

/-! ## Paths of the sum stay in one system -/

section Paths

variable {source : GSLT.{uS}} {target : GSLT.{uT}}

/-- A finite run is empty or a nonempty path. -/
theorem eq_or_transGen_of_multiStep {S : GSLT.{uS}} {a b : S.Term} (path : S.MultiStep a b) :
    a = b ∨ Relation.TransGen S.Step a b := by
  induction path with
  | refl => exact Or.inl rfl
  | step stepped _ reached =>
      rcases reached with same | longer
      · subst same
        exact Or.inr (.single stepped)
      · exact Or.inr (.head stepped longer)

/-- A path of the sum from a source state is a run of the source. -/
theorem sumPath_inl {a : source.Term} {x : source.Term ⊕ target.Term}
    (path : Relation.ReflTransGen (SumStep source target) (.inl a) x) :
    ∃ b, x = .inl b ∧ source.MultiStep a b := by
  induction path with
  | refl => exact ⟨a, rfl, .refl _⟩
  | @tail y z _ stepped reached =>
      obtain ⟨b, rfl, run⟩ := reached
      cases z with
      | inl c => exact ⟨c, rfl, multiStepAppend run (.step stepped (.refl _))⟩
      | inr u => exact False.elim stepped

/-- A path of the sum from a target state is a run of the target. -/
theorem sumPath_inr {t : target.Term} {x : source.Term ⊕ target.Term}
    (path : Relation.ReflTransGen (SumStep source target) (.inr t) x) :
    ∃ u, x = .inr u ∧ target.MultiStep t u := by
  induction path with
  | refl => exact ⟨t, rfl, .refl _⟩
  | @tail y z _ stepped reached =>
      obtain ⟨u, rfl, run⟩ := reached
      cases z with
      | inl c => exact False.elim stepped
      | inr v => exact ⟨v, rfl, multiStepAppend run (.step stepped (.refl _))⟩

/-- A run of the source is a path of the sum. -/
theorem sumPath_of_source {a b : source.Term} (path : source.MultiStep a b) :
    Relation.ReflTransGen (SumStep source target) (.inl a) (.inl b) := by
  induction path with
  | refl => exact .refl
  | @step x y z stepped _ reached =>
      exact Relation.ReflTransGen.head (show SumStep source target (.inl x) (.inl y) from stepped) reached

/-- A run of the target is a path of the sum. -/
theorem sumPath_of_target {t u : target.Term} (path : target.MultiStep t u) :
    Relation.ReflTransGen (SumStep source target) (.inr t) (.inr u) := by
  induction path with
  | refl => exact .refl
  | @step x y z stepped _ reached =>
      exact Relation.ReflTransGen.head (show SumStep source target (.inr x) (.inr y) from stepped) reached

end Paths

/-! ## A correspondence is a path bisimulation -/

section Correspondence

variable {source : GSLT.{uS}} {target : GSLT.{uT}}

/-- **A correspondence that agrees on an observation is a path bisimulation of the sum.** A source step is
matched by the target path of `forward`; a target step by no source step or one. -/
def pathWitness (comparison : OperationalCorrespondence source target) (Obs : Type uO)
    (sourceObs : source.Term → Obs → Prop) (targetObs : target.Term → Obs → Prop)
    (agree : ∀ {a t}, comparison.related a t → ∀ o, (sourceObs a o ↔ targetObs t o)) :
    PathWitness (sumKit source target Obs sourceObs targetObs) where
  rel := sumRelation source target comparison.related
  symm := by
    rintro (a | t) (b | u) related
    · exact False.elim related
    · exact related
    · exact related
    · exact False.elim related
  lift := by
    rintro (a | t) (b | u) related (a' | t') stepped
    · exact False.elim related
    · exact False.elim related
    · obtain ⟨final, ⟨path⟩, related'⟩ := comparison.forward related stepped
      exact ⟨.inr final, sumPath_of_target (executionPathToMultiStep path), related'⟩
    · exact False.elim stepped
    · exact False.elim stepped
    · rcases comparison.readStep related stepped with silent | ⟨after, sourceStep, related'⟩
      · exact ⟨.inl b, .refl, silent⟩
      · exact ⟨.inl after, Relation.ReflTransGen.single sourceStep, related'⟩
    · exact False.elim related
    · exact False.elim related
  obs := by
    rintro (a | t) (b | u) related o observed
    · exact False.elim related
    · exact (agree related o).mp observed
    · exact (agree related o).mpr observed
    · exact False.elim related

/-- **Related states are path bisimilar in the sum.** -/
theorem pathBisim_of_related (comparison : OperationalCorrespondence source target) (Obs : Type uO)
    (sourceObs : source.Term → Obs → Prop) (targetObs : target.Term → Obs → Prop)
    (agree : ∀ {a t}, comparison.related a t → ∀ o, (sourceObs a o ↔ targetObs t o))
    {a : source.Term} {t : target.Term} (related : comparison.related a t) :
    PathBisim (sumKit source target Obs sourceObs targetObs) (.inl a) (.inr t) :=
  ⟨pathWitness comparison Obs sourceObs targetObs agree, related⟩

/-- **A path bisimulation of the sum is a correspondence from the transitive closure of the source**: a target
step is matched by a source path, which is no step or a step of the closure. -/
def correspondence_of_pathWitness {Obs : Type uO} {sourceObs : source.Term → Obs → Prop}
    {targetObs : target.Term → Obs → Prop} (witness : PathWitness (sumKit source target Obs sourceObs targetObs)) :
    OperationalCorrespondence (equalityGSLT source.Term (Relation.TransGen source.Step)) target where
  related a t := witness.rel (.inl a) (.inr t)
  readStep := by
    intro a t t' related stepped
    obtain ⟨q, star, related'⟩ := witness.lift (witness.symm related)
      (show (sumKit source target Obs sourceObs targetObs).step (.inr t) (.inr t') from stepped)
    obtain ⟨a', rfl, run⟩ := sumPath_inl star
    rcases eq_or_transGen_of_multiStep run with same | longer
    · subst same
      exact Or.inl (witness.symm related')
    · exact Or.inr ⟨a', longer, witness.symm related'⟩
  forward := by
    intro a a' t related stepped
    have closure : Relation.TransGen source.Step a a' := stepped
    clear stepped
    induction closure with
    | @single b sourceStep =>
        obtain ⟨q, star, related'⟩ := witness.lift related
          (show (sumKit source target Obs sourceObs targetObs).step (.inl a) (.inl b) from sourceStep)
        obtain ⟨u, rfl, run⟩ := sumPath_inr star
        exact ⟨u, (executionPath_nonempty_iff_multiStep target _ _).mpr run, related'⟩
    | @tail b c _ sourceStep reached =>
        obtain ⟨u, ⟨path⟩, relatedB⟩ := reached
        obtain ⟨q, star, related'⟩ := witness.lift relatedB
          (show (sumKit source target Obs sourceObs targetObs).step (.inl b) (.inl c) from sourceStep)
        obtain ⟨v, rfl, run⟩ := sumPath_inr star
        exact ⟨v, (executionPath_nonempty_iff_multiStep target _ _).mpr
          (multiStepAppend (executionPathToMultiStep path) run), related'⟩

end Correspondence

/-! ## Control: a path bisimulation that is no readback -/

/-- The step of the source `0 → 1 → 2`. -/
def skipSourceStep (a b : ℕ) : Prop := a < 2 ∧ b = a + 1

/-- The step of the target `0 → 2`. -/
def skipTargetStep (a b : ℕ) : Prop := a = 0 ∧ b = 2

/-- The source `0 → 1 → 2`. -/
def skipSource : GSLT := equalityGSLT ℕ skipSourceStep

/-- The target `0 → 2`. -/
def skipTarget : GSLT := equalityGSLT ℕ skipTargetStep

/-- The observation: whether a state is `2`. -/
abbrev isTwo (a : ℕ) (_ : Unit) : Prop := a = 2

/-- The kit of the sum of the control. -/
def skipKit : BisimulationKit (skipSource.Term ⊕ skipTarget.Term) Unit :=
  sumKit skipSource skipTarget Unit isTwo isTwo

/-- The relation `0 ~ 0`, `1 ~ 0`, `2 ~ 2`. -/
def skipRelated (a t : ℕ) : Prop := (a = 0 ∧ t = 0) ∨ (a = 1 ∧ t = 0) ∨ (a = 2 ∧ t = 2)

theorem skipRelated_agree {a t : ℕ} (related : skipRelated a t) : a = 2 ↔ t = 2 := by
  rcases related with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- **The relation is a path bisimulation of the sum**, observing whether the state is `2`. -/
def skipWitness : PathWitness skipKit where
  rel := sumRelation skipSource skipTarget skipRelated
  symm := by
    rintro (a | t) (b | u) related
    · exact False.elim related
    · exact related
    · exact related
    · exact False.elim related
  lift := by
    rintro (a | t) (b | u) related (a' | t') stepped
    · exact False.elim related
    · exact False.elim related
    · obtain ⟨small, rfl⟩ : skipSourceStep a a' := stepped
      rcases (related : skipRelated a u) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨.inr (0 : ℕ), .refl, (Or.inr (Or.inl ⟨rfl, rfl⟩) : skipRelated (0 + 1) 0)⟩
      · exact ⟨.inr (2 : ℕ), Relation.ReflTransGen.single (show skipTargetStep 0 2 from ⟨rfl, rfl⟩),
          (Or.inr (Or.inr ⟨rfl, rfl⟩) : skipRelated (1 + 1) 2)⟩
      · exact absurd small (by decide)
    · exact False.elim stepped
    · exact False.elim stepped
    · obtain ⟨rfl, rfl⟩ : skipTargetStep t t' := stepped
      rcases (related : skipRelated b 0) with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, impossible⟩
      · exact ⟨.inl (2 : ℕ),
          Relation.ReflTransGen.head
            (show SumStep skipSource skipTarget (.inl (0 : ℕ)) (.inl (1 : ℕ)) from
              (⟨by decide, rfl⟩ : skipSourceStep 0 1))
            (Relation.ReflTransGen.single
              (show SumStep skipSource skipTarget (.inl (1 : ℕ)) (.inl (2 : ℕ)) from
                (⟨by decide, rfl⟩ : skipSourceStep 1 2))),
          (Or.inr (Or.inr ⟨rfl, rfl⟩) : skipRelated 2 2)⟩
      · exact ⟨.inl (2 : ℕ), Relation.ReflTransGen.single (show skipSourceStep 1 2 from ⟨by decide, rfl⟩),
          (Or.inr (Or.inr ⟨rfl, rfl⟩) : skipRelated 2 2)⟩
      · exact absurd impossible (by decide)
    · exact False.elim related
    · exact False.elim related
  obs := by
    rintro (a | t) (b | u) related o observed
    · exact False.elim related
    · exact (skipRelated_agree related).mp observed
    · exact (skipRelated_agree related).mpr observed
    · exact False.elim related

/-- **`0` and `0` are path bisimilar in the sum.** -/
theorem skipping_pathBisim : PathBisim skipKit (.inl (0 : ℕ)) (.inr (0 : ℕ)) :=
  ⟨skipWitness, (Or.inl ⟨rfl, rfl⟩ : skipRelated 0 0)⟩

/-- **No readback that agrees on the observation relates `0` and `0`**: the target step `0 → 2` would be read
back as no source step, relating `0` and `2`, or as the step `0 → 1`, relating `1` and `2`; both disagree on
the observation. -/
theorem skipping_not_readback (readback : OperationalReadback skipSource skipTarget)
    (agree : ∀ {a t}, readback.related a t → (isTwo a () ↔ isTwo t ())) :
    ¬ readback.related (0 : ℕ) (0 : ℕ) := by
  intro related
  rcases readback.readStep related (show skipTargetStep 0 2 from ⟨rfl, rfl⟩) with
    silent | ⟨after, stepped, related'⟩
  · exact absurd (show (0 : ℕ) = 2 from (agree silent).mpr rfl) (by decide)
  · obtain ⟨-, rfl⟩ : skipSourceStep 0 after := stepped
    exact absurd (show (0 + 1 : ℕ) = 2 from (agree related').mpr rfl) (by decide)

/-- The relation of the positive instance: `0 ~ 0`, `0 ~ 1`, `2 ~ 2`. -/
def expandRelated (t a : ℕ) : Prop := (t = 0 ∧ a = 0) ∨ (t = 0 ∧ a = 1) ∨ (t = 2 ∧ a = 2)

/-- **Positive instance**: the system `0 → 2` corresponds to the system `0 → 1 → 2`. The source step is
realized by a target path of length two, whose first step is read back as no step. -/
def expanding : OperationalCorrespondence skipTarget skipSource where
  related := expandRelated
  readStep := by
    intro t a a' related stepped
    obtain ⟨small, rfl⟩ : skipSourceStep a a' := stepped
    rcases (related : expandRelated t a) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (Or.inr (Or.inl ⟨rfl, rfl⟩) : expandRelated 0 (0 + 1))
    · exact Or.inr ⟨(2 : ℕ), (show skipTargetStep 0 2 from ⟨rfl, rfl⟩),
        (Or.inr (Or.inr ⟨rfl, rfl⟩) : expandRelated 2 (1 + 1))⟩
    · exact absurd small (by decide)
  forward := by
    intro t t' a related stepped
    obtain ⟨rfl, rfl⟩ : skipTargetStep t t' := stepped
    rcases (related : expandRelated 0 a) with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨impossible, -⟩
    · exact ⟨(2 : ℕ), (executionPath_nonempty_iff_multiStep skipSource _ _).mpr
        (.step (show skipSourceStep 0 1 from ⟨by decide, rfl⟩)
          (.step (show skipSourceStep 1 2 from ⟨by decide, rfl⟩) (.refl _))),
        (Or.inr (Or.inr ⟨rfl, rfl⟩) : expandRelated 2 2)⟩
    · exact ⟨(2 : ℕ), (executionPath_nonempty_iff_multiStep skipSource _ _).mpr
        (.step (show skipSourceStep 1 2 from ⟨by decide, rfl⟩) (.refl _)),
        (Or.inr (Or.inr ⟨rfl, rfl⟩) : expandRelated 2 2)⟩
    · exact absurd impossible (by decide)

/-- The positive instance agrees on the observation, so it is a path bisimulation of the sum. -/
def expandingWitness : PathWitness (sumKit skipTarget skipSource Unit isTwo isTwo) :=
  pathWitness expanding Unit isTwo isTwo (by
    intro t a related o
    rcases (related : expandRelated t a) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [isTwo])

#print axioms eq_or_transGen_of_multiStep
#print axioms sumPath_inl
#print axioms pathWitness
#print axioms pathBisim_of_related
#print axioms correspondence_of_pathWitness
#print axioms skipWitness
#print axioms skipping_pathBisim
#print axioms skipping_not_readback
#print axioms expanding
#print axioms expandingWitness

end Mettapedia.GSLT.IndexedOperational.CorrespondencePathWitness
