import Mettapedia.GSLT.Distinction.BehaviouralMetric
import Mettapedia.GSLT.Distinction.RouteGrades
import Mettapedia.GSLT.Core.IndexedOperational

/-!
# Observation-preserving functional bisimulations are isometries

A map between the terms of two graded systems over GSLTs
(`GradedSystem`) is an **observation-preserving functional bisimulation**
(`ObservationBisimulation`) when it respects the equations, carries each
labelled step to a labelled step under a translation of labels, lifts every
labelled step leaving an image term to a source step whose image is equated
with the target endpoint, preserves each graded reading under a translation of
observation names, and keeps the discount.  It is the graded, labelled form of
the zig-zag maps of `GSLT.Core.FunctionalBisimulation`.

* **No loss** (`logicalDistance_le_map`): every formula translates forward with
  the same values (`eval_translate`), so the logical distance of two terms is at
  most that of their images.
* **Common vocabulary**: when the translations of observation names and labels
  are surjective, so that the target reads nothing the source does not, every
  target formula pulls back with the same values (`eval_pullback`), and the
  logical distances of mapped pairs agree (`logicalDistance_map`).
* **The image and its branching** (`image_stepClosed`,
  `image_finitelyBranching`): the target terms equated with images are closed
  under labelled steps, and they have finitely many successor classes as soon
  as the source has.  Nothing is claimed about target terms outside the image.
* **Behavioural distances agree** (`behaviouralDistance_map`), under finite
  branching of the source, through the quantitative Hennessy–Milner theorem on
  the image region.
* **Zero two-sided distortion** (`distortsAtMost_graph`): the graph of the map
  is a route of grade one between the behavioural observers.
* **The existing translations** (`ofCoveredTranslation`,
  `toOperationalTranslation`): on the stepping systems of two GSLTs, a covered
  translation preserving the graded readings is such a map, and such a map is a
  forward operational translation.

The controls, one for each dropped requirement, are in `IsometryControls`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.IndexedOperational

universe uS uT uP uA uL uO uA' uL' uO' uA'' uL'' uO''

set_option linter.checkUnivs false in
/-- An **observation-preserving functional bisimulation** between graded
systems: equations, labelled steps and graded readings are preserved, labelled
steps leaving images lift up to the target equations, and the discount is
kept. -/
structure ObservationBisimulation {S : GSLT.{uS}} {T : GSLT.{uT}}
    (Q : GradedSystem.{uS, uA, uL, uO} S) (R : GradedSystem.{uT, uA', uL', uO'} T) where
  /-- The term map. -/
  mapTerm : S.Term → T.Term
  mapEquiv : ∀ {left right : S.Term}, S.Equiv left right →
    T.Equiv (mapTerm left) (mapTerm right)
  /-- The translation of observation names. -/
  atom : Q.observations.Atom → R.observations.Atom
  /-- The translation of labels. -/
  label : Q.dynamics.Label → R.dynamics.Label
  discount_eq : Q.discount = R.discount
  value_map : ∀ observation term,
    R.observations.value (atom observation) (mapTerm term) = Q.observations.value observation term
  mapAct : ∀ step ⦃term target : S.Term⦄, Q.dynamics.act step term target →
    R.dynamics.act (label step) (mapTerm term) (mapTerm target)
  liftAct : ∀ step ⦃term : S.Term⦄ ⦃target' : T.Term⦄,
    R.dynamics.act (label step) (mapTerm term) target' →
      ∃ target, Q.dynamics.act step term target ∧ T.Equiv (mapTerm target) target'

namespace ObservationBisimulation

variable {S : GSLT.{uS}} {T : GSLT.{uT}} {Q : GradedSystem.{uS, uA, uL, uO} S}
  {R : GradedSystem.{uT, uA', uL', uO'} T} (map : ObservationBisimulation Q R)

/-! ## Formulas forward -/

/-- Translate a formula along the vocabulary maps. -/
def translate : Q.Formula → R.Formula
  | .top => .top
  | .atom observation => .atom (map.atom observation)
  | .neg inner => .neg (translate inner)
  | .conj left right => .conj (translate left) (translate right)
  | .shift threshold inner => .shift threshold (translate inner)
  | .dia step inner => .dia (map.label step) (translate inner)

/-- **Formula values are preserved.** -/
theorem eval_translate : ∀ (formula : Q.Formula) (term : S.Term),
    R.eval (map.translate formula) (map.mapTerm term) = Q.eval formula term
  | .top, _ => rfl
  | .atom observation, term => map.value_map observation term
  | .neg inner, term => by
      simp only [translate, GradedSystem.eval_neg, eval_translate inner term]
  | .conj left right, term => by
      simp only [translate, GradedSystem.eval_conj, eval_translate left term,
        eval_translate right term]
  | .shift threshold inner, term => by
      simp only [translate, GradedSystem.eval_shift, eval_translate inner term]
  | .dia step inner, term => by
      simp only [translate, GradedSystem.eval_dia]
      rw [map.discount_eq]
      congr 2
      ext value
      constructor
      · rintro ⟨target', targetStep, rfl⟩
        obtain ⟨target, sourceStep, equivalent⟩ := map.liftAct step targetStep
        refine ⟨target, sourceStep, ?_⟩
        rw [← eval_translate inner target]
        exact R.eval_resp _ equivalent
      · rintro ⟨target, sourceStep, rfl⟩
        exact ⟨map.mapTerm target, map.mapAct step sourceStep, eval_translate inner target⟩

/-- **No loss**: the image of a pair is at least as far apart. -/
theorem logicalDistance_le_map (left right : S.Term) :
    Q.logicalDistance left right ≤ R.logicalDistance (map.mapTerm left) (map.mapTerm right) :=
  Q.logicalDistance_le_iff.mpr fun formula => by
    rw [← map.eval_translate formula left, ← map.eval_translate formula right]
    exact R.abs_eval_sub_le_logicalDistance _ _ _

/-! ## Formulas back, for a common vocabulary -/

variable (atomSurjective : Function.Surjective map.atom)
  (labelSurjective : Function.Surjective map.label)

/-- Pull a target formula back along surjective vocabulary maps. -/
noncomputable def pullback : R.Formula → Q.Formula
  | .top => .top
  | .atom observation => .atom (Function.surjInv atomSurjective observation)
  | .neg inner => .neg (pullback inner)
  | .conj left right => .conj (pullback left) (pullback right)
  | .shift threshold inner => .shift threshold (pullback inner)
  | .dia step inner => .dia (Function.surjInv labelSurjective step) (pullback inner)

/-- Pulled-back formulas take the values of their targets at images. -/
theorem eval_pullback : ∀ (formula : R.Formula) (term : S.Term),
    Q.eval (map.pullback atomSurjective labelSurjective formula) term =
      R.eval formula (map.mapTerm term)
  | .top, _ => rfl
  | .atom observation, term => by
      simp only [pullback, GradedSystem.eval_atom]
      rw [← map.value_map, Function.surjInv_eq atomSurjective observation]
  | .neg inner, term => by
      simp only [pullback, GradedSystem.eval_neg, eval_pullback inner term]
  | .conj left right, term => by
      simp only [pullback, GradedSystem.eval_conj, eval_pullback left term,
        eval_pullback right term]
  | .shift threshold inner, term => by
      simp only [pullback, GradedSystem.eval_shift, eval_pullback inner term]
  | .dia step inner, term => by
      simp only [pullback, GradedSystem.eval_dia]
      rw [map.discount_eq]
      congr 2
      ext value
      have relabel := Function.surjInv_eq labelSurjective step
      constructor
      · rintro ⟨target, sourceStep, rfl⟩
        refine ⟨map.mapTerm target, ?_, (eval_pullback inner target).symm⟩
        have := map.mapAct _ sourceStep
        rwa [relabel] at this
      · rintro ⟨target', targetStep, rfl⟩
        rw [← relabel] at targetStep
        obtain ⟨target, sourceStep, equivalent⟩ := map.liftAct _ targetStep
        refine ⟨target, sourceStep, ?_⟩
        rw [eval_pullback inner target]
        exact R.eval_resp _ equivalent

/-- **Logical distances agree on mapped pairs.** -/
theorem logicalDistance_map (atomSurjective : Function.Surjective map.atom)
    (labelSurjective : Function.Surjective map.label) (left right : S.Term) :
    R.logicalDistance (map.mapTerm left) (map.mapTerm right) = Q.logicalDistance left right := by
  refine le_antisymm ?_ (map.logicalDistance_le_map left right)
  refine R.logicalDistance_le_iff.mpr fun formula => ?_
  rw [← map.eval_pullback atomSurjective labelSurjective formula left,
    ← map.eval_pullback atomSurjective labelSurjective formula right]
  exact Q.abs_eval_sub_le_logicalDistance _ _ _

/-! ## The image and its branching -/

/-- The target terms equated with an image. -/
def image : Set T.Term := {term' | ∃ term, T.Equiv (map.mapTerm term) term'}

theorem mapTerm_mem_image (term : S.Term) : map.mapTerm term ∈ map.image :=
  ⟨term, T.equations.iseqv.refl _⟩

/-- A labelled step out of an image term comes from a source step. -/
theorem lift_from_image (labelSurjective : Function.Surjective map.label) {term : S.Term} {term' target' : T.Term}
    (equivalent : T.Equiv (map.mapTerm term) term') (step : R.dynamics.Label)
    (targetStep : R.dynamics.act step term' target') :
    ∃ target, Q.dynamics.act (Function.surjInv labelSurjective step) term target ∧
      T.Equiv (map.mapTerm target) target' := by
  obtain ⟨target'', imageStep, close⟩ :=
    R.dynamics.act_resp_left (T.equations.iseqv.symm equivalent) targetStep
  rw [← Function.surjInv_eq labelSurjective step] at imageStep
  obtain ⟨target, sourceStep, lifted⟩ := map.liftAct _ imageStep
  exact ⟨target, sourceStep,
    T.equations.iseqv.trans lifted (T.equations.iseqv.symm close)⟩

/-- **The image is closed under labelled steps.** -/
theorem image_stepClosed (labelSurjective : Function.Surjective map.label) : R.StepClosed map.image := by
  rintro step _ target' ⟨term, equivalent⟩ targetStep
  obtain ⟨target, -, lifted⟩ := map.lift_from_image labelSurjective equivalent step targetStep
  exact ⟨target, lifted⟩

/-- **Finite branching on the image, from the source.** Image terms have
finitely many successor classes whenever the source has; the representatives
are images of source representatives. -/
theorem image_finitelyBranching (labelSurjective : Function.Surjective map.label)
    (finite : Q.dynamics.ImageFiniteModulo) :
    ∀ (step : R.dynamics.Label) ⦃term' : T.Term⦄, term' ∈ map.image →
      R.FinitelyBranchingAt step term' := by
  rintro step term' ⟨term, equivalent⟩
  obtain ⟨representatives, representativesFinite, covered⟩ :=
    finite (Function.surjInv labelSurjective step) term
  refine ⟨map.mapTerm '' representatives, representativesFinite.image _, ?_⟩
  intro target' targetStep
  obtain ⟨target, sourceStep, lifted⟩ :=
    map.lift_from_image labelSurjective equivalent step targetStep
  obtain ⟨representative, membership, close⟩ := covered sourceStep
  exact ⟨map.mapTerm representative, ⟨representative, membership, rfl⟩,
    T.equations.iseqv.trans (T.equations.iseqv.symm lifted) (map.mapEquiv close)⟩

/-- **Behavioural distances agree on mapped pairs**, under finite branching of
the source; the target is used only on the image of the map. -/
theorem behaviouralDistance_map (atomSurjective : Function.Surjective map.atom)
    (labelSurjective : Function.Surjective map.label)
    (finite : Q.dynamics.ImageFiniteModulo) (left right : S.Term) :
    R.behaviouralDistance (map.mapTerm left) (map.mapTerm right) =
      Q.behaviouralDistance left right := by
  rw [R.behaviouralDistance_eq_logicalDistance_on (map.image_stepClosed labelSurjective)
      (map.image_finitelyBranching labelSurjective finite)
      (map.mapTerm_mem_image left) (map.mapTerm_mem_image right),
    map.logicalDistance_map atomSurjective labelSurjective,
    Q.behaviouralDistance_eq_logicalDistance finite]

open RouteGrades in
/-- **The graph of the map has zero two-sided distortion** between the
behavioural observers. -/
theorem distortsAtMost_graph (atomSurjective : Function.Surjective map.atom)
    (labelSurjective : Function.Surjective map.label) :
    DistortsAtMost Q.toTolerance R.toTolerance (Route.graph map.mapTerm) 0 := by
  rintro left right _ _ rfl rfl
  rw [GradedSystem.toTolerance_distance, GradedSystem.toTolerance_distance,
    map.logicalDistance_map atomSurjective labelSurjective, sub_self, abs_zero]

end ObservationBisimulation

/-! ## Identity and composition -/

namespace ObservationBisimulation

variable {S : GSLT.{uS}} {T : GSLT.{uT}} {P : GSLT.{uP}}
  {Q : GradedSystem.{uS, uA, uL, uO} S} {R : GradedSystem.{uT, uA', uL', uO'} T}
  {W : GradedSystem.{uP, uA'', uL'', uO''} P}

/-- The identity is an observation-preserving functional bisimulation. -/
def identity (Q : GradedSystem.{uS, uA, uL, uO} S) : ObservationBisimulation Q Q where
  mapTerm := id
  mapEquiv := fun equivalent => equivalent
  atom := id
  label := id
  discount_eq := rfl
  value_map _ _ := rfl
  mapAct _ _ _ step := step
  liftAct _ _ target step := ⟨target, step, S.equations.iseqv.refl _⟩

/-- Observation-preserving functional bisimulations compose. -/
def comp (earlier : ObservationBisimulation Q R) (later : ObservationBisimulation R W) :
    ObservationBisimulation Q W where
  mapTerm := later.mapTerm ∘ earlier.mapTerm
  mapEquiv := fun equivalent => later.mapEquiv (earlier.mapEquiv equivalent)
  atom := later.atom ∘ earlier.atom
  label := later.label ∘ earlier.label
  discount_eq := earlier.discount_eq.trans later.discount_eq
  value_map observation term := by
    simp only [Function.comp_apply]
    rw [later.value_map, earlier.value_map]
  mapAct step _ _ sourceStep := later.mapAct _ (earlier.mapAct step sourceStep)
  liftAct step term target'' targetStep := by
    obtain ⟨middle, middleStep, middleClose⟩ := later.liftAct _ targetStep
    obtain ⟨target, sourceStep, sourceClose⟩ := earlier.liftAct step middleStep
    exact ⟨target, sourceStep,
      P.equations.iseqv.trans (later.mapEquiv sourceClose) middleClose⟩

end ObservationBisimulation

/-! ## The existing operational translations -/

section Stepping

variable {S : GSLT.{uS}}

/-- The stepping dynamics of a GSLT: one label, the GSLT's own step, as in
`HennessyMilner.System.ofObserved` without crisp atoms. -/
abbrev steppingDynamics (S : GSLT.{uS}) : System.{0, 0} S where
  Atom := Empty
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := Unit
  act _ := S.Step
  act_resp_left equivalent step := S.rewrites_resp_left equivalent step
  act_resp_right step equivalent := S.rewrites_resp_right step equivalent

/-- The graded system of a GSLT's own steps. -/
noncomputable abbrev GradedSystem.stepping (S : GSLT.{uS}) (observations : GradedObservations.{uS, uO} S)
    (discount : ℝ) (discount_nonneg : 0 ≤ discount) (discount_le_one : discount ≤ 1) :
    GradedSystem.{uS, 0, 0, uO} S where
  dynamics := steppingDynamics S
  observations := observations
  discount := discount
  discount_nonneg := discount_nonneg
  discount_le_one := discount_le_one

end Stepping

section Covered

universe u

variable {S T : GSLT.{u}} (observations : GradedObservations.{u, uO} S)
  (observations' : GradedObservations.{u, uO'} T) {discount : ℝ}
  (discount_nonneg : 0 ≤ discount) (discount_le_one : discount ≤ 1)

/-- **A covered translation that preserves the graded readings** is an
observation-preserving functional bisimulation of the stepping systems. -/
def ObservationBisimulation.ofCoveredTranslation (translation : CoveredTranslation S T)
    (atom : observations.Atom → observations'.Atom)
    (value_map : ∀ observation term,
      observations'.value (atom observation) (translation.mapTerm term) =
        observations.value observation term) :
    ObservationBisimulation (GradedSystem.stepping S observations discount discount_nonneg
        discount_le_one)
      (GradedSystem.stepping T observations' discount discount_nonneg discount_le_one) where
  mapTerm := translation.mapTerm
  mapEquiv := translation.mapEquiv
  atom := atom
  label := id
  discount_eq := rfl
  value_map := value_map
  mapAct _ _ _ step := translation.cover.mapStep step
  liftAct _ _ _ step := by
    obtain ⟨target, sourceStep, equal⟩ := translation.cover.liftStep step
    exact ⟨target, sourceStep, equal ▸ T.equations.iseqv.refl _⟩

/-- Between stepping systems, an observation-preserving functional bisimulation
is a forward operational translation. -/
def ObservationBisimulation.toOperationalTranslation
    (map : ObservationBisimulation
      (GradedSystem.stepping S observations discount discount_nonneg discount_le_one)
      (GradedSystem.stepping T observations' discount discount_nonneg discount_le_one)) :
    OperationalTranslation S T where
  mapTerm := map.mapTerm
  mapEquiv := map.mapEquiv
  mapStep := fun step => map.mapAct () step

end Covered

end Mettapedia.GSLT.Distinction
