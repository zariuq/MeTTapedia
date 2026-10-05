import Mettapedia.GSLT.Distinction.Isometry
import Mettapedia.GSLT.Distinction.BehaviouralMetricControls

/-!
# Controls for the isometry theorem

* **Positive, image only** (`quadIntoChains_behaviouralDistance`).  The two
  one-step processes of `BehaviouralMetricControls` embed into a target that
  also contains the infinitely branching chains of
  `HennessyMilner.ImageFinitenessNecessary`.  The target is not image-finite
  (`withChains_not_imageFinite`), yet the processes stay at behavioural distance
  `1/2`: finite branching is needed, and proved, on the image only.
* **Steps only** (`stepsOnly_control`).  A map that respects the equations,
  preserves every step and every reading, but meets an extra target step at an
  image, carries two terms at distance `0` to terms at distance `1`.
* **Unlabelled bisimilarity only** (`unlabelled_control`).  Two systems with the
  same unlabelled steps, one labelling two steps differently and one alike:
  the identity preserves unlabelled behaviour and changes the distance from `1`
  to `0`.
* **Zero kernels only** (`zeroKernel_control`).  Readings `0, 1/2` against
  `0, 1` with no steps: the zero kernels agree and the distances are `1/2`
  and `1`.
* **An extra target observation** (`extraObservation_control`).  Every
  requirement of `ObservationBisimulation` holds, the translation of
  observation names is not surjective, and the distance grows from `0` to `1`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.IsometryControls

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.HennessyMilner.ImageFinitenessNecessary
open Mettapedia.GSLT.Distinction
open Mettapedia.GSLT.Distinction.BehaviouralMetricControls

/-! ## Positive: the processes inside a target with an infinitely branching part -/

/-- The steps of the two processes and of the chains, side by side. -/
inductive WithChainsStep : Quad ⊕ St → Quad ⊕ St → Prop where
  | quad {source target : Quad} : QuadStep source target → WithChainsStep (.inl source) (.inl target)
  | chain {source target : St} : Step source target → WithChainsStep (.inr source) (.inr target)

/-- The GSLT of both. -/
abbrev withChains : GSLT.{0} where
  Term := Quad ⊕ St
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := WithChainsStep
  rewrites_resp_left := by
    intro _ _ target equal step
    exact ⟨target, equal ▸ step, rfl⟩
  rewrites_resp_right := by
    intro _ _ _ step equal
    exact equal ▸ step

/-- One label, no crisp atoms. -/
abbrev withChainsSystem : System.{0, 0} withChains where
  Atom := Empty
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := Unit
  act _ := WithChainsStep
  act_resp_left := by
    intro _ _ _ target equal step
    exact ⟨target, equal ▸ step, rfl⟩
  act_resp_right := by
    intro _ _ _ _ step equal
    exact equal ▸ step

/-- The process reading on the processes, `0` on the chains. -/
noncomputable def withChainsValue : Quad ⊕ St → ℝ
  | .inl state => quadValue state
  | .inr _ => 0

/-- The single reading. -/
noncomputable abbrev withChainsReading : GradedObservations.{0, 0} withChains where
  Atom := Unit
  value _ state := withChainsValue state
  value_nonneg _ state := by
    cases state with
    | inl state => cases state <;> norm_num [withChainsValue, quadValue]
    | inr _ => exact le_rfl
  value_le_one _ state := by
    cases state with
    | inl state => cases state <;> norm_num [withChainsValue, quadValue]
    | inr _ => exact zero_le_one
  value_resp _ _ _ equal := congrArg withChainsValue equal

/-- The undiscounted graded system of both. -/
noncomputable abbrev withChainsGraded : GradedSystem.{0, 0, 0, 0} withChains where
  dynamics := withChainsSystem
  observations := withChainsReading
  discount := 1
  discount_nonneg := zero_le_one
  discount_le_one := le_rfl

/-- **The processes embed** as an observation-preserving functional
bisimulation. -/
def quadIntoChains : ObservationBisimulation quadGraded withChainsGraded where
  mapTerm := Sum.inl
  mapEquiv := fun equal => congrArg Sum.inl equal
  atom := id
  label := id
  discount_eq := rfl
  value_map _ _ := rfl
  mapAct _ _ _ step := WithChainsStep.quad step
  liftAct _ _ _ step := by
    change WithChainsStep (.inl _) _ at step
    cases step with
    | quad sourceStep => exact ⟨_, sourceStep, rfl⟩

/-- The processes have finitely many successors. -/
theorem quadGraded_imageFinite : quadGraded.dynamics.ImageFiniteModulo := by
  intro _ _
  refine ⟨{Quad.firstDone, Quad.secondDone}, Set.toFinite _, ?_⟩
  intro target step
  change QuadStep _ target at step
  cases step
  · exact ⟨Quad.firstDone, by simp, rfl⟩
  · exact ⟨Quad.secondDone, by simp, rfl⟩

/-- **The target is not image-finite**: the chain part branches infinitely. -/
theorem withChains_not_imageFinite : ¬ withChainsGraded.dynamics.ImageFiniteModulo := by
  intro finite
  obtain ⟨representatives, representativesFinite, covered⟩ := finite () (Sum.inr St.left)
  have contains : Set.range (fun n : ℕ => (Sum.inr (St.chain n) : Quad ⊕ St)) ⊆
      representatives := by
    rintro _ ⟨n, rfl⟩
    obtain ⟨representative, membership, equal⟩ :=
      covered (WithChainsStep.chain (Step.leftChain n))
    change (Sum.inr (St.chain n) : Quad ⊕ St) = representative at equal
    show (Sum.inr (St.chain n) : Quad ⊕ St) ∈ representatives
    rw [equal]
    exact membership
  have injective : Function.Injective fun n : ℕ => (Sum.inr (St.chain n) : Quad ⊕ St) := by
    intro first second equal
    simp only [Sum.inr.injEq, St.chain.injEq] at equal
    exact equal
  exact (Set.infinite_range_of_injective injective) (representativesFinite.subset contains)

/-- **Image-only metric transport.** The embedded processes stay at behavioural
distance `1/2` although the target as a whole is not image-finite. -/
theorem quadIntoChains_behaviouralDistance :
    withChainsGraded.behaviouralDistance (.inl .first) (.inl .second) = 1 / 2 ∧
      ¬ withChainsGraded.dynamics.ImageFiniteModulo := by
  refine ⟨?_, withChains_not_imageFinite⟩
  have transported := quadIntoChains.behaviouralDistance_map
    (fun observation => ⟨observation, rfl⟩) (fun step => ⟨step, rfl⟩) quadGraded_imageFinite
    Quad.first Quad.second
  rw [quad_behaviouralDistance.1] at transported
  exact transported

/-! ## Two states without steps or with one extra step -/

/-- A GSLT whose equations are equality. -/
abbrev plainGSLT (Term : Type) (step : Term → Term → Prop) : GSLT.{0} where
  Term := Term
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := step
  rewrites_resp_left := by
    intro _ _ target equal stepped
    exact ⟨target, equal ▸ stepped, rfl⟩
  rewrites_resp_right := by
    intro _ _ _ stepped equal
    exact equal ▸ stepped

/-- A labelled system on a plain GSLT, without crisp atoms. -/
abbrev plainSystem (Term : Type) (step : Term → Term → Prop) (Label : Type)
    (act : Label → Term → Term → Prop) : System.{0, 0} (plainGSLT Term step) where
  Atom := Empty
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := Label
  act := act
  act_resp_left := by
    intro _ _ _ target equal stepped
    exact ⟨target, equal ▸ stepped, rfl⟩
  act_resp_right := by
    intro _ _ _ _ stepped equal
    exact equal ▸ stepped

/-- Two states, no steps. -/
abbrev pair : GSLT.{0} := plainGSLT Bool fun _ _ => False

/-- Two states and a self-loop at `true`. -/
abbrev loopAtTrue : GSLT.{0} := plainGSLT Bool fun source target => source = true ∧ target = true

/-- No graded observations on a GSLT whose equations are equality. -/
def noReadings (S : GSLT.{0}) : GradedObservations.{0, 0} S where
  Atom := Empty
  value atom _ := atom.elim
  value_nonneg atom _ := atom.elim
  value_le_one atom _ := atom.elim
  value_resp atom := atom.elim

/-- The pair without steps, as an undiscounted graded system. -/
noncomputable abbrev pairGraded : GradedSystem.{0, 0, 0, 0} pair where
  dynamics := plainSystem Bool (fun _ _ => False) Unit (fun _ _ _ => False)
  observations := noReadings pair
  discount := 1
  discount_nonneg := zero_le_one
  discount_le_one := le_rfl

/-- The loop at `true`, as an undiscounted graded system. -/
noncomputable abbrev loopGraded : GradedSystem.{0, 0, 0, 0} loopAtTrue where
  dynamics := plainSystem Bool (fun source target => source = true ∧ target = true) Unit
    (fun _ source target => source = true ∧ target = true)
  observations := noReadings loopAtTrue
  discount := 1
  discount_nonneg := zero_le_one
  discount_le_one := le_rfl

theorem pairGraded_zero : pairGraded.logicalDistance false true = 0 :=
  pairGraded.logicalDistance_eq_zero_of_gradedBisimilar
    ⟨fun _ _ => True, ⟨fun _ _ _ _ _ step => step.elim, fun _ _ _ _ _ step => step.elim,
      fun _ _ _ atom => atom.elim⟩, trivial⟩

theorem loopGraded_one : loopGraded.logicalDistance false true = 1 := by
  refine le_antisymm (loopGraded.logicalDistance_le_one _ _) ?_
  have probe := loopGraded.abs_eval_sub_le_logicalDistance (.dia () .top) false true
  have atTrue : loopGraded.successors () true = {true} := by
    ext target
    constructor
    · rintro ⟨-, rfl⟩
      rfl
    · rintro rfl
      exact ⟨rfl, rfl⟩
  have atFalse : loopGraded.successors () false = ∅ := by
    ext target
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨absurd, -⟩
    cases absurd
  rw [GradedSystem.eval_dia, GradedSystem.eval_dia, atTrue, atFalse, Set.image_empty,
    Set.image_singleton, Real.sSup_empty, csSup_singleton, GradedSystem.eval_top] at probe
  norm_num at probe
  exact probe

/-- **Steps only is not enough.** The identity respects the equations,
preserves every step (there are none) and every reading (there are none), and
carries two terms at distance `0` to terms at distance `1`: a step at an image
has no source lift. -/
theorem stepsOnly_control :
    (∀ source target : Bool, pairGraded.dynamics.act () source target →
        loopGraded.dynamics.act () source target) ∧
      loopGraded.dynamics.act () true true ∧
      (∀ target, ¬ pairGraded.dynamics.act () true target) ∧
      pairGraded.logicalDistance false true = 0 ∧ loopGraded.logicalDistance false true = 1 :=
  ⟨fun _ _ step => step.elim, ⟨rfl, rfl⟩, fun _ step => step, pairGraded_zero, loopGraded_one⟩

/-! ## Unlabelled bisimilarity only -/

/-- The unlabelled steps of three states: two step to the third. -/
def toTwo (source target : Fin 3) : Prop := (source = 0 ∨ source = 1) ∧ target = 2

/-- Three states: two that step to the third. -/
abbrev three : GSLT.{0} := plainGSLT (Fin 3) toTwo

/-- The source labels the two steps differently. -/
def differentLabels (label : Bool) (source target : Fin 3) : Prop :=
  (source = 0 ∧ target = 2 ∧ label = true) ∨ (source = 1 ∧ target = 2 ∧ label = false)

/-- The target labels both alike. -/
def sameLabel (label : Bool) (source target : Fin 3) : Prop :=
  (source = 0 ∨ source = 1) ∧ target = 2 ∧ label = true

noncomputable abbrev differentGraded : GradedSystem.{0, 0, 0, 0} three where
  dynamics := plainSystem (Fin 3) toTwo Bool differentLabels
  observations := noReadings three
  discount := 1
  discount_nonneg := zero_le_one
  discount_le_one := le_rfl

noncomputable abbrev sameGraded : GradedSystem.{0, 0, 0, 0} three where
  dynamics := plainSystem (Fin 3) toTwo Bool sameLabel
  observations := noReadings three
  discount := 1
  discount_nonneg := zero_le_one
  discount_le_one := le_rfl

theorem differentGraded_one : differentGraded.logicalDistance 0 1 = 1 := by
  refine le_antisymm (differentGraded.logicalDistance_le_one _ _) ?_
  have probe := differentGraded.abs_eval_sub_le_logicalDistance (.dia true .top) 0 1
  have atZero : differentGraded.successors true 0 = {2} := by
    ext target
    simp only [GradedSystem.successors, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    change differentLabels true 0 target ↔ target = 2
    simp [differentLabels]
  have atOne : differentGraded.successors true 1 = ∅ := by
    ext target
    simp only [GradedSystem.successors, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    change ¬ differentLabels true 1 target
    simp [differentLabels]
  rw [GradedSystem.eval_dia, GradedSystem.eval_dia, atZero, atOne, Set.image_empty,
    Set.image_singleton, Real.sSup_empty, csSup_singleton, GradedSystem.eval_top] at probe
  norm_num at probe
  exact probe

theorem sameGraded_zero : sameGraded.logicalDistance 0 1 = 0 := by
  refine sameGraded.logicalDistance_eq_zero_of_gradedBisimilar
    ⟨fun first second => (first = 2 ↔ second = 2), ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, by decide⟩
  · intro first second related label first' step
    change sameLabel label first first' at step
    obtain ⟨sourceIs, rfl, rfl⟩ := step
    have notTwo : second ≠ 2 := by
      intro isTwo
      rcases sourceIs with rfl | rfl <;> simp_all
    refine ⟨2, ?_, Iff.rfl⟩
    change sameLabel true second 2
    refine ⟨?_, rfl, rfl⟩
    revert notTwo
    fin_cases second <;> simp
  · intro first second related label second' step
    change sameLabel label second second' at step
    obtain ⟨sourceIs, rfl, rfl⟩ := step
    have notTwo : first ≠ 2 := by
      intro isTwo
      rcases sourceIs with rfl | rfl <;> simp_all
    refine ⟨2, ?_, Iff.rfl⟩
    change sameLabel true first 2
    refine ⟨?_, rfl, rfl⟩
    revert notTwo
    fin_cases first <;> simp

/-- **Unlabelled bisimilarity is not enough.** Both systems have the same
unlabelled steps, so the identity preserves unlabelled behaviour; the
source separates the two states and the target does not. -/
theorem unlabelled_control :
    (∀ source target : Fin 3, (∃ label, differentLabels label source target) ↔
        (∃ label, sameLabel label source target)) ∧
      differentGraded.logicalDistance 0 1 = 1 ∧ sameGraded.logicalDistance 0 1 = 0 := by
  refine ⟨fun source target => ?_, differentGraded_one, sameGraded_zero⟩
  constructor
  · rintro ⟨_, (⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩)⟩
    · exact ⟨true, Or.inl rfl, rfl, rfl⟩
    · exact ⟨true, Or.inr rfl, rfl, rfl⟩
  · rintro ⟨_, (rfl | rfl), rfl, -⟩
    · exact ⟨true, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · exact ⟨false, Or.inr ⟨rfl, rfl, rfl⟩⟩

/-! ## Zero kernels only, and an extra observation -/

/-- One reading on two states. -/
def reading (atFalse atTrue : ℝ) (nonneg : 0 ≤ atFalse ∧ 0 ≤ atTrue)
    (le_one : atFalse ≤ 1 ∧ atTrue ≤ 1) : GradedObservations.{0, 0} pair where
  Atom := Unit
  value _ state := if state then atTrue else atFalse
  value_nonneg _ state := by cases state <;> simp [nonneg.1, nonneg.2]
  value_le_one _ state := by cases state <;> simp [le_one.1, le_one.2]
  value_resp _ _ _ equal := by rw [show _ = _ from equal]

/-- The pair without steps, with one reading. -/
noncomputable abbrev readGraded (atFalse atTrue : ℝ) (nonneg : 0 ≤ atFalse ∧ 0 ≤ atTrue)
    (le_one : atFalse ≤ 1 ∧ atTrue ≤ 1) : GradedSystem.{0, 0, 0, 0} pair where
  dynamics := plainSystem Bool (fun _ _ => False) Unit (fun _ _ _ => False)
  observations := reading atFalse atTrue nonneg le_one
  discount := 1
  discount_nonneg := zero_le_one
  discount_le_one := le_rfl

/-- Without steps the logical distance is the reading difference. -/
theorem readGraded_logicalDistance (atFalse atTrue : ℝ) (nonneg : 0 ≤ atFalse ∧ 0 ≤ atTrue)
    (le_one : atFalse ≤ 1 ∧ atTrue ≤ 1) :
    (readGraded atFalse atTrue nonneg le_one).logicalDistance false true = |atFalse - atTrue| := by
  refine le_antisymm ?_ ?_
  · have bisim : (readGraded atFalse atTrue nonneg le_one).IsBisimMetric fun first second =>
        |(if first then atTrue else atFalse) - (if second then atTrue else atFalse)| :=
      ⟨fun _ _ => abs_nonneg _, fun _ _ _ => le_rfl, fun _ _ _ _ step => step.elim,
        fun _ _ _ _ step => step.elim⟩
    exact (readGraded atFalse atTrue nonneg le_one).logicalDistance_le_of_isBisimMetric bisim
      false true
  · exact (readGraded atFalse atTrue nonneg le_one).abs_eval_sub_le_logicalDistance (.atom ())
      false true

/-- **Agreement of zero kernels is not enough.** Readings `0, 1/2` and `0, 1`
without steps: both observers separate the two states, so their zero kernels
agree; the distances are `1/2` and `1`. -/
theorem zeroKernel_control :
    let half := readGraded 0 (1 / 2) (by norm_num) (by norm_num)
    let full := readGraded 0 1 (by norm_num) (by norm_num)
    (∀ first second : Bool, half.logicalDistance first second = 0 ↔
        full.logicalDistance first second = 0) ∧
      half.logicalDistance false true = 1 / 2 ∧ full.logicalDistance false true = 1 := by
  intro half full
  have halfValue : half.logicalDistance false true = 1 / 2 := by
    rw [readGraded_logicalDistance]
    norm_num
  have fullValue : full.logicalDistance false true = 1 := by
    rw [readGraded_logicalDistance]
    norm_num
  refine ⟨fun first second => ?_, halfValue, fullValue⟩
  cases first <;> cases second
  · simp
  · rw [halfValue, fullValue]
    norm_num
  · rw [half.logicalDistance_symm, full.logicalDistance_symm, halfValue, fullValue]
    norm_num
  · simp

/-- **An extra target observation is not enough to keep an isometry.** The
identity on the pair without readings into the pair with one reading meets
every requirement of `ObservationBisimulation`; the translation of
observation names misses the extra reading, and the distance grows. -/
def unreadIntoRead :
    ObservationBisimulation pairGraded (readGraded 0 1 (by norm_num) (by norm_num)) where
  mapTerm := id
  mapEquiv := fun equal => equal
  atom := fun atom => atom.elim
  label := id
  discount_eq := rfl
  value_map atom _ := atom.elim
  mapAct _ _ _ step := step
  liftAct _ _ _ step := step.elim

theorem extraObservation_control :
    ¬ Function.Surjective unreadIntoRead.atom ∧
      pairGraded.logicalDistance false true = 0 ∧
      (readGraded 0 1 (by norm_num) (by norm_num)).logicalDistance
        (unreadIntoRead.mapTerm false) (unreadIntoRead.mapTerm true) = 1 := by
  refine ⟨fun surjective => (surjective ()).elim fun atom _ => atom.elim, pairGraded_zero, ?_⟩
  change (readGraded 0 1 _ _).logicalDistance false true = 1
  rw [readGraded_logicalDistance]
  norm_num

end Mettapedia.GSLT.Distinction.IsometryControls
