import Mettapedia.GSLT.Core.Ultrainfinite

/-!
# Two independent ultrainfinite doctrines

The word "ultrainfinite" has been used for two mathematically different
structures in the GSLT and NIK programme.

* A **generative-unbounded ground** is assembled through finite stages.  Each
  stage embeds in the next, genuinely new stage data remains available, and
  local observation agrees with observation after realization in the whole.
* An **ultrafilter-perspective ground** starts with a whole and projects it to
  indexed observations.  An ultrafilter then selects which coordinate family
  determines the verdict.  A nonprincipal view is extra structure, not a
  consequence of staged generation.

These are opposite variances around a whole: stages map into it, while views
read out from it.  `CombinedGround` carries both without identifying them.
The canaries prove that forgetting either coordinate loses genuine choices,
and exhibit a nonprincipal perspective separately from the principal ones.

This file factors capabilities.  It does not claim that either capability by
itself proves source soundness, checker fidelity, or physical correctness.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Ultrainfinite.DoctrineFactorization

open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.Logic.Metaphysics

universe uWhole uStage uLocalObservation
universe uPerspective uShadow uViewObservation

/-! ## Generative unboundedness -/

/-- A whole presented through a strictly growing sequence of finite stages,
with an observation that can be computed before passing to the whole. -/
structure GenerativeUnboundedGround
    (Whole : Type uWhole) (LocalObservation : Type uLocalObservation)
    (Stage : Nat → Type uStage) where
  stageFinite : ∀ level, Finite (Stage level)
  advance : ∀ level, Stage level → Stage (level + 1)
  realize : ∀ level, Stage level → Whole
  realize_injective : ∀ level, Function.Injective (realize level)
  realize_advance : ∀ level (stage : Stage level),
    realize (level + 1) (advance level stage) = realize level stage
  fresh : ∀ level,
    ∃ next : Stage (level + 1),
      ∀ previous : Stage level, advance level previous ≠ next
  observeWhole : Whole → LocalObservation
  observeStage : ∀ level, Stage level → LocalObservation
  observe_realize : ∀ level (stage : Stage level),
    observeStage level stage = observeWhole (realize level stage)

namespace GenerativeUnboundedGround

/-- Realization of the fresh next-stage element is outside the image of the
preceding stage.  Thus strict growth cannot be erased by realization. -/
theorem exists_realized_fresh
    {Whole : Type uWhole} {LocalObservation : Type uLocalObservation}
    {Stage : Nat → Type uStage}
    (ground : GenerativeUnboundedGround Whole LocalObservation Stage)
    (level : Nat) :
    ∃ next : Stage (level + 1),
      ∀ previous : Stage level,
        ground.realize (level + 1) next ≠ ground.realize level previous := by
  obtain ⟨next, fresh⟩ := ground.fresh level
  refine ⟨next, ?_⟩
  intro previous sameRealization
  apply fresh previous
  apply ground.realize_injective (level + 1)
  rw [ground.realize_advance level previous]
  exact sameRealization.symm

end GenerativeUnboundedGround

/-- A generative ground is exhaustive when every object of the ambient whole
is realized at some finite stage.  This is deliberately stronger than mere
unboundedness: strict growth alone need not present the entire semantic
carrier. -/
structure ExhaustiveGenerativeGround
    (Whole : Type uWhole) (LocalObservation : Type uLocalObservation)
    (Stage : Nat → Type uStage)
    extends GenerativeUnboundedGround Whole LocalObservation Stage where
  exhaustive : ∀ whole : Whole,
    ∃ level stage, realize level stage = whole

/-! ## Perspective-relative truth -/

/-- A projection system together with the ultrafilter selecting its semantic
perspective.  The projection retains the whole-to-shadow direction already
formalized by `PerspectiveProjection`. -/
structure UltrafilterPerspectiveGround
    (Whole : Type uWhole) (Perspective : Type uPerspective)
    (Shadow : Perspective → Type uShadow)
    (ViewObservation : Perspective → Type uViewObservation) where
  projection :
    PerspectiveProjection Whole Perspective Shadow ViewObservation
  view : Ultrafilter Perspective

namespace UltrafilterPerspectiveGround

/-- The proposition family observed through one perspective ground. -/
def verdictFamily
    {Whole : Type uWhole} {Perspective : Type uPerspective}
    {Shadow : Perspective → Type uShadow}
    {ViewObservation : Perspective → Type uViewObservation}
    (ground : UltrafilterPerspectiveGround Whole Perspective Shadow
      ViewObservation)
    (whole : Whole)
    (verdict : (perspective : Perspective) →
      ViewObservation perspective → Prop) : Perspective → Prop :=
  ground.projection.verdictFamily whole verdict

/-- Relative truth is ultrafilter truth of the projected verdict family. -/
def Meaning
    {Whole : Type uWhole} {Perspective : Type uPerspective}
    {Shadow : Perspective → Type uShadow}
    {ViewObservation : Perspective → Type uViewObservation}
    (ground : UltrafilterPerspectiveGround Whole Perspective Shadow
      ViewObservation)
    (whole : Whole)
    (verdict : (perspective : Perspective) →
      ViewObservation perspective → Prop) : Prop :=
  UltraTrue ground.view (ground.verdictFamily whole verdict)

end UltrafilterPerspectiveGround

/-- A genuinely infinite-primary view records that its selected ultrafilter is
not any principal coordinate. -/
structure NonprincipalPerspectiveGround
    (Whole : Type uWhole) (Perspective : Type uPerspective)
    (Shadow : Perspective → Type uShadow)
    (ViewObservation : Perspective → Type uViewObservation)
    extends UltrafilterPerspectiveGround Whole Perspective Shadow
      ViewObservation where
  nonprincipal : ∀ perspective, view ≠ pure perspective

/-! ## The product, without collapse -/

/-- Both doctrines may coexist over one whole, but remain separate fields. -/
structure CombinedGround
    (Whole : Type uWhole) (LocalObservation : Type uLocalObservation)
    (Stage : Nat → Type uStage) (Perspective : Type uPerspective)
    (Shadow : Perspective → Type uShadow)
    (ViewObservation : Perspective → Type uViewObservation) where
  generative : GenerativeUnboundedGround Whole LocalObservation Stage
  perspectival :
    UltrafilterPerspectiveGround Whole Perspective Shadow ViewObservation

/-! ## Nontrivial generative instances -/

/-- The level-`n` finite stage has exactly `n + 1` positions. -/
abbrev FiniteStage (level : Nat) := Fin (level + 1)

/-- The standard realization places each finite stage at its natural-number
coordinate. -/
def standardGeneration :
    GenerativeUnboundedGround Nat Nat FiniteStage where
  stageFinite := fun _level => inferInstance
  advance := fun _level stage => stage.castSucc
  realize := fun _level stage => stage.val
  realize_injective := by
    intro _level left right equalValues
    exact Fin.ext equalValues
  realize_advance := by
    intro _level _stage
    rfl
  fresh := by
    intro level
    refine ⟨Fin.last (level + 1), ?_⟩
    intro previous
    exact Fin.castSucc_ne_last previous
  observeWhole := id
  observeStage := fun _level stage => stage.val
  observe_realize := by
    intro _level _stage
    rfl

/-- A shifted realization has the same finite stages and inclusions, but
places the generated whole one coordinate later. -/
def shiftedGeneration :
    GenerativeUnboundedGround Nat Nat FiniteStage where
  stageFinite := fun _level => inferInstance
  advance := fun _level stage => stage.castSucc
  realize := fun _level stage => stage.val + 1
  realize_injective := by
    intro _level left right equalValues
    apply Fin.ext
    exact Nat.add_right_cancel equalValues
  realize_advance := by
    intro _level _stage
    rfl
  fresh := by
    intro level
    refine ⟨Fin.last (level + 1), ?_⟩
    intro previous
    exact Fin.castSucc_ne_last previous
  observeWhole := id
  observeStage := fun _level stage => stage.val + 1
  observe_realize := by
    intro _level _stage
    rfl

theorem standardGeneration_ne_shifted :
    standardGeneration ≠ shiftedGeneration := by
  intro equalGrounds
  have equalAtZero := congrArg
    (fun ground : GenerativeUnboundedGround Nat Nat FiniteStage =>
      ground.realize 0 (0 : FiniteStage 0))
    equalGrounds
  simp [standardGeneration, shiftedGeneration] at equalAtZero

/-! ## Principal and nonprincipal perspective instances -/

def booleanPerspectiveProjection :
    PerspectiveProjection Nat Bool (fun _ => Nat) (fun _ => Bool) where
  project := fun _perspective whole => whole
  observeWhole := fun perspective _whole => perspective
  observeShadow := fun perspective _shadow => perspective
  adequate := by
    intro _perspective _whole
    rfl

def falsePrincipalPerspective :
    UltrafilterPerspectiveGround Nat Bool (fun _ => Nat) (fun _ => Bool) where
  projection := booleanPerspectiveProjection
  view := pure false

def truePrincipalPerspective :
    UltrafilterPerspectiveGround Nat Bool (fun _ => Nat) (fun _ => Bool) where
  projection := booleanPerspectiveProjection
  view := pure true

theorem falsePrincipalPerspective_ne_truePrincipalPerspective :
    falsePrincipalPerspective ≠ truePrincipalPerspective := by
  intro equalGrounds
  have equalViews := congrArg
    (fun ground :
      UltrafilterPerspectiveGround Nat Bool (fun _ => Nat) (fun _ => Bool) =>
        ground.view)
    equalGrounds
  exact Bool.false_ne_true (Ultrafilter.pure_injective equalViews)

def naturalPerspectiveProjection :
    PerspectiveProjection Nat Nat (fun _ => Nat) (fun _ => Bool) where
  project := fun _perspective whole => whole
  observeWhole := fun perspective whole => decide (perspective ≠ whole)
  observeShadow := fun perspective shadow => decide (perspective ≠ shadow)
  adequate := by
    intro _perspective _whole
    rfl

theorem hyperfilter_nat_nonprincipal (perspective : Nat) :
    Filter.hyperfilter Nat ≠ (pure perspective : Ultrafilter Nat) := by
  intro equalViews
  have cofiniteVerdict :
      {coordinate : Nat | coordinate ≠ perspective} ∈
        Filter.hyperfilter Nat := by
    apply Filter.mem_hyperfilter_of_finite_compl
    have complement :
        {coordinate : Nat | coordinate ≠ perspective}ᶜ = {perspective} := by
      ext coordinate
      simp
    rw [complement]
    exact Set.finite_singleton perspective
  have principalRejects :
      {coordinate : Nat | coordinate ≠ perspective} ∉
        (pure perspective : Ultrafilter Nat) := by
    simp
  exact principalRejects (equalViews ▸ cofiniteVerdict)

/-- A genuinely nonprincipal infinite-primary perspective. -/
noncomputable def naturalNonprincipalPerspective :
    NonprincipalPerspectiveGround Nat Nat (fun _ => Nat) (fun _ => Bool) where
  projection := naturalPerspectiveProjection
  view := Filter.hyperfilter Nat
  nonprincipal := hyperfilter_nat_nonprincipal

theorem nonprincipal_affirms_positive_tail :
    naturalNonprincipalPerspective.toUltrafilterPerspectiveGround.Meaning 0
      (fun _perspective observation => observation = true) := by
  change UltraTrue (Filter.hyperfilter Nat)
    (fun perspective => decide (perspective ≠ 0) = true)
  simpa using hyperfilter_pure_disagree.1

/-! ## Neither coordinate determines the other -/

abbrev BooleanCombinedGround :=
  CombinedGround Nat Nat FiniteStage Bool (fun _ => Nat) (fun _ => Bool)

def standardFalseCombined : BooleanCombinedGround where
  generative := standardGeneration
  perspectival := falsePrincipalPerspective

def standardTrueCombined : BooleanCombinedGround where
  generative := standardGeneration
  perspectival := truePrincipalPerspective

def shiftedFalseCombined : BooleanCombinedGround where
  generative := shiftedGeneration
  perspectival := falsePrincipalPerspective

/-- The two doctrines also coexist nontrivially with a genuinely
nonprincipal semantic view. -/
abbrev NaturalCombinedGround :=
  CombinedGround Nat Nat FiniteStage Nat (fun _ => Nat) (fun _ => Bool)

noncomputable def standardNonprincipalCombined : NaturalCombinedGround where
  generative := standardGeneration
  perspectival :=
    naturalNonprincipalPerspective.toUltrafilterPerspectiveGround

/-- Forgetting perspective data is not injective, even when the complete
generative presentation is retained. -/
theorem generativeProjection_not_injective :
    ¬ (Function.Injective
      (fun ground : BooleanCombinedGround => ground.generative)) := by
  intro injective
  have equalCombined : standardFalseCombined = standardTrueCombined :=
    injective rfl
  have equalPerspectives := congrArg
    (fun ground : BooleanCombinedGround => ground.perspectival) equalCombined
  exact falsePrincipalPerspective_ne_truePrincipalPerspective equalPerspectives

/-- Forgetting staged generation is not injective, even when the complete
perspective semantics is retained. -/
theorem perspectivalProjection_not_injective :
    ¬ (Function.Injective
      (fun ground : BooleanCombinedGround => ground.perspectival)) := by
  intro injective
  have equalCombined : standardFalseCombined = shiftedFalseCombined :=
    injective rfl
  have equalGenerations := congrArg
    (fun ground : BooleanCombinedGround => ground.generative) equalCombined
  exact standardGeneration_ne_shifted equalGenerations

#print axioms GenerativeUnboundedGround.exists_realized_fresh
#print axioms standardGeneration_ne_shifted
#print axioms falsePrincipalPerspective_ne_truePrincipalPerspective
#print axioms hyperfilter_nat_nonprincipal
#print axioms nonprincipal_affirms_positive_tail
#print axioms generativeProjection_not_injective
#print axioms perspectivalProjection_not_injective

end Mettapedia.GSLT.Ultrainfinite.DoctrineFactorization
