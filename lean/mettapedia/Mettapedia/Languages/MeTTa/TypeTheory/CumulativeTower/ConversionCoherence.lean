import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.TypingGeneration

/-!
# Conversion coherence for declaration-aware presentations

This module isolates the constructor-level consequence of a conversion
metatheory.  It does not choose a normalizer or checker.  If conversion has a
Church--Rosser witness and declaration-specific root rules do not rewrite a
Pi or universe head at the root, then Pi components are injective and Pi is
disjoint from universe heads.

The result is reusable for every declaration-aware presentation.  Native
indexed families instantiate only the root-neutrality side; proving their
beta/iota Church--Rosser property remains a separate metatheorem.
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace ConversionCoherence

/-- Forward multi-step computation for one presentation. -/
abbrev StepStar (rules : Rules Head) (source target : Tm Head n) : Prop :=
  Relation.ReflTransGen
    (StepCore rules.computation rules.headEq) source target

/-- Church--Rosser stated directly for the conversion relation used by the
declarative presentation. -/
abbrev ChurchRosser (rules : Rules Head) : Prop :=
  ∀ {n : Nat} {left right : Tm Head n},
    Conv rules.headEq left right rules.computation →
      ∃ common,
        StepStar rules left common ∧ StepStar rules right common

/-- Root equations are constructor-neutral at the two outer forms used to
separate function types from universe levels.  Computation inside their
components remains available through ordinary congruence. -/
structure RootPiHeadNeutral (rules : Rules Head) : Prop where
  pi {n : Nat} {domain : Tm Head n} {codomain : Tm Head (n + 1)}
      {target : Tm Head n} :
    ¬ rules.computation.step (.pi domain codomain) target
  head {n : Nat} {source : Head} {target : Tm Head n} :
    ¬ rules.computation.step (.head source) target

/-- A parallel reduction is useful for a presentation when it covers every
ordinary computation step and every parallel step is realized by a finite
ordinary computation.  The diamond law is deliberately kept separate: an
instance must prove it from its actual root equations and their overlaps. -/
structure ParallelSimulation (rules : Rules Head) where
  parallel : {n : Nat} → Tm Head n → Tm Head n → Prop
  ofStep {n : Nat} {source target : Tm Head n} :
    Step rules.headEq source target rules.computation →
      parallel source target
  realizes {n : Nat} {source target : Tm Head n} :
    parallel source target → StepStar rules source target

/-- One-step diamond for a presentation-specific parallel simulation. -/
abbrev ParallelDiamond {rules : Rules Head}
    (simulation : ParallelSimulation rules) : Prop :=
  ∀ {n : Nat} {source left right : Tm Head n},
    simulation.parallel source left →
    simulation.parallel source right →
      ∃ common,
        simulation.parallel left common ∧
        simulation.parallel right common

/-- Reflexive-transitive closure of a presentation-specific parallel
reduction. -/
abbrev ParallelStar {rules : Rules Head}
    (simulation : ParallelSimulation rules)
    (source target : Tm Head n) : Prop :=
  Relation.ReflTransGen simulation.parallel source target

private theorem singleStep
    {rules : Rules Head} {source target : Tm Head n}
    (step : Step rules.headEq source target rules.computation) :
    StepStar rules source target :=
  Relation.ReflTransGen.tail (Relation.ReflTransGen.refl) step

/-- Every ordinary multi-step computation is covered by the closure of a
parallel simulation. -/
theorem stepStar_to_parallelStar
    {rules : Rules Head} (simulation : ParallelSimulation rules)
    {source target : Tm Head n} (steps : StepStar rules source target) :
    ParallelStar simulation source target := by
  induction steps with
  | refl => exact Relation.ReflTransGen.refl
  | tail priorSteps finalStep ih =>
      exact Relation.ReflTransGen.tail ih (simulation.ofStep finalStep)

/-- The closure of a parallel simulation is realized by ordinary multi-step
computation. -/
theorem parallelStar_to_stepStar
    {rules : Rules Head} (simulation : ParallelSimulation rules)
    {source target : Tm Head n}
    (steps : ParallelStar simulation source target) :
    StepStar rules source target := by
  induction steps with
  | refl => exact Relation.ReflTransGen.refl
  | tail priorSteps finalStep ih =>
      exact Relation.ReflTransGen.trans ih
        (simulation.realizes finalStep)

/-- A one-step diamond lifts to confluence of the parallel closure. -/
theorem parallelStar_confluence
    {rules : Rules Head} (simulation : ParallelSimulation rules)
    (diamond : ParallelDiamond simulation)
    {source left right : Tm Head n}
    (leftSteps : ParallelStar simulation source left)
    (rightSteps : ParallelStar simulation source right) :
    ∃ common,
      ParallelStar simulation left common ∧
      ParallelStar simulation right common := by
  have localJoin : ∀ (a b c : Tm Head n),
      simulation.parallel a b → simulation.parallel a c →
        ∃ d,
          Relation.ReflGen simulation.parallel b d ∧
          Relation.ReflTransGen simulation.parallel c d := by
    intro a b c first second
    rcases diamond first second with ⟨d, firstJoin, secondJoin⟩
    exact
      ⟨d, Relation.ReflGen.single firstJoin,
        Relation.ReflTransGen.tail Relation.ReflTransGen.refl secondJoin⟩
  exact Relation.church_rosser localJoin leftSteps rightSteps

/-- A parallel simulation with a diamond proves Church--Rosser for the
presentation's actual conversion relation.  This is the reusable abstract
part of the complete-development argument; no particular root computation
or checker is selected here. -/
theorem churchRosserOfParallelDiamond
    {rules : Rules Head} (simulation : ParallelSimulation rules)
    (diamond : ParallelDiamond simulation) : ChurchRosser rules := by
  intro n source target conversion
  refine Relation.EqvGen.rec ?_ ?_ ?_ ?_ conversion
  · intro left right step
    exact ⟨right, singleStep step, Relation.ReflTransGen.refl⟩
  · intro term
    exact ⟨term, Relation.ReflTransGen.refl,
      Relation.ReflTransGen.refl⟩
  · intro left right _ inductionHypothesis
    rcases inductionHypothesis with ⟨common, leftSteps, rightSteps⟩
    exact ⟨common, rightSteps, leftSteps⟩
  · intro left middle right _ _ firstHypothesis secondHypothesis
    rcases firstHypothesis with
      ⟨firstCommon, leftSteps, middleFirstSteps⟩
    rcases secondHypothesis with
      ⟨secondCommon, middleSecondSteps, rightSteps⟩
    rcases parallelStar_confluence simulation diamond
        (stepStar_to_parallelStar simulation middleFirstSteps)
        (stepStar_to_parallelStar simulation middleSecondSteps) with
      ⟨finalCommon, firstJoin, secondJoin⟩
    exact
      ⟨finalCommon,
        Relation.ReflTransGen.trans leftSteps
          (parallelStar_to_stepStar simulation firstJoin),
        Relation.ReflTransGen.trans rightSteps
          (parallelStar_to_stepStar simulation secondJoin)⟩

/-- Every forward multi-step path is conversion evidence. -/
theorem stepStar_implies_conv
    {rules : Rules Head} {source target : Tm Head n}
    (steps : StepStar rules source target) :
    Conv rules.headEq source target rules.computation := by
  induction steps with
  | refl => exact Relation.EqvGen.refl _
  | tail priorSteps finalStep ih =>
      exact Relation.EqvGen.trans _ _ _ ih
        (Relation.EqvGen.rel _ _ finalStep)

private theorem step_pi_decomp
    {rules : Rules Head} (neutral : RootPiHeadNeutral rules)
    {domain : Tm Head n} {codomain : Tm Head (n + 1)}
    {target : Tm Head n}
    (step : Step rules.headEq (.pi domain codomain) target
      rules.computation) :
    ∃ domain' codomain',
      target = .pi domain' codomain' ∧
      StepStar rules domain domain' ∧
      StepStar rules codomain codomain' := by
  cases step with
  | root rootStep => exact False.elim (neutral.pi rootStep)
  | congPiDom inner =>
      exact ⟨_, _, rfl, singleStep inner, Relation.ReflTransGen.refl⟩
  | congPiCod inner =>
      exact ⟨_, _, rfl, Relation.ReflTransGen.refl, singleStep inner⟩

/-- Forward reduction from a Pi preserves its outer constructor and exposes
the complete component paths. -/
theorem stepStar_pi_decomp
    {rules : Rules Head} (neutral : RootPiHeadNeutral rules)
    {domain : Tm Head n} {codomain : Tm Head (n + 1)}
    {target : Tm Head n}
    (steps : StepStar rules (.pi domain codomain) target) :
    ∃ domain' codomain',
      target = .pi domain' codomain' ∧
      StepStar rules domain domain' ∧
      StepStar rules codomain codomain' := by
  induction steps with
  | refl =>
      exact ⟨domain, codomain, rfl,
        Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | tail priorSteps finalStep ih =>
      rcases ih with ⟨middleDomain, middleCodomain, rfl,
        domainSteps, codomainSteps⟩
      rcases step_pi_decomp neutral finalStep with
        ⟨targetDomain, targetCodomain, rfl,
          finalDomain, finalCodomain⟩
      exact
        ⟨targetDomain, targetCodomain, rfl,
          Relation.ReflTransGen.trans domainSteps finalDomain,
          Relation.ReflTransGen.trans codomainSteps finalCodomain⟩

private theorem step_head_shape
    {rules : Rules Head} (neutral : RootPiHeadNeutral rules)
    {source : Head} {target : Tm Head n}
    (step : Step rules.headEq (.head source) target rules.computation) :
    ∃ targetHead, target = .head targetHead := by
  cases step with
  | head equality => exact ⟨_, rfl⟩
  | root rootStep => exact False.elim (neutral.head rootStep)

/-- Forward reduction from a universe head remains a universe head. -/
theorem stepStar_head_shape
    {rules : Rules Head} (neutral : RootPiHeadNeutral rules)
    {source : Head} {target : Tm Head n}
    (steps : StepStar rules (.head source) target) :
    ∃ targetHead, target = .head targetHead := by
  induction steps with
  | refl => exact ⟨source, rfl⟩
  | tail priorSteps finalStep ih =>
      rcases ih with ⟨middleHead, rfl⟩
      exact step_head_shape neutral finalStep

/-- Church--Rosser plus root constructor-neutrality yields precisely the Pi
conversion boundary used by cumulative typing generation. -/
def piConversionBoundaryOfChurchRosser
    {rules : Rules Head} (neutral : RootPiHeadNeutral rules)
    (churchRosser : ChurchRosser rules) : PiConversionBoundary rules where
  components := by
    intro n domain₁ domain₂ codomain₁ codomain₂ conversion
    rcases churchRosser conversion with
      ⟨common, firstSteps, secondSteps⟩
    rcases stepStar_pi_decomp neutral firstSteps with
      ⟨commonDomain₁, commonCodomain₁, firstShape,
        firstDomain, firstCodomain⟩
    rcases stepStar_pi_decomp neutral secondSteps with
      ⟨commonDomain₂, commonCodomain₂, secondShape,
        secondDomain, secondCodomain⟩
    have shapeEquality :
        (.pi commonDomain₁ commonCodomain₁ : Tm Head n) =
          .pi commonDomain₂ commonCodomain₂ :=
      firstShape.symm.trans secondShape
    injection shapeEquality with domainEquality codomainEquality
    subst commonDomain₂
    subst commonCodomain₂
    exact
      ⟨ Relation.EqvGen.trans _ _ _
          (stepStar_implies_conv firstDomain)
          (Relation.EqvGen.symm _ _
            (stepStar_implies_conv secondDomain))
      , Relation.EqvGen.trans _ _ _
          (stepStar_implies_conv firstCodomain)
          (Relation.EqvGen.symm _ _
            (stepStar_implies_conv secondCodomain)) ⟩
  headDisjoint := by
    intro n domain codomain head conversion
    rcases churchRosser conversion with
      ⟨common, piSteps, headSteps⟩
    rcases stepStar_pi_decomp neutral piSteps with
      ⟨commonDomain, commonCodomain, piShape, _, _⟩
    rcases stepStar_head_shape neutral headSteps with
      ⟨commonHead, headShape⟩
    rw [piShape] at headShape
    cases headShape

/-! ## Controls -/

/-- Positive interface control: the constructed boundary exposes Pi
component conversion exactly as promised. -/
theorem piComponentsOfChurchRosser
    {rules : Rules Head} (neutral : RootPiHeadNeutral rules)
    (churchRosser : ChurchRosser rules)
    {domain₁ domain₂ : Tm Head n}
    {codomain₁ codomain₂ : Tm Head (n + 1)}
    (conversion : Conv rules.headEq (.pi domain₁ codomain₁)
      (.pi domain₂ codomain₂) rules.computation) :
    Conv rules.headEq domain₁ domain₂ rules.computation ∧
      Conv rules.headEq codomain₁ codomain₂ rules.computation :=
  (piConversionBoundaryOfChurchRosser neutral churchRosser).components
    conversion

/-- Negative interface control: the same hypotheses rule out a Pi/head
collapse, rather than merely omitting a way to construct one. -/
theorem noPiHeadCollapseOfChurchRosser
    {rules : Rules Head} (neutral : RootPiHeadNeutral rules)
    (churchRosser : ChurchRosser rules)
    {domain : Tm Head n} {codomain : Tm Head (n + 1)} {head : Head} :
    ¬ Conv rules.headEq (.pi domain codomain) (.head head)
      rules.computation :=
  (piConversionBoundaryOfChurchRosser neutral churchRosser).headDisjoint

/-! ## Axiom audit -/

#print axioms stepStar_implies_conv
#print axioms stepStar_to_parallelStar
#print axioms parallelStar_to_stepStar
#print axioms parallelStar_confluence
#print axioms churchRosserOfParallelDiamond
#print axioms stepStar_pi_decomp
#print axioms stepStar_head_shape
#print axioms piConversionBoundaryOfChurchRosser
#print axioms piComponentsOfChurchRosser
#print axioms noPiHeadCollapseOfChurchRosser

end ConversionCoherence
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
