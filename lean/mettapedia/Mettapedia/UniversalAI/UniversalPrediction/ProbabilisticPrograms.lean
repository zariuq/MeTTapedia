import Mettapedia.UniversalAI.UniversalPrediction.BitGeneratorSemimeasure

/-!
# Executable finite prediction over probabilistic generators

A catalogue assigns a nonnegative prior weight to each entry in its list.
Evidence is the observed output prefix, and an entry's likelihood is its
fair-tape probability of producing that prefix. At a finite cutoff all
terms are computed as rationals. A zero denominator at this cutoff leaves
the readout unresolved. The lower approximations are to masses, not to
the normalized posterior ratios.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAI.UniversalPrediction.ProbabilisticPrograms

open Mettapedia.Computability.BitGenerator
open Filter
open scoped ENNReal

structure Hypothesis (State : Type*) where
  prior : ℚ
  prior_nonneg : 0 ≤ prior
  program : Generator State Bool

variable {State : Type*} [DecidableEq State]

def Hypothesis.stageWeight (entry : Hypothesis State) (history : List Bool) (stage : Nat) : ℚ :=
  entry.prior * entry.program.stageMass history stage

def catalogueMass (family : List (Hypothesis State)) (history : List Bool) (stage : Nat) : ℚ :=
  (family.map fun entry => entry.stageWeight history stage).sum

def posteriorAt (family : List (Hypothesis State)) (history : List Bool) (stage : Nat) (index : Nat) :
    Option ℚ :=
  match family[index]? with
  | none => none
  | some entry =>
    let total := catalogueMass family history stage
    if total = 0 then none else some (entry.stageWeight history stage / total)

def predictAt (family : List (Hypothesis State)) (history : List Bool) (stage : Nat) (next : Bool) :
    Option ℚ :=
  let total := catalogueMass family history stage
  if total = 0 then none else some (catalogueMass family (history ++ [next]) stage / total)

/-- The exact mixture of emitted-prefix probabilities for this catalogue. -/
noncomputable def exactMass (family : List (Hypothesis State)) (history : List Bool) : ℝ :=
  (family.map fun entry => (entry.prior : ℝ) * (entry.program.semimeasure history).toReal).sum

theorem stageWeight_tendsto (entry : Hypothesis State) (history : List Bool) :
    Tendsto (fun stage => (entry.stageWeight history stage : ℝ)) atTop
      (nhds ((entry.prior : ℝ) * (entry.program.semimeasure history).toReal)) := by
  simpa only [Hypothesis.stageWeight, Rat.cast_mul] using
    (tendsto_const_nhds (x := (entry.prior : ℝ))).mul (entry.program.toReal_stageMass_tendsto history)

theorem catalogueMass_tendsto (family : List (Hypothesis State)) (history : List Bool) :
    Tendsto (fun stage => (catalogueMass family history stage : ℝ)) atTop
      (nhds (exactMass family history)) := by
  induction family with
  | nil => simp [catalogueMass, exactMass]
  | cons first rest ih =>
    simpa only [catalogueMass, exactMass, List.map_cons, List.sum_cons, Rat.cast_add] using
      (stageWeight_tendsto first history).add ih

/-- Once the observation has positive exact mass, finite predictions become
defined and converge to the ratio of prefix masses. -/
theorem predictAt_tendsto (family : List (Hypothesis State)) (history : List Bool) (next : Bool)
    (positive : 0 < exactMass family history) :
    (∀ᶠ stage in atTop, (predictAt family history stage next).isSome) ∧
    Tendsto (fun stage => ((predictAt family history stage next).getD 0 : ℝ)) atTop
      (nhds (exactMass family (history ++ [next]) / exactMass family history)) := by
  have converges := catalogueMass_tendsto family history
  have eventuallyPositive : ∀ᶠ stage in atTop, 0 < (catalogueMass family history stage : ℝ) :=
    (tendsto_order.mp converges).1 0 positive
  have eventuallyNonzero : ∀ᶠ stage in atTop, catalogueMass family history stage ≠ 0 :=
    eventuallyPositive.mono fun stage hp zero => by simp [zero] at hp
  constructor
  · exact eventuallyNonzero.mono fun stage hn => by simp [predictAt, hn]
  · refine ((catalogueMass_tendsto family (history ++ [next])).div converges positive.ne').congr' ?_
    exact eventuallyNonzero.mono fun stage hn => by simp [predictAt, hn, Rat.cast_div]

end Mettapedia.UniversalAI.UniversalPrediction.ProbabilisticPrograms
