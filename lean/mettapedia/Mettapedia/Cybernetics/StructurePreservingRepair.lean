import Mettapedia.Cybernetics.MultiscaleGoal

/-!
# Structure-preserving repair of represented misfit

Alexander treats design as adaptation between form and context and represents
failure negatively through explicit potential misfits.  A local improvement
can nevertheless damage something already valued or introduce a different
misfit.  This module therefore gives the strong, compositional notion an
engineering proof may safely claim: a repair preserves a declared observation
and makes the represented misfit set a strict subset.

Repair evidence remains proof-relevant.  A path retains the individual
changes instead of replacing a history by its endpoints.  The destructive
canary proves that strict misfit reduction alone does not establish
structure-preserving repair.

This is an Alexander-inspired formal interface, not a claim that every design
process is monotone or that one fixed misfit vocabulary is complete.

Reference:

- C. Alexander, *Notes on the Synthesis of Form* (1964), especially goodness
  of fit, potential misfit variables, interacting requirements, and gradual
  adaptation.
- C. Alexander, *Systems Generating Systems* (1967), for the distinction
  between a generated object and a system that generates fitting form.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.StructurePreservingRepair

universe uState uValue uMisfit uChange

/-- A represented repair problem.  `valuedObservation` names the structure
that repairs must conserve; `HasMisfit` names the currently recognized
failures; `Change` retains concrete histories between states. -/
structure Problem (State : Type uState) (Value : Type uValue)
    (Misfit : Type uMisfit) where
  valuedObservation : Observer State Value
  HasMisfit : State → Misfit → Prop
  Change : State → State → Type uChange

namespace Problem

variable {State : Type uState} {Value : Type uValue}
  {Misfit : Type uMisfit}

/-- The represented misfits present in one state. -/
def misfits (problem : Problem.{uState, uValue, uMisfit, uChange}
    State Value Misfit) (state : State) : Set Misfit :=
  {misfit | problem.HasMisfit state misfit}

/-- Perfect represented fit is absence of every currently named misfit. -/
def Fits (problem : Problem.{uState, uValue, uMisfit, uChange}
    State Value Misfit) (state : State) : Prop :=
  problem.misfits state = ∅

end Problem

/-- One witnessed, monotone, structure-preserving repair.  Strict subset is
stronger than a decreasing scalar count: it forbids introducing a new named
misfit while removing another. -/
structure Repair
    {State : Type uState} {Value : Type uValue} {Misfit : Type uMisfit}
    (problem : Problem.{uState, uValue, uMisfit, uChange}
      State Value Misfit)
    (source target : State) : Type (max uValue uMisfit uChange) where
  evidence : problem.Change source target
  preservesValue :
    problem.valuedObservation.observe target =
      problem.valuedObservation.observe source
  strictlyReducesMisfit : problem.misfits target ⊂ problem.misfits source

namespace Repair

variable {State : Type uState} {Value : Type uValue}
  {Misfit : Type uMisfit}
  {problem : Problem.{uState, uValue, uMisfit, uChange}
    State Value Misfit}

/-- A strict repair cannot leave the full system state unchanged. -/
theorem source_ne_target {source target : State}
    (repair : Repair problem source target) : source ≠ target := by
  intro equal
  subst target
  exact ssubset_irrefl (problem.misfits source)
    repair.strictlyReducesMisfit

end Repair

/-! ## Histories of local repair -/

/-- A repair path retains every witnessed local repair. -/
inductive Path
    {State : Type uState} {Value : Type uValue} {Misfit : Type uMisfit}
    (problem : Problem.{uState, uValue, uMisfit, uChange}
      State Value Misfit) : Nat → State → State →
      Type (max uState uValue uMisfit uChange) where
  | refl (state : State) : Path problem 0 state state
  | step {steps : Nat} {source middle target : State} :
      Repair problem source middle →
      Path problem steps middle target →
      Path problem (steps + 1) source target

namespace Path

variable {State : Type uState} {Value : Type uValue}
  {Misfit : Type uMisfit}
  {problem : Problem.{uState, uValue, uMisfit, uChange}
    State Value Misfit}

/-- Every repair history preserves the selected valued observation. -/
theorem preservesValue {steps : Nat} {source target : State}
    (path : Path problem steps source target) :
    problem.valuedObservation.observe target =
      problem.valuedObservation.observe source := by
  induction path with
  | refl => rfl
  | step repair tail inductionHypothesis =>
      exact inductionHypothesis.trans repair.preservesValue

/-- A repair history never introduces a represented misfit absent at its
source. -/
theorem misfits_subset {steps : Nat} {source target : State}
    (path : Path problem steps source target) :
    problem.misfits target ⊆ problem.misfits source := by
  induction path with
  | refl => exact Set.Subset.rfl
  | step repair tail inductionHypothesis =>
      exact inductionHypothesis.trans repair.strictlyReducesMisfit.subset

/-- Every nonempty repair history strictly improves represented fit. -/
theorem strictlyReducesMisfit {steps : Nat} {source target : State}
    (path : Path problem (steps + 1) source target) :
    problem.misfits target ⊂ problem.misfits source := by
  cases path with
  | step repair tail =>
      have repairImproves := repair.strictlyReducesMisfit
      rw [Set.ssubset_iff_subset_ne] at repairImproves ⊢
      refine ⟨tail.misfits_subset.trans repairImproves.1, ?_⟩
      intro targetEqualsSource
      apply repairImproves.2
      apply Set.Subset.antisymm repairImproves.1
      intro misfit sourceHasMisfit
      apply tail.misfits_subset
      rw [targetEqualsSource]
      exact sourceHasMisfit

end Path

/-! ## Positive repair and destructive-improvement canaries -/

namespace Canary

abbrev State := Bool × Bool

inductive Change : State → State → Type where
  | repairSecond (value : Bool) : Change (value, false) (value, true)
  | overwrite : Change (false, false) (true, true)

/-- The first coordinate is declared valuable; the sole named misfit is a
false second coordinate. -/
def problem : Problem State Bool Unit where
  valuedObservation := { observe := Prod.fst }
  HasMisfit := fun state _ => state.2 = false
  Change := Change

/-- A positive repair fixes the represented misfit while retaining the
declared first-coordinate value. -/
def repairFalse : Repair problem (false, false) (false, true) where
  evidence := .repairSecond false
  preservesValue := rfl
  strictlyReducesMisfit := by
    rw [Set.ssubset_iff_subset_ne]
    constructor
    · intro misfit targetMisfit
      simp [Problem.misfits, problem] at targetMisfit
    · intro equal
      have sourceMisfit : () ∈ problem.misfits (false, false) := by
        simp [Problem.misfits, problem]
      have targetMisfit : () ∈ problem.misfits (false, true) := by
        rw [equal]
        exact sourceMisfit
      simp [Problem.misfits, problem] at targetMisfit

/-- The positive repair reaches represented fit. -/
theorem repairFalse_fits : problem.Fits (false, true) := by
  ext misfit
  simp [Problem.misfits, problem]

/-- The destructive change removes the named misfit but changes the declared
valuable observation. -/
theorem destructive_strictlyReducesMisfit :
    problem.misfits (true, true) ⊂ problem.misfits (false, false) := by
  rw [Set.ssubset_iff_subset_ne]
  constructor
  · intro misfit targetMisfit
    simp [Problem.misfits, problem] at targetMisfit
  · intro equal
    have sourceMisfit : () ∈ problem.misfits (false, false) := by
      simp [Problem.misfits, problem]
    have targetMisfit : () ∈ problem.misfits (true, true) := by
      rw [equal]
      exact sourceMisfit
    simp [Problem.misfits, problem] at targetMisfit

/-- Strict misfit reduction and concrete change evidence alone do not imply
structure-preserving repair. -/
theorem misfit_reduction_alone_is_insufficient :
    Nonempty (problem.Change (false, false) (true, true)) ∧
      problem.misfits (true, true) ⊂ problem.misfits (false, false) ∧
      ¬ Nonempty (Repair problem (false, false) (true, true)) := by
  refine ⟨⟨.overwrite⟩, destructive_strictlyReducesMisfit, ?_⟩
  rintro ⟨repair⟩
  have preserved := repair.preservesValue
  simp [problem] at preserved

end Canary

end Mettapedia.Cybernetics.StructurePreservingRepair

#print axioms Mettapedia.Cybernetics.StructurePreservingRepair.Repair.source_ne_target
#print axioms Mettapedia.Cybernetics.StructurePreservingRepair.Path.preservesValue
#print axioms Mettapedia.Cybernetics.StructurePreservingRepair.Path.strictlyReducesMisfit
#print axioms Mettapedia.Cybernetics.StructurePreservingRepair.Canary.repairFalse_fits
#print axioms Mettapedia.Cybernetics.StructurePreservingRepair.Canary.misfit_reduction_alone_is_insufficient
