import Mettapedia.GSLT.Distinction.MaterializationObserver
import Mettapedia.GSLT.Distinction.ProductiveBlocksControls

/-!
# Crisp observers of a reading

Three observers of the distinction layer read a status of each state as crisp
atoms: the status of a machine after one transition
(`ProductiveBlocks.Machine.statusSystem`), the results and faults of the outcome
system of `ObservedMaterialization.Controls`, and the return flag read by
`BlockTransportControls.ending_control`.  Each is the same construction: keep the
labelled steps and take the values of a reading as atoms.

* **The builder** (`HennessyMilner.System.withReading`).  The labelled steps of a
  system, with the values of a reading that respects the equations as atoms; a
  term observes exactly the value it reads.
* **Its bisimulations** (`withReading_isBisimulation_iff`,
  `withReading_bisimilar_read_eq`).  A relation is a bisimulation of the crisp
  observer exactly when it matches the labelled steps both ways and relates terms
  that read alike; bisimilar terms read alike.
* **The three observers** (`ProductiveBlocks.Machine.statusSystem_eq_withReading`,
  `ObservedMaterialization.Controls.system_sat_iff`,
  `BlockTransportControls.flagReading_value_eq`).  The status system of a machine
  is the builder applied to its block system, by definition.  The outcome system
  observes the same formulas as the builder applied to it with its outcome
  reading (its atoms are stated in the other orientation).  The return reading is
  the indicator of the atom `true` of the builder applied to the return flag.
* **Controls** (`wedge_reading_separates`, `wedge_spinning_wedged_bisimilar`).
  Blocks relate a finished state and a silent loop; the crisp observer of the
  one-step status separates them through the reading alone.  The same observer
  relates the silent loop to a stuck state: one-step status does not separate
  divergence from deadlock.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.HennessyMilner.System

universe uAtom uLabel uValue

variable {S : GSLT} (M : System.{uAtom, uLabel} S)

/-- **The crisp observer of a reading**: the labelled steps of `M`, with the
values of `read` as atoms; a term observes exactly the value it reads. -/
def withReading {Value : Type uValue} (read : S.Term → Value)
    (read_resp : ∀ {left right : S.Term}, S.Equiv left right → read left = read right) :
    System.{uValue, uLabel} S where
  Atom := Value
  observes value term := read term = value
  observes_resp _ _ _ equivalent :=
    ⟨fun holds => (read_resp equivalent).symm.trans holds,
      fun holds => (read_resp equivalent).trans holds⟩
  Label := M.Label
  act := M.act
  act_resp_left := M.act_resp_left
  act_resp_right := M.act_resp_right

variable {M}
variable {Value : Type uValue} {read : S.Term → Value}
  {read_resp : ∀ {left right : S.Term}, S.Equiv left right → read left = read right}

/-- **A bisimulation of the crisp observer** matches the labelled steps both ways
and relates terms that read alike, and conversely. -/
theorem withReading_isBisimulation_iff (relation : S.Term → S.Term → Prop) :
    (M.withReading read read_resp).IsBisimulation relation ↔
      ((∀ ⦃left right⦄, relation left right → ∀ (label : M.Label) ⦃left'⦄,
          M.act label left left' → ∃ right', M.act label right right' ∧ relation left' right') ∧
        (∀ ⦃left right⦄, relation left right → ∀ (label : M.Label) ⦃right'⦄,
          M.act label right right' → ∃ left', M.act label left left' ∧ relation left' right')) ∧
        ∀ ⦃left right⦄, relation left right → read left = read right := by
  constructor
  · rintro ⟨forth, back, atoms⟩
    exact ⟨⟨forth, back⟩, fun _ right related => (atoms related (read right)).mpr rfl⟩
  · rintro ⟨⟨forth, back⟩, agree⟩
    exact ⟨forth, back, fun _ _ related _ =>
      ⟨fun holds => (agree related).symm.trans holds, fun holds => (agree related).trans holds⟩⟩

/-- **Bisimilar terms read alike.** -/
theorem withReading_bisimilar_read_eq {left right : S.Term}
    (bisimilar : (M.withReading read read_resp).Bisimilar left right) : read left = read right := by
  obtain ⟨relation, bisimulation, related⟩ := bisimilar
  exact ((withReading_isBisimulation_iff relation).mp bisimulation).2 related

end Mettapedia.GSLT.HennessyMilner.System

/-! ## The status of a machine -/

namespace Mettapedia.GSLT.Distinction.ProductiveBlocks.Machine

open Mettapedia.GSLT.HennessyMilner

variable {State Event Verdict Request : Type} (machine : Machine State Event Verdict Request)

/-- The one-step status respects the machine's equations, which are equality. -/
theorem status_resp {left right : State} (equal : machine.gslt.Equiv left right) :
    (machine.observe 1 left).status = (machine.observe 1 right).status :=
  congrArg (fun state => (machine.observe 1 state).status) (show left = right from equal)

/-- **The status system is the crisp observer of the one-step status** on the
block system. -/
theorem statusSystem_eq_withReading :
    machine.statusSystem = machine.reading.blockSystem.withReading
      (fun state => (machine.observe 1 state).status) machine.status_resp :=
  rfl

end Mettapedia.GSLT.Distinction.ProductiveBlocks.Machine

/-! ## The outcome system of the material readout -/

namespace Mettapedia.GSLT.ObservedMaterialization.Controls

open Mettapedia.GSLT.HennessyMilner
open Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u

theorem outcome_resp {left right : State.{u}} (equal : theory.{u}.Equiv left right) :
    outcome left = outcome right :=
  congrArg outcome (show left = right from equal)

/-- The outcome system with its atoms read in the builder's orientation. -/
abbrev outcomeObserver : System.{u, u} theory.{u} :=
  system.{u}.withReading outcome outcome_resp

/-- The outcome system and the builder observe the same atoms, in the two
orientations of the equation. -/
theorem system_observes_iff (atom : OutcomeLabels.Outcome.{u}) (state : State.{u}) :
    system.{u}.observes atom state ↔ outcomeObserver.{u}.observes atom state :=
  ⟨Eq.symm, Eq.symm⟩

/-- **The outcome system satisfies the same formulas as the crisp observer of its
outcome reading.** -/
theorem system_sat_iff :
    ∀ (formula : Formula OutcomeLabels.Outcome.{u} PUnit.{u + 1}) (state : State.{u}),
      system.{u}.sat formula state ↔ outcomeObserver.{u}.sat formula state
  | .top, _ => Iff.rfl
  | .atom atom, state => system_observes_iff atom state
  | .conj left right, state => and_congr (system_sat_iff left state) (system_sat_iff right state)
  | .neg inner, state => not_congr (system_sat_iff inner state)
  | .dia _ inner, _ =>
      ⟨fun ⟨target, step, holds⟩ => ⟨target, step, (system_sat_iff inner target).mp holds⟩,
        fun ⟨target, step, holds⟩ => ⟨target, step, (system_sat_iff inner target).mpr holds⟩⟩

/-- **The two observers have the same bisimulations.** -/
theorem system_isBisimulation_iff (relation : State.{u} → State.{u} → Prop) :
    system.{u}.IsBisimulation relation ↔ outcomeObserver.{u}.IsBisimulation relation := by
  constructor
  · rintro ⟨forth, back, atoms⟩
    refine ⟨forth, back, fun left right related atom => ?_⟩
    exact (system_observes_iff atom left).symm.trans
      ((atoms related atom).trans (system_observes_iff atom right))
  · rintro ⟨forth, back, atoms⟩
    refine ⟨forth, back, fun left right related atom => ?_⟩
    exact (system_observes_iff atom left).trans
      ((atoms related atom).trans (system_observes_iff atom right).symm)

end Mettapedia.GSLT.ObservedMaterialization.Controls

/-! ## The return reading of `ending_control` -/

namespace Mettapedia.GSLT.Distinction.BlockTransportControls

open Mettapedia.GSLT.HennessyMilner

theorem finished_resp {left right : Ending} (equal : ending.Equiv left right) :
    Ending.finished left = Ending.finished right :=
  congrArg Ending.finished (show left = right from equal)

/-- **The return reading is the indicator of the atom `true`** of the crisp
observer of the return flag on the block system. -/
theorem flagReading_value_eq (term : Ending) :
    (flagReading Ending endingStep Ending.finished).value () term =
      (GradedObservations.ofSystem
        (endingReading.blockSystem.withReading Ending.finished finished_resp)).value true term := by
  cases term <;> simp [GradedObservations.ofSystem, System.withReading, Ending.finished]

end Mettapedia.GSLT.Distinction.BlockTransportControls

/-! ## Controls -/

namespace Mettapedia.GSLT.Distinction.StatusObservers.Controls

open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.GSLT.Distinction.ProductiveBlocks.Controls

/-- **Negative for the block system, positive for the reading**: blocks relate a
finished state and a silent loop, and the crisp observer of the one-step status
separates them through the reading alone. -/
theorem wedge_reading_separates :
    wedgeMachine.reading.blockSystem.Bisimilar .done .spinning ∧
      ¬ wedgeMachine.statusSystem.Bisimilar .done .spinning := by
  refine ⟨blocks_cannot_separate .done .spinning, fun bisimilar => ?_⟩
  rw [Machine.statusSystem_eq_withReading] at bisimilar
  have same := System.withReading_bisimilar_read_eq bisimilar
  simp [Machine.observe, Machine.run, wedgeMachine, Outcome.status] at same

/-- **One-step status does not separate divergence from deadlock**: the silent
loop and the stuck state read alike and have no blocks, so the crisp observer
relates them. -/
theorem wedge_spinning_wedged_bisimilar :
    wedgeMachine.statusSystem.Bisimilar .spinning .wedged := by
  rw [Machine.statusSystem_eq_withReading]
  refine ⟨fun left right => (wedgeMachine.observe 1 left).status = (wedgeMachine.observe 1 right).status,
    (System.withReading_isBisimulation_iff _).mpr ⟨⟨?_, ?_⟩, fun _ _ same => same⟩, rfl⟩
  · intro _ _ _ _ _ block
    exact absurd block (no_blocks _ _ _)
  · intro _ _ _ _ _ block
    exact absurd block (no_blocks _ _ _)

end Mettapedia.GSLT.Distinction.StatusObservers.Controls
