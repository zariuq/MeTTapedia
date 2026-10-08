import Mettapedia.OSLF.Syntax.DeterministicGSOSCounterexample

/-!
# Infinitely many finite rules versus image-finite rules

An enabled-input probe returns one fixed stopped process when any input
action is available. Every successful readout has a singleton observation
witness, so ordinary finite-premise rules present it. At the all-disabled
guard no uniform finite observation bound decides absence; consequently
no image-finite rule presentation exists. Actions remain countably infinite.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS.EnabledProbe

open CategoryTheory Mettapedia.TypeTheory
open AllDisabled

noncomputable def rules : GuardedSchemas actions := by
  classical
  exact fun _ operator guard action => match operator with
    | .stopped => none
    | .probe => if action = 0 ∧ ∃ address, guard address = true then some (stopped _) else none

theorem rename_stopped {X Y : signature.Families} (mapping : X ⟶ Y) :
    signature.rename mapping (stopped X) = stopped Y := by
  rw [stopped, stopped]
  change IndexedPolynomial.Free.map signature.polynomial _ PUnit.unit ()
    (IndexedPolynomial.Free.node signature.polynomial Operator.stopped _) = _
  rw [IndexedPolynomial.Free.map_node]
  apply congrArg (IndexedPolynomial.Free.node signature.polynomial Operator.stopped)
  funext position
  exact position.elim

theorem readout_enabled (guard : Guard actions (sort := ()) Operator.probe) (action : Nat)
    (enabled : action = 0 ∧ ∃ address, guard address = true) :
    universalReadout actions rules Operator.probe guard action =
      some (stopped (universalVariables actions (sort := ()) Operator.probe)) := by
  simp only [universalReadout, rules, enabled]
  exact congrArg some (rename_stopped _)

theorem readout_disabled (guard : Guard actions (sort := ()) Operator.probe) (action : Nat)
    (disabled : ¬ (action = 0 ∧ ∃ address, guard address = true)) :
    universalReadout actions rules Operator.probe guard action = none := by
  classical
  unfold universalReadout
  change (if action = 0 ∧ ∃ address, guard address = true then some (stopped _) else none).map _ = none
  rw [if_neg disabled]
  rfl

theorem finite_successes : FiniteSuccessfulObservation actions rules := by
  classical
  intro sort operator action guard target success
  cases sort
  cases operator with
  | stopped => simp [universalReadout, rules] at success
  | probe =>
      by_cases enabled : action = 0 ∧ ∃ address, guard address = true
      · obtain ⟨zero, address, present⟩ := enabled
        have targetRead := (readout_enabled guard action ⟨zero, address, present⟩).symm.trans success
        have targetEq := Option.some.inj targetRead
        refine ⟨{address}, ?_⟩
        intro other agrees
        have preserved : other address = true :=
          (agrees address (Finset.mem_singleton_self address)).trans present
        exact (readout_enabled other action ⟨zero, address, preserved⟩).trans (congrArg some targetEq)
      · have impossible := (readout_disabled guard action enabled).symm.trans success
        cases impossible

theorem finitePremise_presentation :
    ∃ presentation : FinitePresentation actions, Denotes actions presentation rules :=
  (finitePremise_iff_finiteSuccessfulObservation actions rules).mpr finite_successes

theorem no_uniform_bound : ¬ UniformFiniteObservation actions rules := by
  classical
  intro uniform
  obtain ⟨tested, determines⟩ := uniform () Operator.probe 0
  let fresh := tested.sup (fun address => address.2) + 1
  have missed : (⟨(), fresh⟩ : Address actions (sort := ()) Operator.probe) ∉ tested := by
    intro member
    have bounded : fresh ≤ tested.sup (fun address => address.2) :=
      Finset.le_sup (f := fun address : Address actions (sort := ()) Operator.probe => address.2) member
    exact (Nat.not_succ_le_self _) bounded
  let enabled : Guard actions (sort := ()) Operator.probe :=
    fun address => if address.2 = fresh then true else false
  have agrees : ∀ address ∈ tested, enabled address = AllDisabled.disabled address := by
    intro address member
    have different : address.2 ≠ fresh := by
      intro equal
      have same : address = ⟨(), fresh⟩ := Sigma.ext (Subsingleton.elim _ _) (heq_of_eq equal)
      exact missed (same ▸ member)
    simp [enabled, AllDisabled.disabled, different]
  have stoppedRead := readout_enabled enabled 0
    ⟨rfl, ⟨(), fresh⟩, by simp [enabled]⟩
  have emptyRead := readout_disabled AllDisabled.disabled 0 (by simp [AllDisabled.disabled])
  have impossible := determines AllDisabled.disabled enabled agrees
  rw [stoppedRead, emptyRead] at impossible
  cases impossible

theorem no_imageFinite_presentation :
    ¬ ∃ presentation : FinitePresentation actions,
      ImageFinite actions presentation ∧ Denotes actions presentation rules := by
  rw [imageFinite_iff_uniformFiniteObservation]
  exact no_uniform_bound

/-- The two finite-format qualifications are mathematically different. -/
theorem finitePremise_does_not_imply_imageFinite :
    FiniteSuccessfulObservation actions rules ∧ ¬ UniformFiniteObservation actions rules :=
  ⟨finite_successes, no_uniform_bound⟩

end Mettapedia.OSLF.DeterministicGSOS.EnabledProbe
