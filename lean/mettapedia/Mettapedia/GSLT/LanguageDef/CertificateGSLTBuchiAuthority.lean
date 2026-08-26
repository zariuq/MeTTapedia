import Mathlib.Data.Nat.Find
import Mettapedia.GSLT.LanguageDef.CertificateGSLTUltrainfinite

/-!
# Exact scope of the finite Buechi progress authority

A natural-number progress measure is sound for recurrence from a selected
root.  Its exact semantic scope is slightly stronger: every state declared
active by the controller must be recurrent, including active states that are
not reachable from the selected root.

This module proves both directions.  It also gives a finite negative fixture
in which the root execution is recurrent but an unreachable active component
is not.  Consequently root-only recurrence is not, in general, complete for
the existing progress-certificate language.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

universe uState uAction

/-- Uniform Buechi recurrence over the controller's whole declared active
region, together with local transition legality from the selected root. -/
def MemorylessController.UniformBuchiWinning
    {State : Type uState} {Action : Type uAction}
    (system : LabeledSystem State Action)
    (controller : MemorylessController State Action) (root : State) : Prop :=
  controller.LocallyValid system root /\
    forall state, controller.active state = true ->
      controller.BuchiWinning system state

/-- A valid progress measure proves recurrence from every active state, not
only from the root named in the certificate claim. -/
theorem ProgressMeasure.uniformBuchi_sound
    {State : Type uState} {Action : Type uAction}
    {system : LabeledSystem State Action}
    {controller : MemorylessController State Action}
    {measure : ProgressMeasure State} {root : State}
    (valid : measure.Valid system controller root) :
    controller.UniformBuchiWinning system root := by
  constructor
  · exact valid.1
  · intro state active
    apply ProgressMeasure.buchi_sound
    exact ⟨⟨active, valid.1.2⟩, valid.2⟩

private theorem eventuallyAccepting_of_buchi
    {State : Type uState} {Action : Type uAction}
    {system : LabeledSystem State Action}
    {controller : MemorylessController State Action} {root : State}
    (winning : controller.BuchiWinning system root) :
    exists visit,
      system.accepting (controller.next^[visit] root) = true := by
  obtain ⟨visit, _, accepted⟩ :=
    winning (controller.canonicalExecution root) 0
  exact ⟨visit, accepted⟩

/-- The first distance at which the canonical controller execution reaches
an accepting state.  Inactive states receive rank zero because no progress
obligation is imposed on them. -/
noncomputable def MemorylessController.firstAcceptingRank
    {State : Type uState} {Action : Type uAction}
    (system : LabeledSystem State Action)
    (controller : MemorylessController State Action)
    (uniform : forall state, controller.active state = true ->
      controller.BuchiWinning system state) : State -> Nat :=
  fun state =>
    if active : controller.active state = true then
      Nat.find (eventuallyAccepting_of_buchi (uniform state active))
    else
      0

private theorem firstAcceptingRank_eq_zero_of_accepting
    {State : Type uState} {Action : Type uAction}
    {system : LabeledSystem State Action}
    {controller : MemorylessController State Action}
    {uniform : forall state, controller.active state = true ->
      controller.BuchiWinning system state}
    {state : State} (active : controller.active state = true)
    (accepted : system.accepting state = true) :
    controller.firstAcceptingRank system uniform state = 0 := by
  rw [MemorylessController.firstAcceptingRank, dif_pos active]
  apply Nat.eq_zero_of_le_zero
  apply Nat.find_min'
  simpa using accepted

private theorem firstAcceptingRank_decreases
    {State : Type uState} {Action : Type uAction}
    {system : LabeledSystem State Action}
    {controller : MemorylessController State Action}
    {uniform : forall state, controller.active state = true ->
      controller.BuchiWinning system state}
    {state : State} (active : controller.active state = true)
    (nextActive : controller.active (controller.next state) = true)
    (notAccepted : system.accepting state = false) :
    controller.firstAcceptingRank system uniform (controller.next state) <
      controller.firstAcceptingRank system uniform state := by
  simp only [MemorylessController.firstAcceptingRank, dif_pos active,
    dif_pos nextActive]
  let sourceWitness := eventuallyAccepting_of_buchi (uniform state active)
  let nextWitness :=
    eventuallyAccepting_of_buchi (uniform (controller.next state) nextActive)
  have sourcePositive : 0 < Nat.find sourceWitness := by
    apply Nat.pos_of_ne_zero
    intro sourceZero
    have sourceAccepted := Nat.find_spec sourceWitness
    rw [sourceZero] at sourceAccepted
    simp only [Function.iterate_zero_apply] at sourceAccepted
    simp [notAccepted] at sourceAccepted
  obtain ⟨distance, sourceDistance⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt sourcePositive)
  have sourceAccepted := Nat.find_spec sourceWitness
  rw [sourceDistance, Function.iterate_succ_apply] at sourceAccepted
  have nextBound : Nat.find nextWitness <= distance :=
    Nat.find_min' nextWitness sourceAccepted
  omega

/-- Uniform recurrence constructs a valid natural-number progress measure.
This is the nontrivial completeness direction for the finite evidence
language; it is not a restatement of certificate existence. -/
theorem ProgressMeasure.exists_valid_of_uniformBuchi
    {State : Type uState} {Action : Type uAction}
    {system : LabeledSystem State Action}
    {controller : MemorylessController State Action} {root : State}
    (uniform : controller.UniformBuchiWinning system root) :
    exists measure : ProgressMeasure State,
      measure.Valid system controller root := by
  let measure : ProgressMeasure State :=
    { rank := controller.firstAcceptingRank system uniform.2 }
  refine ⟨measure, uniform.1, ?_⟩
  intro state active
  split
  next accepted =>
    change controller.firstAcceptingRank system uniform.2 state = 0
    exact firstAcceptingRank_eq_zero_of_accepting
      (uniform := uniform.2) active accepted
  next notAccepted =>
    have selected := uniform.1.2 state active
    have currentFalse : system.accepting state = false := by
      cases value : system.accepting state <;> simp_all
    by_cases nextAccepted : system.accepting (controller.next state) = true
    · exact Or.inl nextAccepted
    · right
      change controller.firstAcceptingRank system uniform.2
          (controller.next state) <
        controller.firstAcceptingRank system uniform.2 state
      exact firstAcceptingRank_decreases
        (uniform := uniform.2) active selected.2 currentFalse

/-- The natural progress-measure language is exact for uniform recurrence on
the controller's declared active region. -/
theorem ProgressMeasure.exists_valid_iff_uniformBuchi
    {State : Type uState} {Action : Type uAction}
    {system : LabeledSystem State Action}
    {controller : MemorylessController State Action} {root : State} :
    (exists measure : ProgressMeasure State,
      measure.Valid system controller root) <->
      controller.UniformBuchiWinning system root := by
  constructor
  · rintro ⟨measure, valid⟩
    exact measure.uniformBuchi_sound valid
  · exact ProgressMeasure.exists_valid_of_uniformBuchi

/-! ## Root-only recurrence is strictly weaker -/

private def splitSystem : LabeledSystem Bool Unit where
  step := fun source _ target => decide (target = source)
  accepting := fun state => state

private def splitController : MemorylessController Bool Unit where
  active := fun _ => true
  action := fun _ => ()
  next := id

theorem splitController_locallyValid :
    splitController.LocallyValid splitSystem true := by
  constructor
  · rfl
  · intro state _
    simp [splitController, splitSystem]

theorem splitController_root_buchiWinning :
    splitController.BuchiWinning splitSystem true := by
  intro execution lowerBound
  refine ⟨lowerBound, le_rfl, ?_⟩
  have constant : forall n, execution.state n = true := by
    intro n
    induction n with
    | zero => exact execution.starts
    | succ n inductionHypothesis =>
        rw [execution.follows n]
        simpa [splitController] using inductionHypothesis
  simp [splitSystem, constant lowerBound]

/-- The unreachable active `false` state is a nonaccepting self-loop, so no
rank can satisfy the global descent condition. -/
theorem splitController_no_valid_progress :
    ¬ (exists measure : ProgressMeasure Bool,
      measure.Valid splitSystem splitController true) := by
  rintro ⟨measure, valid⟩
  have impossible := valid.2 false (by rfl)
  simp [splitSystem, splitController] at impossible

/-- Root-local legality and root recurrence do not imply the existence of a
progress certificate when the declared active region contains unreachable
states. -/
theorem rootBuchi_does_not_imply_progress :
    splitController.LocallyValid splitSystem true /\
      splitController.BuchiWinning splitSystem true /\
      ¬ (exists measure : ProgressMeasure Bool,
        measure.Valid splitSystem splitController true) :=
  ⟨splitController_locallyValid, splitController_root_buchiWinning,
    splitController_no_valid_progress⟩

end Mettapedia.GSLT.LanguageDef.CertificateGSLT
