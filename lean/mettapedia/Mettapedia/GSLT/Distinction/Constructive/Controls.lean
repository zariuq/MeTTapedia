import Mettapedia.GSLT.Distinction.Constructive.ClassicalBridge
import Mettapedia.GSLT.Logic.ConstructiveModalStrength

/-!
# Controls for the constructive depth-indexed layer

All systems here are presented over the integer scale (`Scale.integers`), whose
order and group laws use no choice principle; every theorem below except the
two marked **classical** avoids `Classical.choice`.  Finite facts are checked
by kernel `decide`; `le_rfl` at `ℤ` is avoided, since its synthesized order
instance depends on `Classical.choice`.

* **The stream probe** (`probe`, from `ConstructiveModalStrength`).  Under at
  most one true bit its roots have depth bound `0` at every depth
  (`probe_depthBound_eq_zero`), while their graded bisimilarity is exactly the
  LLPO disjunction (`probe_gradedBisimilar_iff`).  Hence requiring finite-depth
  reflection of every presented system constructively implies LLPO
  (`finiteDepthReflection_implies_llpo`): a lower bound on that principle, not
  an equivalence.  The classical bridge supplies the reflection
  (`probe_llpo_classical`, **classical**), which is where the classical step
  enters; so does the classical Hennessy–Milner theorem fed to
  `ConstructiveModalStrength.image_finite_reflection_implies_llpo` (`llpo_of_classical_adequacy`,
  **classical**).  At the zero stream an explicit bisimulation is the witness
  (`probe_zero_stream_witness`).
* **A finite system with a certificate** (`cells`): a self-loop, a two-cycle, a
  half reading and a dead end, read on a scale with unit `2`.  Its bounds
  stabilize at depth `1` (`cells_stabilizes`, by kernel evaluation) and not at
  depth `0` (`cells_not_stable_at_zero`), so they converge
  (`cells_converge`); reflection holds constructively because of the
  certificate (`cells_rest_ping_bisimilar`), and the dead end is separated at
  depth `1` by an explicit diamond (`cells_rest_dead_separated`).
* **Exact transport along a collapse** (`collapse`): the two-cycle folds onto
  the self-loop with a supplied section, so every depth bound is preserved
  (`collapse_depthBound`), and the cycle and the loop agree at every depth by
  transport alone (`cells_ping_rest_every_depth`).
* **No section** (`refine`): every requirement of an exact observation map
  holds, the target reads an extra observation, no section exists
  (`refine_no_section`), no pullback of target formulas exists
  (`refine_no_pullback`), and the depth-`0` bound grows from `0` to `1`
  (`refine_distances`).
* **The vocabulary is priced separately** (`counting`): formula values exist
  for a system with a label for every natural number (`counting_val`), but no
  finite vocabulary does (`counting_no_vocabulary`).
* **A convergence modulus at discount one is LPO** (`signal`,
  `modulus_at_discount_one_implies_lpo`): a deterministic one-successor system
  whose depth bounds record whether a sequence has a true entry so far.
* **Errors add and are attained** (`graded`, `rise`): two maps of error `1`
  compose to a map of error `2` whose error is attained by a formula value
  (`composite_error_attained`), so a positive error bound gives no exact
  transport (`composite_not_exact`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.Constructive.Controls

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.Distinction.Constructive

/-- The integer scale with unit one: readings `0` and `1`. -/
def unitScale : Scale ℤ := Scale.integers 1 (by decide)

/-- The integer scale with unit two: readings `0`, `1/2` and `1`. -/
def halfScale : Scale ℤ := Scale.integers 2 (by decide)

theorem unitScale_positive : unitScale.Positive := Scale.integers_positive 1 _

theorem halfScale_positive : halfScale.Positive := Scale.integers_positive 2 _

/-! ## The stream probe -/

section Probe

/-- The reading of a Boolean observation: `1` exactly when the observed bit is
that Boolean. -/
def probeReading (stream : ℕ → Bool) (observation : Bool)
    (state : ConstructiveModalStrength.State) : ℤ :=
  if ConstructiveModalStrength.observedBit stream state = observation then 1 else 0

theorem probeReading_mem (stream : ℕ → Bool) (observation : Bool)
    (state : ConstructiveModalStrength.State) :
    0 ≤ probeReading stream observation state ∧ probeReading stream observation state ≤ 1 := by
  unfold probeReading
  by_cases same : ConstructiveModalStrength.observedBit stream state = observation
  · rw [if_pos same]
    decide
  · rw [if_neg same]
    decide

/-- **The stream probe** as a presented system over the integer scale, with
the authored successor lists of `ConstructiveModalStrength`. -/
def probe (stream : ℕ → Bool) :
    PresentedSystem.{0, 0, 0, 0, 0} ConstructiveModalStrength.theory unitScale where
  dynamics := ConstructiveModalStrength.system.{0} stream
  Obs := Bool
  value := probeReading stream
  value_nonneg observation state := (probeReading_mem stream observation state).1
  value_le_one observation state := (probeReading_mem stream observation state).2
  value_resp observation left right same := by
    have equal : left = right := same
    rw [equal]
  successors _ state := ConstructiveModalStrength.successors state
  successors_act member := member
  successors_cover {_ _ target} step := ⟨target, step, rfl⟩

/-- Both Booleans and the single label, listed. -/
def probeVocabulary (stream : ℕ → Bool) : (probe stream).Vocabulary where
  observations := [false, true]
  observations_complete observation := by
    cases observation
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  labels := [PUnit.unit]
  labels_complete _ := List.mem_singleton_self _

theorem probe_values_zero_trace (stream : ℕ → Bool) (track : ConstructiveModalStrength.Track)
    (position : ℕ)
    (clear : ConstructiveModalStrength.bit stream track position = false) (observation : Bool) :
    (probe stream).value observation (.trace .zero position) =
      (probe stream).value observation (.trace track position) := by
  show probeReading stream observation (.trace .zero position) =
    probeReading stream observation (.trace track position)
  unfold probeReading
  rw [show ConstructiveModalStrength.observedBit stream (.trace track position) = false from clear]
  rfl

/-- The zero stream approximates a clear stream to every depth it is clear. -/
theorem probe_approx_zero_trace (stream : ℕ → Bool) (track : ConstructiveModalStrength.Track) :
    ∀ (depth position : ℕ),
      (∀ offset ≤ depth, ConstructiveModalStrength.bit stream track (position + offset) = false) →
        (probe stream).Approx depth (.trace .zero position) (.trace track position)
  | 0, position, clear => probe_values_zero_trace stream track position (clear 0 (Nat.le_refl 0))
  | depth + 1, position, clear => by
      refine ⟨probe_values_zero_trace stream track position (clear 0 (Nat.zero_le _)), ?_, ?_⟩
      · intro label target step
        change target ∈ [ConstructiveModalStrength.State.trace .zero (position + 1)] at step
        rw [List.mem_singleton.mp step]
        refine ⟨.trace track (position + 1), List.mem_singleton.mpr rfl,
          probe_approx_zero_trace stream track depth (position + 1) fun offset le => ?_⟩
        have later := clear (offset + 1) (Nat.succ_le_succ le)
        rwa [show position + (offset + 1) = position + 1 + offset by omega] at later
      · intro label target step
        change target ∈ [ConstructiveModalStrength.State.trace track (position + 1)] at step
        rw [List.mem_singleton.mp step]
        refine ⟨.trace .zero (position + 1), List.mem_singleton.mpr rfl,
          probe_approx_zero_trace stream track depth (position + 1) fun offset le => ?_⟩
        have later := clear (offset + 1) (Nat.succ_le_succ le)
        rwa [show position + (offset + 1) = position + 1 + offset by omega] at later

/-- The two roots are approximants at every depth, under at most one true bit.
The branch matching the zero stream depends on the depth. -/
theorem probe_approx_roots (stream : ℕ → Bool)
    (unique : ∀ first second, stream first = true → stream second = true → first = second) :
    ∀ depth, (probe stream).Approx depth (.root true) (.root false)
  | 0 => fun _ => rfl
  | depth + 1 => by
      refine ⟨fun _ => rfl, ?_, ?_⟩
      · intro label target step
        change target ∈ [ConstructiveModalStrength.State.trace .even 0,
          ConstructiveModalStrength.State.trace .odd 0,
          ConstructiveModalStrength.State.trace .zero 0] at step
        rcases List.mem_cons.mp step with rfl | step
        · exact ⟨_, List.mem_cons_self, (probe stream).approx_refl depth _⟩
        rcases List.mem_cons.mp step with rfl | step
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, (probe stream).approx_refl depth _⟩
        rw [List.mem_singleton.mp step]
        rcases ConstructiveModalStrength.finite_zero_cover stream unique (depth + 1) with
          even | odd
        · refine ⟨.trace .even 0, List.mem_cons_self,
            probe_approx_zero_trace stream .even depth 0 fun offset le => ?_⟩
          show stream (2 * (0 + offset)) = false
          rw [Nat.zero_add]
          exact even offset (Nat.lt_succ_of_le le)
        · refine ⟨.trace .odd 0, List.mem_cons_of_mem _ List.mem_cons_self,
            probe_approx_zero_trace stream .odd depth 0 fun offset le => ?_⟩
          show stream (2 * (0 + offset) + 1) = false
          rw [Nat.zero_add]
          exact odd offset (Nat.lt_succ_of_le le)
      · intro label target step
        change target ∈ [ConstructiveModalStrength.State.trace .even 0,
          ConstructiveModalStrength.State.trace .odd 0] at step
        refine ⟨target, List.mem_cons.mpr ?_, (probe stream).approx_refl depth target⟩
        rcases List.mem_cons.mp step with same | step
        · exact Or.inl same
        · exact Or.inr (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp step)))

/-- **Agreement at every finite depth**, without any omniscience principle. -/
theorem probe_depthBound_eq_zero (stream : ℕ → Bool)
    (unique : ∀ first second, stream first = true → stream second = true → first = second)
    (depth : ℕ) :
    (probe stream).depthBound (probeVocabulary stream) depth (.root true) (.root false) = 0 :=
  (probe stream).depthBound_eq_zero_of_approx _ (probe_approx_roots stream unique depth)

theorem probe_value_eq_iff (stream : ℕ → Bool) (observation : Bool)
    (left right : ConstructiveModalStrength.State) :
    (probe stream).value observation left = (probe stream).value observation right ↔
      ((ConstructiveModalStrength.system.{0} stream).observes observation left ↔
        (ConstructiveModalStrength.system.{0} stream).observes observation right) := by
  show probeReading stream observation left = probeReading stream observation right ↔
    (observation = ConstructiveModalStrength.observedBit stream left ↔
      observation = ConstructiveModalStrength.observedBit stream right)
  unfold probeReading
  generalize ConstructiveModalStrength.observedBit stream left = first
  generalize ConstructiveModalStrength.observedBit stream right = second
  cases observation <;> cases first <;> cases second <;> decide

/-- Graded bisimulations of the probe are its crisp bisimulations. -/
theorem probe_isGradedBisimulation_iff (stream : ℕ → Bool)
    (relation : ConstructiveModalStrength.State → ConstructiveModalStrength.State → Prop) :
    (probe stream).IsGradedBisimulation relation ↔
      (ConstructiveModalStrength.system.{0} stream).IsBisimulation relation :=
  ⟨fun ⟨forward, backward, values⟩ => ⟨forward, backward, fun _ _ related observation =>
      (probe_value_eq_iff stream observation _ _).mp (values related observation)⟩,
    fun ⟨forward, backward, observes⟩ => ⟨forward, backward, fun _ _ related observation =>
      (probe_value_eq_iff stream observation _ _).mpr (observes related observation)⟩⟩

/-- **The infinite witness is the LLPO disjunction.** -/
theorem probe_gradedBisimilar_iff (stream : ℕ → Bool) :
    (probe stream).GradedBisimilar (.root true) (.root false) ↔
      (∀ position, stream (2 * position) = false) ∨
        (∀ position, stream (2 * position + 1) = false) := by
  refine Iff.trans ?_ (ConstructiveModalStrength.roots_bisimilar_iff.{0} stream)
  exact ⟨fun ⟨relation, bisimulation, related⟩ =>
      ⟨relation, (probe_isGradedBisimulation_iff stream relation).mp bisimulation, related⟩,
    fun ⟨relation, bisimulation, related⟩ =>
      ⟨relation, (probe_isGradedBisimulation_iff stream relation).mpr bisimulation, related⟩⟩

/-- **Finite-depth reflection, required of every presented system over the
integer scale, implies LLPO** for sequences with at most one true entry.  This
is a lower bound on the strength of that reflection principle. -/
theorem finiteDepthReflection_implies_llpo
    (reflection : ∀ (S : GSLT.{0}) (Q : PresentedSystem.{0, 0, 0, 0, 0} S unitScale)
      (W : Q.Vocabulary) (left right : S.Term),
        (∀ depth, Q.depthBound W depth left right = 0) → Q.GradedBisimilar left right)
    (stream : ℕ → Bool)
    (unique : ∀ first second, stream first = true → stream second = true → first = second) :
    (∀ position, stream (2 * position) = false) ∨
      (∀ position, stream (2 * position + 1) = false) :=
  (probe_gradedBisimilar_iff stream).mp
    (reflection _ (probe stream) (probeVocabulary stream) _ _
      (probe_depthBound_eq_zero stream unique))

/-- **Classical.**  The classical quantitative Hennessy–Milner theorem supplies
the reflection for the probe, and with it the LLPO disjunction.  Its axioms
include `Classical.choice`: this is where the classical step enters. -/
theorem probe_llpo_classical (stream : ℕ → Bool)
    (unique : ∀ first second, stream first = true → stream second = true → first = second) :
    (∀ position, stream (2 * position) = false) ∨
      (∀ position, stream (2 * position + 1) = false) :=
  (probe_gradedBisimilar_iff stream).mp
    (((probe stream).gradedBisimilar_iff_forall_depthBound_eq_zero (Realization.integers 1 _)
      (probeVocabulary stream) (show (0 : ℝ) < 1 from one_pos) _ _).mpr
      (probe_depthBound_eq_zero stream unique))

/-- **Classical.**  The LLPO theorem of `ConstructiveModalStrength`, with the
classical Hennessy–Milner adequacy theorem supplying its reflection hypothesis:
the LLPO disjunction follows, and `Classical.choice` appears among the axioms. -/
theorem llpo_of_classical_adequacy (stream : ℕ → Bool)
    (unique : ∀ first second, stream first = true → stream second = true → first = second) :
    (∀ position, stream (2 * position) = false) ∨
      (∀ position, stream (2 * position + 1) = false) :=
  ConstructiveModalStrength.image_finite_reflection_implies_llpo
    (fun _ system finite left right equivalent =>
      (system.logicallyEquivalent_iff_bisimilar finite left right).mp equivalent)
    stream unique

/-- **An explicit witness.**  At the zero stream the coherent matching relation
of `ConstructiveModalStrength` is a graded bisimulation of the roots. -/
theorem probe_zero_stream_witness :
    (probe fun _ => false).GradedBisimilar (.root true) (.root false) :=
  (probe_gradedBisimilar_iff _).mpr (Or.inl fun _ => rfl)

end Probe

/-! ## A finite system with a stabilization certificate -/

/-- Five cells: a self-loop, a two-cycle, a self-loop reading one half, and a
dead end. -/
inductive Cell where
  | rest
  | ping
  | pong
  | half
  | dead
  deriving DecidableEq

/-- The successors of a cell. -/
def Cell.next : Cell → List Cell
  | .rest => [.rest]
  | .ping => [.pong]
  | .pong => [.ping]
  | .half => [.half]
  | .dead => []

/-- The reading of a cell on the scale with unit two. -/
def Cell.reading : Cell → ℤ
  | .half => 1
  | _ => 0

/-- The GSLT of the cells. -/
abbrev cellTheory : GSLT.{0} where
  Term := Cell
  equations := ⟨Eq, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩
  rewrites source target := target ∈ source.next
  rewrites_resp_left := by
    intro _ _ target same step
    exact ⟨target, same ▸ step, rfl⟩
  rewrites_resp_right := by
    intro _ _ _ step same
    exact same ▸ step

/-- One label: the cell step. -/
abbrev cellDynamics : System.{0, 0} cellTheory where
  Atom := Empty
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := Unit
  act _ source target := target ∈ source.next
  act_resp_left := by
    intro _ _ _ target same step
    exact ⟨target, same ▸ step, rfl⟩
  act_resp_right := by
    intro _ _ _ _ step same
    exact same ▸ step

/-- **The cells** as a presented system on the scale with unit two. -/
def cells : PresentedSystem.{0, 0, 0, 0, 0} cellTheory halfScale where
  dynamics := cellDynamics
  Obs := Unit
  value _ cell := cell.reading
  value_nonneg _ cell := by cases cell <;> decide
  value_le_one _ cell := by cases cell <;> decide
  value_resp _ _ _ same := by
    have equal := same
    rw [show _ = _ from equal]
  successors _ cell := cell.next
  successors_act member := member
  successors_cover {_ _ target} step := ⟨target, step, rfl⟩

def cellVocabulary : cells.Vocabulary where
  observations := [()]
  observations_complete _ := List.mem_singleton_self _
  labels := [()]
  labels_complete _ := List.mem_singleton_self _

/-- **The stabilization certificate**, checked by kernel evaluation. -/
theorem cells_stabilizes : cells.Stabilizes cellVocabulary 1 := by
  intro left right
  cases left <;> cases right <;> decide

theorem cells_not_stable_at_zero : ¬ cells.Stabilizes cellVocabulary 0 := by
  intro stable
  have := stable .rest .dead
  revert this
  decide

/-- **The bounds converge**: they are constant from depth one on. -/
theorem cells_converge (extra : ℕ) (left right : Cell) :
    cells.depthBound cellVocabulary (1 + extra) left right =
      cells.depthBound cellVocabulary 1 left right :=
  cells.depthBound_add_of_stabilizes cellVocabulary cells_stabilizes extra left right

/-- **Reflection from the certificate**: the self-loop and the two-cycle are
graded bisimilar. -/
theorem cells_rest_ping_bisimilar : cells.GradedBisimilar .rest .ping :=
  ((cells.gradedBisimilar_iff_of_stabilizes cellVocabulary halfScale_positive cells_stabilizes
    .rest .ping).2).mpr (by decide)

/-- The half reading is separated at depth zero by one half. -/
theorem cells_rest_half : cells.depthBound cellVocabulary 0 .rest .half = 1 := by decide

/-- **The dead end** is separated at depth one by the full unit, attained by
the diamond of truth, and is not bisimilar to the self-loop. -/
theorem cells_rest_dead_separated :
    cells.depthBound cellVocabulary 0 .rest .dead = 0 ∧
      cells.depthBound cellVocabulary 1 .rest .dead = 2 ∧
      cells.val (.dia () .top) .rest - cells.val (.dia () .top) .dead = 2 ∧
      ¬ cells.GradedBisimilar .rest .dead := by
  refine ⟨by decide, by decide, by decide, fun bisimilar => ?_⟩
  have zero := cells.depthBound_eq_zero_of_gradedBisimilar cellVocabulary bisimilar 1
  revert zero
  decide

/-! ## Exact transport along a collapse -/

/-- Fold the two-cycle onto the self-loop. -/
def Cell.collapse : Cell → Cell
  | .ping => .rest
  | .pong => .rest
  | cell => cell

/-- **The collapse** is an exact observation map of the cells into themselves. -/
def collapse : ObservationMap cells cells 0 where
  error_nonneg := by decide
  mapTerm := Cell.collapse
  mapEquiv := fun same => congrArg Cell.collapse same
  atom := id
  label := id
  value_close _ cell := by
    show |cell.collapse.reading - cell.reading| ≤ 0
    cases cell <;> decide
  mapAct _ source target step := by
    change target ∈ source.next at step
    change target.collapse ∈ source.collapse.next
    cases source <;> simp only [Cell.next, List.mem_singleton, List.not_mem_nil] at step <;>
      subst step <;> exact List.mem_singleton_self _
  liftAct _ source target' step := by
    change target' ∈ source.collapse.next at step
    cases source with
    | rest => exact ⟨.rest, List.mem_singleton_self _, (List.mem_singleton.mp step).symm⟩
    | ping => exact ⟨.pong, List.mem_singleton_self _, (List.mem_singleton.mp step).symm⟩
    | pong => exact ⟨.ping, List.mem_singleton_self _, (List.mem_singleton.mp step).symm⟩
    | half => exact ⟨.half, List.mem_singleton_self _, (List.mem_singleton.mp step).symm⟩
    | dead => exact absurd step List.not_mem_nil

instance : DecidableEq cells.Obs := inferInstanceAs (DecidableEq Unit)

instance : DecidableEq cells.dynamics.Label := inferInstanceAs (DecidableEq Unit)

/-- Its section, computed from the vocabulary lists. -/
def collapseSection : collapse.VocabularySection :=
  ObservationMap.VocabularySection.ofEnumeration collapse cellVocabulary
    (fun observation => ⟨observation, rfl⟩) (fun step => ⟨step, rfl⟩)

/-- **Every depth bound is preserved by the collapse.** -/
theorem collapse_depthBound (depth : ℕ) (left right : Cell) :
    cells.depthBound cellVocabulary depth left.collapse right.collapse =
      cells.depthBound cellVocabulary depth left right :=
  ObservationMap.depthBound_map_eq collapseSection cellVocabulary cellVocabulary depth left right

/-- **Agreement at every depth by transport alone.** -/
theorem cells_ping_rest_every_depth (depth : ℕ) :
    cells.depthBound cellVocabulary depth .ping .rest = 0 := by
  rw [← collapse_depthBound]
  exact cells.depthBound_self cellVocabulary depth .rest

/-! ## No section -/

/-- Two terms and no steps. -/
abbrev pairTheory : GSLT.{0} where
  Term := Bool
  equations := ⟨Eq, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩
  rewrites _ _ := False
  rewrites_resp_left := by
    intro _ _ _ _ step
    exact step.elim
  rewrites_resp_right := by
    intro _ _ _ step _
    exact step.elim

abbrev stillDynamics : System.{0, 0} pairTheory where
  Atom := Empty
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := Unit
  act _ _ _ := False
  act_resp_left := by
    intro _ _ _ _ _ step
    exact step.elim
  act_resp_right := by
    intro _ _ _ _ step _
    exact step.elim

/-- One observation, reading `0` on both terms. -/
def coarse : PresentedSystem.{0, 0, 0, 0, 0} pairTheory unitScale where
  dynamics := stillDynamics
  Obs := Unit
  value _ _ := 0
  value_nonneg _ _ := by show (0 : ℤ) ≤ 0; decide
  value_le_one _ _ := by decide
  value_resp _ _ _ _ := rfl
  successors _ _ := []
  successors_act member := absurd member List.not_mem_nil
  successors_cover step := step.elim

/-- The image of that observation, and an extra one reading the term. -/
def fineReading : Option Unit → Bool → ℤ
  | some _, _ => 0
  | none, false => 0
  | none, true => 1

theorem fineReading_mem : ∀ (observation : Option Unit) (term : Bool),
    0 ≤ fineReading observation term ∧ fineReading observation term ≤ 1
  | some _, _ => ⟨by show (0 : ℤ) ≤ 0; decide, by show (0 : ℤ) ≤ 1; decide⟩
  | none, false => ⟨by decide, by decide⟩
  | none, true => ⟨by decide, by decide⟩

def fine : PresentedSystem.{0, 0, 0, 0, 0} pairTheory unitScale where
  dynamics := stillDynamics
  Obs := Option Unit
  value := fineReading
  value_nonneg observation term := (fineReading_mem observation term).1
  value_le_one observation term := (fineReading_mem observation term).2
  value_resp _ _ _ same := by
    have equal := same
    rw [show _ = _ from equal]
  successors _ _ := []
  successors_act member := absurd member List.not_mem_nil
  successors_cover step := step.elim

def coarseVocabulary : coarse.Vocabulary where
  observations := [()]
  observations_complete _ := List.mem_singleton_self _
  labels := [()]
  labels_complete _ := List.mem_singleton_self _

def fineVocabulary : fine.Vocabulary where
  observations := [some (), none]
  observations_complete observation := by
    cases observation with
    | none => exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    | some _ => exact List.mem_cons_self
  labels := [()]
  labels_complete _ := List.mem_singleton_self _

/-- **Every requirement of an exact observation map holds.** -/
def refine : ObservationMap coarse fine 0 where
  error_nonneg := by decide
  mapTerm := id
  mapEquiv := fun same => same
  atom _ := some ()
  label := id
  value_close _ _ := by
    show |(0 : ℤ) - 0| ≤ 0
    decide
  mapAct _ _ _ step := step.elim
  liftAct _ _ _ step := step.elim

/-- **No section of the observation translation exists.** -/
theorem refine_no_section : IsEmpty refine.VocabularySection :=
  ⟨fun section' => by
    have impossible : (some () : Option Unit) = none := section'.atom_atomBack none
    cases impossible⟩

theorem coarse_gradedBisimilar : coarse.GradedBisimilar false true :=
  ⟨fun _ _ => True, ⟨fun _ _ _ _ _ step => step.elim, fun _ _ _ _ _ step => step.elim,
    fun _ _ _ _ => rfl⟩, trivial⟩

/-- **No pullback of target formulas exists**: the extra observation separates
images that every source formula equates. -/
theorem refine_no_pullback :
    ¬ ∃ pull : fine.Formula → coarse.Formula,
      ∀ (formula : fine.Formula) (term : Bool),
        coarse.val (pull formula) term = fine.val formula (refine.mapTerm term) := by
  rintro ⟨pull, agrees⟩
  have same := coarse.val_eq_of_gradedBisimilar coarse_gradedBisimilar (pull (.atom none))
  rw [agrees, agrees] at same
  exact absurd same (by decide)

/-- **The depth-zero bound grows from `0` to `1`.** -/
theorem refine_distances :
    coarse.depthBound coarseVocabulary 0 false true = 0 ∧
      fine.depthBound fineVocabulary 0 (refine.mapTerm false) (refine.mapTerm true) = 1 :=
  ⟨by decide, by decide⟩

/-! ## Formula values need branching only; bounds need a vocabulary -/

/-- No steps, and one label for every natural number. -/
abbrev countingDynamics : System.{0, 0} pairTheory where
  Atom := Empty
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := ℕ
  act _ _ _ := False
  act_resp_left := by
    intro _ _ _ _ _ step
    exact step.elim
  act_resp_right := by
    intro _ _ _ _ step _
    exact step.elim

def counting : PresentedSystem.{0, 0, 0, 0, 0} pairTheory unitScale where
  dynamics := countingDynamics
  Obs := Unit
  value _ _ := 0
  value_nonneg _ _ := by show (0 : ℤ) ≤ 0; decide
  value_le_one _ _ := by decide
  value_resp _ _ _ _ := rfl
  successors _ _ := []
  successors_act member := absurd member List.not_mem_nil
  successors_cover step := step.elim

theorem le_foldr_max : ∀ (list : List ℕ) (element : ℕ), element ∈ list →
    element ≤ list.foldr max 0
  | [], _, member => absurd member List.not_mem_nil
  | head :: rest, element, member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact le_max_left _ _
      · exact (le_foldr_max rest element member).trans (le_max_right _ _)

theorem exists_not_mem_nat (list : List ℕ) : ∃ number, number ∉ list :=
  ⟨list.foldr max 0 + 1, fun member => absurd (le_foldr_max list _ member) (by omega)⟩

/-- **Formula values exist** for every label of the counting system. -/
theorem counting_val (label : ℕ) (term : Bool) :
    counting.val (.dia (show counting.dynamics.Label from label) .top) term = 0 := rfl

/-- **No finite vocabulary exists**, so no depth bound is computed: the
vocabulary is a separate, priced assumption. -/
theorem counting_no_vocabulary : IsEmpty counting.Vocabulary :=
  ⟨fun vocabulary => by
    obtain ⟨number, missing⟩ := exists_not_mem_nat vocabulary.labels
    exact missing (vocabulary.labels_complete number)⟩

/-! ## A convergence modulus at discount one decides LPO -/

/-- A chain reading a sequence, and a quiet loop. -/
inductive Signal where
  | chain (position : ℕ)
  | quiet

def Signal.next : Signal → List Signal
  | .chain position => [.chain (position + 1)]
  | .quiet => [.quiet]

abbrev signalTheory : GSLT.{0} where
  Term := Signal
  equations := ⟨Eq, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩
  rewrites source target := target ∈ source.next
  rewrites_resp_left := by
    intro _ _ target same step
    exact ⟨target, same ▸ step, rfl⟩
  rewrites_resp_right := by
    intro _ _ _ step same
    exact same ▸ step

abbrev signalDynamics : System.{0, 0} signalTheory where
  Atom := Empty
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := Unit
  act _ source target := target ∈ source.next
  act_resp_left := by
    intro _ _ _ target same step
    exact ⟨target, same ▸ step, rfl⟩
  act_resp_right := by
    intro _ _ _ _ step same
    exact same ▸ step

def signalReading (stream : ℕ → Bool) : Signal → ℤ
  | .chain position => if stream position then 1 else 0
  | .quiet => 0

theorem signalReading_mem (stream : ℕ → Bool) (signal : Signal) :
    0 ≤ signalReading stream signal ∧ signalReading stream signal ≤ 1 := by
  cases signal with
  | quiet =>
      show (0 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ 1
      decide
  | chain position =>
      show (0 : ℤ) ≤ (if stream position = true then 1 else 0) ∧
        (if stream position = true then (1 : ℤ) else 0) ≤ 1
      cases stream position <;> decide

/-- **The signal system** on the scale with unit one and discount one. -/
def signal (stream : ℕ → Bool) : PresentedSystem.{0, 0, 0, 0, 0} signalTheory unitScale where
  dynamics := signalDynamics
  Obs := Unit
  value _ := signalReading stream
  value_nonneg _ signal := (signalReading_mem stream signal).1
  value_le_one _ signal := (signalReading_mem stream signal).2
  value_resp _ _ _ same := by
    have equal := same
    rw [show _ = _ from equal]
  successors _ signal := signal.next
  successors_act member := member
  successors_cover {_ _ target} step := ⟨target, step, rfl⟩

def signalVocabulary (stream : ℕ → Bool) : (signal stream).Vocabulary where
  observations := [()]
  observations_complete _ := List.mem_singleton_self _
  labels := [()]
  labels_complete _ := List.mem_singleton_self _

theorem signal_values_iff (stream : ℕ → Bool) (position : ℕ) :
    (∀ observation, (signal stream).value observation (.chain position) =
      (signal stream).value observation .quiet) ↔ stream position = false := by
  constructor
  · intro same
    have reading := same ()
    change (if stream position = true then (1 : ℤ) else 0) = 0 at reading
    revert reading
    cases stream position <;> decide
  · intro clear _
    show (if stream position = true then (1 : ℤ) else 0) = 0
    rw [clear]
    rfl

/-- The chain approximates the quiet loop to depth `n` exactly when the next
`n + 1` entries are false. -/
theorem signal_approx_iff (stream : ℕ → Bool) :
    ∀ (depth position : ℕ), (signal stream).Approx depth (.chain position) .quiet ↔
      ∀ offset ≤ depth, stream (position + offset) = false
  | 0, position => by
      refine (signal_values_iff stream position).trans ⟨fun clear offset le => ?_,
        fun clear => clear 0 (Nat.le_refl 0)⟩
      rw [Nat.le_zero.mp le]
      exact clear
  | depth + 1, position => by
      constructor
      · rintro ⟨values, forward, -⟩ offset le
        rcases offset with _ | offset
        · exact (signal_values_iff stream position).mp values
        · obtain ⟨right', step, approx⟩ :=
            forward () (.chain (position + 1)) (List.mem_singleton_self _)
          change right' ∈ [Signal.quiet] at step
          rw [List.mem_singleton.mp step] at approx
          have later := (signal_approx_iff stream depth (position + 1)).mp approx offset
            (Nat.le_of_succ_le_succ le)
          rwa [show position + 1 + offset = position + (offset + 1) by omega] at later
      · intro clear
        have next : (signal stream).Approx depth (.chain (position + 1)) .quiet :=
          (signal_approx_iff stream depth (position + 1)).mpr fun offset le => by
            have later := clear (offset + 1) (Nat.succ_le_succ le)
            rwa [show position + (offset + 1) = position + 1 + offset by omega] at later
        refine ⟨(signal_values_iff stream position).mpr (clear 0 (Nat.zero_le _)), ?_, ?_⟩
        · intro _ target step
          change target ∈ [Signal.chain (position + 1)] at step
          rw [List.mem_singleton.mp step]
          exact ⟨.quiet, List.mem_singleton_self _, next⟩
        · intro _ target step
          change target ∈ [Signal.quiet] at step
          rw [List.mem_singleton.mp step]
          exact ⟨.chain (position + 1), List.mem_singleton_self _, next⟩

/-- At depth `n` the bound is `0` exactly when the first `n + 1` entries are
false. -/
theorem signal_depthBound_eq_zero_iff (stream : ℕ → Bool) (depth : ℕ) :
    (signal stream).depthBound (signalVocabulary stream) depth (.chain 0) .quiet = 0 ↔
      ∀ position ≤ depth, stream position = false := by
  rw [(signal stream).depthBound_eq_zero_iff_approx _ unitScale_positive,
    signal_approx_iff stream depth 0]
  simp only [Nat.zero_add]

/-- A finite search for a true entry needs no omniscience. -/
theorem bounded_search (stream : ℕ → Bool) :
    ∀ bound, (∀ position ≤ bound, stream position = false) ∨
      ∃ position ≤ bound, stream position = true
  | 0 => by
      cases found : stream 0 with
      | false => exact Or.inl fun position le => (Nat.le_zero.mp le) ▸ found
      | true => exact Or.inr ⟨0, Nat.le_refl 0, found⟩
  | bound + 1 => by
      rcases bounded_search stream bound with clear | ⟨position, le, found⟩
      · cases found : stream (bound + 1) with
        | false =>
            refine Or.inl fun position le => ?_
            rcases Nat.lt_or_eq_of_le le with less | same
            · exact clear position (Nat.le_of_lt_succ less)
            · exact same ▸ found
        | true => exact Or.inr ⟨bound + 1, Nat.le_refl _, found⟩
      · exact Or.inr ⟨position, Nat.le_succ_of_le le, found⟩

/-- **A convergence modulus at discount one implies LPO.**  If the depth bounds
of every signal system become constant, to within less than the unit, after
some stage, then every binary sequence is constantly false or has a true
entry. -/
theorem modulus_at_discount_one_implies_lpo
    (modulus : ∀ stream : ℕ → Bool, ∃ stage, ∀ depth, stage ≤ depth →
      (signal stream).depthBound (signalVocabulary stream) depth (.chain 0) .quiet -
        (signal stream).depthBound (signalVocabulary stream) stage (.chain 0) .quiet < 1)
    (stream : ℕ → Bool) :
    (∀ position, stream position = false) ∨ ∃ position, stream position = true := by
  obtain ⟨stage, close⟩ := modulus stream
  rcases bounded_search stream stage with clear | ⟨position, _, found⟩
  · refine Or.inl fun position => ?_
    have stageZero := (signal_depthBound_eq_zero_iff stream stage).mpr clear
    have later := close (max stage position) (le_max_left _ _)
    rw [stageZero, sub_zero] at later
    have nonneg := (signal stream).depthBound_nonneg (signalVocabulary stream)
      (max stage position) (.chain 0) .quiet
    have zero : (signal stream).depthBound (signalVocabulary stream) (max stage position)
        (.chain 0) .quiet = 0 := by omega
    exact (signal_depthBound_eq_zero_iff stream _).mp zero position (le_max_right _ _)
  · exact Or.inr ⟨position, found⟩

/-! ## Errors add and are attained -/

/-- Readings `0` on `false` and `top` on `true`, on the scale with unit two. -/
def gradedReading (top : ℤ) : Bool → ℤ
  | false => 0
  | true => top

def graded (top : ℤ) (nonneg : 0 ≤ top) (le : top ≤ 2) :
    PresentedSystem.{0, 0, 0, 0, 0} pairTheory halfScale where
  dynamics := stillDynamics
  Obs := Unit
  value _ := gradedReading top
  value_nonneg _ term := by cases term; exacts [by show (0 : ℤ) ≤ 0; decide, nonneg]
  value_le_one _ term := by cases term; exacts [by show (0 : ℤ) ≤ 2; decide, le]
  value_resp _ _ _ same := by
    have equal := same
    rw [show _ = _ from equal]
  successors _ _ := []
  successors_act member := absurd member List.not_mem_nil
  successors_cover step := step.elim

/-- The identity raising every reading of `true` by `1`. -/
def rise (low high : ℤ) (lowNonneg : 0 ≤ low) (lowLe : low ≤ 2) (highNonneg : 0 ≤ high)
    (highLe : high ≤ 2) (step : high - low = 1) :
    ObservationMap (graded low lowNonneg lowLe) (graded high highNonneg highLe) 1 where
  error_nonneg := by decide
  mapTerm := id
  mapEquiv := fun same => same
  atom := id
  label := id
  value_close _ term := by
    cases term
    · show |(0 : ℤ) - 0| ≤ 1
      decide
    · show |high - low| ≤ 1
      rw [step]
      decide
  mapAct _ _ _ step := step.elim
  liftAct _ _ _ step := step.elim

/-- **Two maps of error `1` compose to a map of error `1 + 1`.** -/
def composite : ObservationMap (graded 0 (by decide) (by decide)) (graded 2 (by decide) (by decide))
    (1 + 1) :=
  (rise 0 1 (by decide) (by decide) (by decide) (by decide) (by decide)).comp
    (rise 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))

/-- **The composite error is attained** by a formula value. -/
theorem composite_error_attained :
    |(graded 2 (by decide) (by decide)).val (composite.translate (.atom ())) (composite.mapTerm true) -
        (graded 0 (by decide) (by decide)).val (.atom ()) true| = 1 + 1 := by
  decide

/-- **A positive error bound gives no exact transport.** -/
theorem composite_not_exact :
    (graded 2 (by decide) (by decide)).val (composite.translate (.atom ())) (composite.mapTerm true) ≠
      (graded 0 (by decide) (by decide)).val (.atom ()) true := by
  decide

end Mettapedia.GSLT.Distinction.Constructive.Controls
