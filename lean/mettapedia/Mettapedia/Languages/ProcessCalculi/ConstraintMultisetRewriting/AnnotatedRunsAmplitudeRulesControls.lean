import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsAmplitudeGather
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsAmplitudeControls

/-!
# Controls for waveform guards as transform rules

A store holds path rows: `30` and `32` carry the path `1`, `31` carries `-1`.

* **The cancellation guard fires on a cancelling region and is refused once a path arrives**
  (`guard_fires`, `guard_refused_after_arrival`, `guard_refused_three`): with the rows `30` and `31`
  the region cancels and the guard produces the row of amplitude zero at `40`. Once `32` arrives,
  the guard whose query saw `30` and `31` is refused, and one whose query saw all three rows is
  refused because they do not cancel.
* **A reader cannot certify the cancellation** (`reader_cannot_certify`): a firing that reads `30`
  and `31`, without a predicate query, is admitted before and after `32` arrives, while the region
  cancels only before.
* **The same guard is sound with its predicate query and unsound without it** (`query_needed`):
  the cancellation guard decided on the rows it read, instead of on a predicate query, still fires
  once `32` has arrived, and produces the row of amplitude zero where the region does not cancel.
* **The reinforcement guard** (`reinforcement_fires`, `reinforcement_refused_after_arrival`): with
  the rows `30` and `32` the region reinforces, `4` against `2`, and the guard produces the row of
  the amplitude `2` at `41`; once `31` arrives the region gives `1` against `3`.
* **From branches to a rule** (`superposition_gathered_cancels`): R27's two superposed alternatives,
  with amplitudes `1` and `-1`, form a complete collection that certifies a cancellation. Gathered
  as the rows `30` and `31` into an empty store, they let the cancellation guard fire there.
* **A dark fringe** (`Fringe.dark_fringe`): of three superposed alternatives, two of amplitudes `1`
  and `-1` end in the outcome `yes` and one of amplitude `1` in `no`. The incoherent readout gives
  `yes` the probability `2/3`; the `yes` paths cancel, so its Born probability is `0`.
  That reading gives the two `yes` histories one end, as the nominal end does
  (`AggregationControls.Superposed.nominal_interferes` for the same pair); with the
  identity-observing end their answer rows are records and `yes` reads `2/3`
  (`QuantumFringe.dark_fringe_recorded`).
* **The status travels with the rows** (`complete_published_fires`, `incomplete_published_refused`):
  gathered with its status row, the complete collection fires the certified guard. The staged
  superposition at depth budget `1` has an incomplete collection whose paths `1` and `-1` cancel;
  gathered with its status row, its rows cancel at the new cut, yet the certified guard reading that
  row is refused at every cut.
-/

set_option autoImplicit false

open scoped QuadraticAlgebra

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns.AmplitudeRuns.WaveControls

open Mettapedia.Algebra.RationalComplexAmplitude (Amplitude born born_zero_iff)
open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open MeTTaCalculus.OccurrenceCommits (regionOf mem_regionOf)
open WorldModelRuns (GuardBits)
open AmplitudeControls (everything)

abbrev Run := Firing (Term signature) (Subst signature) Nat

/-- Rows `30` and `32` carry `1`, row `31` carries `-1`; `33` and `34` are status rows, complete
and incomplete; `40` is the row of amplitude zero and `41` the row of a nonzero amplitude. -/
def waveLabel : Nat → Term signature
  | 30 => .const 1
  | 31 => .const 2
  | 32 => .const 1
  | 33 => .const 3
  | 34 => .const 4
  | 40 => .const 5
  | 41 => .const 6
  | _ => .const 7

/-- The amplitude a row carries. -/
def wave : Term signature → Amplitude
  | .const 1 => 1
  | .const 2 => -1
  | _ => 0

/-- The wave region: the rows that carry paths. -/
def region : Term signature → Bool
  | .const 1 => true
  | .const 2 => true
  | _ => false

/-- The row of a produced amplitude: `5` for zero, `6` otherwise. -/
def row (z : Amplitude) : Term signature := if z = 0 then .const 5 else .const 6

/-- Guard verdicts: `1` for yes and `0` for no, which no substitution identifies. -/
def bits : GuardBits A :=
  ⟨.const 1, .const 0, fun _ same => by
    change (Term.const (σ := signature) 0) = .const 1 at same
    cases same⟩

theorem consistent_nil : A.Consistent ([] : EquationStore (Term signature)) :=
  ⟨Subst.id signature, fun _ member => by cases member⟩

theorem neg_one_ne_one : (-1 : Amplitude) ≠ 1 := fun same => by
  have parts := congrArg QuadraticAlgebra.re same
  norm_num at parts

theorem two_ne_zero' : (1 + 1 : Amplitude) ≠ 0 := fun same => by
  have weight := congrArg born same
  rw [born_double, born_one, born_zero] at weight
  norm_num at weight

/-! ## The cancellation guard -/

/-- The rows `30` and `31`: the paths `1` and `-1`. -/
def twoPaths : Configuration (Term signature) Nat := ⟨[], {30, 31}⟩

/-- The third path `32` has arrived. -/
def threePaths : Configuration (Term signature) Nat := ⟨twoPaths.equations, twoPaths.present ∪ {32}⟩

theorem region_two : regionOf waveLabel twoPaths.present region = {30, 31} := by decide

theorem paths_two : regionPaths waveLabel wave region twoPaths = {1, -1} := by
  unfold regionPaths pathsOf
  rw [region_two, Finset.insert_val_of_notMem (by decide), Finset.singleton_val, Multiset.map_cons,
    Multiset.map_singleton]
  rfl

theorem twoPaths_cancel : Destructive (regionPaths waveLabel wave region twoPaths) := by
  rw [paths_two]
  exact opposite_phase_control.2.2

theorem threePaths_do_not_cancel :
    ¬ Destructive (regionPaths waveLabel wave region threePaths) := by
  unfold threePaths
  rw [regionPaths_arrival waveLabel wave region twoPaths (by decide) rfl, paths_two]
  exact third_path_flips.2.2.2

/-- The cancellation guard on the wave region, whose predicate query saw `30` and `31`, making
`40`. -/
def guard : Run := cancellationFiring A waveLabel wave bits row region {30, 31} 40

/-- **The cancellation guard fires on the cancelling region**, and produces the row of amplitude
zero. -/
theorem guard_fires : guard.Valid A waveLabel twoPaths ∧ waveLabel 40 = row 0 := by
  have rowZero : waveLabel 40 = row 0 := by simp [row, waveLabel]
  have fires := waveform_fires A waveLabel wave (bits := bits) (row := row) (r := 40)
    twoPaths_cancel (by decide) (rowZero.trans (congrArg row twoPaths_cancel.1.symm))
    consistent_nil
  rw [region_two] at fires
  exact ⟨fires, rowZero⟩

/-- **Once the third path arrives, the guard's predicate query is refused.** -/
theorem guard_refused_after_arrival : ¬ guard.Valid A waveLabel threePaths :=
  waveform_refuses_arrival A waveLabel wave guard_fires.1 (by decide) rfl

/-- **A predicate query that saw all three paths is refused too: they do not cancel.** -/
theorem guard_refused_three :
    ¬ (cancellationFiring A waveLabel wave bits row region (regionOf waveLabel threePaths.present
      region) 40 : Run).Valid A waveLabel threePaths :=
  waveform_refused A waveLabel wave threePaths_do_not_cancel

/-! ## A reader cannot certify the cancellation -/

/-- Reads `30` and `31` and makes `41`; no guard and no predicate query. -/
def pairReader : Run := ⟨⟨[], [.const 1, .const 2], [], [], [.const 6]⟩, [], ⟨[], [30, 31], [41]⟩⟩

theorem pairReader_valid : pairReader.Valid A waveLabel twoPaths := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨Subst.id signature, ?_⟩,
    by simp [pairReader]⟩, by simp [pairReader]⟩
  intro equation member
  have cases : equation = (.const 1, waveLabel 30) ∨ equation = (.const 2, waveLabel 31) := by
    simpa [Selection.problem, Selection.equations, twoPaths, pairReader] using member
  rcases cases with rfl | rfl <;> rfl

/-- **A reader cannot certify the cancellation**: it is admitted with the two paths, which cancel,
and after the third arrives, when they do not. -/
theorem reader_cannot_certify :
    pairReader.Valid A waveLabel twoPaths ∧
      Destructive (regionPaths waveLabel wave region twoPaths) ∧
      pairReader.Valid A waveLabel threePaths ∧
      ¬ Destructive (regionPaths waveLabel wave region threePaths) :=
  ⟨pairReader_valid, twoPaths_cancel,
    reads_cannot_certify_cancellation A waveLabel wave region
      (fun check member => by simp [pairReader] at member) rfl pairReader_valid twoPaths_cancel
      (by decide) (by decide) rfl one_ne_zero'⟩

/-- The cancellation guard without its predicate query: it reads `30` and `31` and decides its guard
on the paths it read. -/
def readGuard : Run :=
  ⟨⟨[], [.const 1, .const 2], [], [bits.check (decide (Destructive {1, -1}))], [.const 5]⟩, [],
    ⟨[], [30, 31], [40]⟩⟩

theorem readGuard_valid : readGuard.Valid A waveLabel twoPaths := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨Subst.id signature, ?_⟩, ?_⟩,
    by simp [readGuard]⟩
  · intro equation member
    have cases : equation = (.const 1, waveLabel 30) ∨ equation = (.const 2, waveLabel 31) := by
      simpa [Selection.problem, Selection.equations, twoPaths, readGuard] using member
    rcases cases with rfl | rfl <;> rfl
  · intro check member σ _
    rw [List.mem_singleton.mp member]
    exact (GuardBits.holds_iff waveLabel bits σ _ _).mpr
      (decide_eq_true opposite_phase_control.2.2)

/-- **The same guard is sound with its predicate query and unsound without it.** With the query, the
cancellation guard fires with the two paths and is refused once the third arrives. Deciding the
same verdict on the rows it read, the guard fires with the two paths and still fires once the
third arrives, producing the row of amplitude zero where the region does not cancel. -/
theorem query_needed :
    guard.Valid A waveLabel twoPaths ∧ ¬ guard.Valid A waveLabel threePaths ∧
      readGuard.Valid A waveLabel twoPaths ∧ readGuard.Valid A waveLabel threePaths ∧
      waveLabel 40 = row 0 ∧ ¬ Destructive (regionPaths waveLabel wave region threePaths) :=
  ⟨guard_fires.1, guard_refused_after_arrival, readGuard_valid,
    (reads_cannot_certify_cancellation A waveLabel wave region (o := 32)
      (fun check member => ⟨_, _, List.mem_singleton.mp member⟩) rfl readGuard_valid twoPaths_cancel
      (by decide) (by decide) rfl one_ne_zero').1,
    guard_fires.2, threePaths_do_not_cancel⟩

/-! ## The reinforcement guard -/

/-- The rows `30` and `32`: two paths `1`. -/
def alignedPaths : Configuration (Term signature) Nat := ⟨[], {30, 32}⟩

/-- The path `31` has arrived. -/
def opposedArrived : Configuration (Term signature) Nat :=
  ⟨alignedPaths.equations, alignedPaths.present ∪ {31}⟩

theorem region_aligned : regionOf waveLabel alignedPaths.present region = {30, 32} := by decide

theorem paths_aligned : regionPaths waveLabel wave region alignedPaths = {1, 1} := by
  unfold regionPaths pathsOf
  rw [region_aligned, Finset.insert_val_of_notMem (by decide), Finset.singleton_val,
    Multiset.map_cons, Multiset.map_singleton]
  rfl

/-- **The reinforcement guard fires on the reinforcing region**, `4` against `2`, and produces
the row of the amplitude `2` at `41`. -/
theorem reinforcement_fires :
    born (coherent (regionPaths waveLabel wave region alignedPaths)) = 4 ∧
      incoherent (regionPaths waveLabel wave region alignedPaths) = 2 ∧
      (reinforcementFiring A waveLabel wave bits row region {30, 32} 41 : Run).Valid A waveLabel
        alignedPaths := by
  have reinforces : Constructive (regionPaths waveLabel wave region alignedPaths) := by
    rw [paths_aligned]
    exact in_phase_control.2.2
  have rowEq : waveLabel 41 = row (coherent (regionPaths waveLabel wave region alignedPaths)) := by
    rw [paths_aligned, coherent_pair, row, if_neg two_ne_zero']
    rfl
  have fires := waveform_fires A waveLabel wave (bits := bits) (row := row) (r := 41) reinforces
    (by decide) rowEq consistent_nil
  rw [region_aligned] at fires
  refine ⟨?_, ?_, fires⟩
  · rw [paths_aligned]
    exact in_phase_control.1
  · rw [paths_aligned]
    exact in_phase_control.2.1

/-- **Once the path `-1` arrives, the region no longer reinforces** (`1` against `3`), and the
guard's predicate query is refused. -/
theorem reinforcement_refused_after_arrival :
    ¬ Constructive (regionPaths waveLabel wave region opposedArrived) ∧
      ¬ (reinforcementFiring A waveLabel wave bits row region {30, 32} 41 : Run).Valid A waveLabel
        opposedArrived := by
  refine ⟨?_, waveform_refuses_arrival A waveLabel wave reinforcement_fires.2.2 (by decide) rfl⟩
  unfold opposedArrived
  rw [regionPaths_arrival waveLabel wave region alignedPaths (by decide) rfl, paths_aligned]
  unfold Constructive
  rw [incoherent_cons, incoherent_pair, coherent_cons, coherent_pair]
  change ¬ (born (-1) + (born 1 + born 1) < born (-1 + (1 + 1)))
  rw [show (-1 : Amplitude) + (1 + 1) = 1 by ring, born_neg, born_one]
  norm_num

/-! ## From branches to a rule -/

/-- The row of a path: `1` for the path `1`, `2` for the path `-1`. -/
def pathRow (z : Amplitude) : Term signature :=
  if z = 1 then .const 1 else if z = -1 then .const 2 else .const 7

theorem pathRow_one : pathRow 1 = .const 1 := if_pos rfl

theorem pathRow_neg_one : pathRow (-1) = .const 2 := by
  rw [pathRow, if_neg neg_one_ne_one, if_pos rfl]

/-- An empty store. -/
def parent : Configuration (Term signature) Nat := ⟨[], ∅⟩

/-- The gather of the two paths `1` and `-1` as the rows `30` and `31`. -/
def gather : Run := gatherFiring pathRow [1, -1] [30, 31]

theorem gather_valid : gather.Valid A waveLabel parent := by
  refine ⟨⟨by decide, by decide, rfl, rfl, ?_, by decide, ⟨Subst.id signature, ?_⟩,
    by simp [gather, gatherFiring]⟩, by simp [gather, gatherFiring]⟩
  · change [waveLabel 30, waveLabel 31] = [pathRow 1, pathRow (-1)]
    rw [pathRow_one, pathRow_neg_one]
    rfl
  · intro equation member
    simp [Selection.problem, Selection.equations, parent, gather, gatherFiring] at member

theorem encodes : Encodes wave region pathRow [1, -1] := by
  intro z member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rw [pathRow_one]
    exact ⟨rfl, rfl⟩
  · rw [pathRow_neg_one]
    exact ⟨rfl, rfl⟩

/-- Where the gather leaves the store. -/
abbrev gathered : Configuration (Term signature) Nat := gather.result waveLabel parent

/-- **From branches to a rule.** R27's two superposed alternatives with amplitudes `1` and `-1`
form a complete collection that certifies a cancellation. Gathered as the rows `30` and `31` into
an empty store, they let the cancellation guard fire there, with a predicate query that saw those
rows. -/
theorem superposition_gathered_cancels :
    CertifiesCancellation (amplitudeCollection A AnnotatedRuns.Controls.label
        AmplitudeControls.Superposed.shifted
        AnnotatedRunBranchCollection.Controls.Superpose.alternatives 1
        AnnotatedRunBranchCollection.Controls.Superpose.root everything) ∧
      regionPaths waveLabel wave region gathered = {1, -1} ∧
      (cancellationFiring A waveLabel wave bits row region
        (regionOf waveLabel gathered.present region) 40 : Run).Valid A waveLabel gathered := by
  have cancelled := AmplitudeControls.Superposed.superposed_cancel
  have empty : regionOf waveLabel parent.present region = ∅ := by decide
  refine ⟨cancelled.2.2.2.2.1, ?_, ?_⟩
  · exact (gather_regionPaths A waveLabel wave gather_valid empty encodes).trans rfl
  · exact (gather_then_guard_iff A waveLabel wave cancelled.2.2.2.1 rfl gather_valid empty encodes
      bits row (by decide) (by simp [row, waveLabel]) consistent_nil).mpr cancelled.2.2.2.2.1

/-! ## The status travels with the rows -/

/-- Status marks: `3` for complete and `4` for incomplete, which no substitution identifies. -/
def statusBits : GuardBits A :=
  ⟨.const 3, .const 4, fun _ same => by
    change (Term.const (σ := signature) 4) = .const 3 at same
    cases same⟩

/-- The superposition's complete collection gathered with its status: rows `30` and `31`, status
`33`. -/
def completeGather : Run :=
  statusGatherFiring A statusBits (.complete {1, -1}) pathRow [1, -1] [30, 31] 33

/-- The staged superposition's incomplete collection gathered with its status: rows `30`, `31`,
status `34`. -/
def incompleteGather : Run :=
  statusGatherFiring A statusBits (.incomplete {1, -1}) pathRow [1, -1] [30, 31] 34

theorem completeGather_valid : completeGather.Valid A waveLabel parent := by
  refine ⟨⟨by decide, by decide, rfl, rfl, ?_, by decide, ⟨Subst.id signature, ?_⟩,
    by simp [completeGather, statusGatherFiring]⟩, by simp [completeGather, statusGatherFiring]⟩
  · change [waveLabel 30, waveLabel 31, waveLabel 33] =
      [pathRow 1, pathRow (-1)] ++ [statusMark A statusBits (.complete {1, -1})]
    rw [pathRow_one, pathRow_neg_one]
    rfl
  · intro equation member
    simp [Selection.problem, Selection.equations, parent, completeGather, statusGatherFiring]
      at member

theorem incompleteGather_valid : incompleteGather.Valid A waveLabel parent := by
  refine ⟨⟨by decide, by decide, rfl, rfl, ?_, by decide, ⟨Subst.id signature, ?_⟩,
    by simp [incompleteGather, statusGatherFiring]⟩, by simp [incompleteGather, statusGatherFiring]⟩
  · change [waveLabel 30, waveLabel 31, waveLabel 34] =
      [pathRow 1, pathRow (-1)] ++ [statusMark A statusBits (.incomplete {1, -1})]
    rw [pathRow_one, pathRow_neg_one]
    rfl
  · intro equation member
    simp [Selection.problem, Selection.equations, parent, incompleteGather, statusGatherFiring]
      at member

/-- Where the complete gather leaves the store. -/
abbrev afterComplete : Configuration (Term signature) Nat := completeGather.result waveLabel parent

/-- Where the incomplete gather leaves the store. -/
abbrev afterIncomplete : Configuration (Term signature) Nat :=
  incompleteGather.result waveLabel parent

theorem afterComplete_consistent :
    A.Consistent (afterComplete.equations ++ [(statusBits.yes, waveLabel 33)]) := by
  refine ⟨Subst.id signature, fun equation member => ?_⟩
  have same : equation = (statusBits.yes, waveLabel 33) := by
    simpa [afterComplete, completeGather, statusGatherFiring, Firing.result, Selection.result,
      Selection.problem, Selection.equations, parent] using member
  subst same
  rfl

/-- **A complete collection published with its status fires the certified guard.** R27's
superposition with amplitudes `1` and `-1` certifies a cancellation; gathered with its status row,
the certified guard fires with a predicate query of its rows and produces the row of amplitude
zero. -/
theorem complete_published_fires :
    (certifiedCancellationFiring A waveLabel wave statusBits bits row region
      (regionOf waveLabel afterComplete.present region) 33 40 : Run).Valid A waveLabel
        afterComplete := by
  have cancelled := AmplitudeControls.Superposed.superposed_cancel
  exact (statusGather_complete_iff A waveLabel wave (bits := bits) (row := row)
    cancelled.2.2.2.1 rfl completeGather_valid (by decide) encodes rfl (by decide)
    (by simp [row, waveLabel]) afterComplete_consistent).mpr cancelled.2.2.2.2.1

/-- **An incomplete collection published with its status never fires the certified guard.** The
staged superposition at depth budget `1` has the incomplete collection `1, -1`. Gathered with its
status row, its rows cancel at the new cut, yet the certified guard reading that row is refused at
every cut, whatever its predicate query saw. -/
theorem incomplete_published_refused :
    amplitudeCollection A AnnotatedRuns.Controls.label AmplitudeControls.Superposed.shifted
        AmplitudeControls.Staged.staged 1 AnnotatedRunBranchCollection.Controls.Superpose.root
        everything = .incomplete {1, -1} ∧
      Destructive (regionPaths waveLabel wave region afterIncomplete) ∧
      ∀ (seen : Finset Nat) (r : Nat) (D : Configuration (Term signature) Nat),
        ¬ (certifiedCancellationFiring A waveLabel wave statusBits bits row region seen 34 r :
          Run).Valid A waveLabel D := by
  refine ⟨AmplitudeControls.Staged.partial_cancellation_not_certified.2.1, ?_,
    fun _ _ _ => statusGather_incomplete_refused A waveLabel wave incompleteGather_valid⟩
  have gathered :
      regionPaths waveLabel wave region afterIncomplete = ({1, -1} : Multiset Amplitude) :=
    statusGather_regionPaths A waveLabel wave incompleteGather_valid (by decide) encodes rfl
  rw [gathered]
  exact opposite_phase_control.2.2

/-! ## A dark fringe -/

namespace Fringe

open AnnotatedRuns.Controls (label)
open AnnotatedRunBranchCollection.Controls.Superpose (root first second first_ne_second)
open AmplitudeControls (single_class_injective)
open AmplitudeControls.Superposed (shifted shifted_first shifted_second shifted_third third
  alternatives₃ branches₃ closed₃ first_ne_third second_ne_third)
open AnnotatedRunUnfolding (CausalClass)

/-- The outcome `yes`: the end holds the answer `20` or `21`. -/
def yesOutcome : ConfigurationClass A Nat → Prop :=
  Quotient.lift (fun C : Configuration (Term signature) Nat => 20 ∈ C.present ∨ 21 ∈ C.present)
    fun _ _ same => by simp only [same.2]

/-- The outcome `no`: the end holds the answer `22`. -/
def noOutcome : ConfigurationClass A Nat → Prop :=
  Quotient.lift (fun C : Configuration (Term signature) Nat => 22 ∈ C.present)
    fun _ _ same => by simp only [same.2]

open Classical in
theorem yes_branches :
    regionBranches A label alternatives₃ 1 root yesOutcome =
      {Quot.mk _ [first], Quot.mk _ [second]} := by
  ext trace
  rw [mem_regionBranches, branches₃]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨(rfl | rfl | rfl), inYes⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · change 20 ∈ (third.result label root).present ∨ 21 ∈ (third.result label root).present
        at inYes
      revert inYes
      decide
  · rintro (rfl | rfl)
    · refine ⟨Or.inl rfl, ?_⟩
      change 20 ∈ (first.result label root).present ∨ 21 ∈ (first.result label root).present
      decide
    · refine ⟨Or.inr (Or.inl rfl), ?_⟩
      change 20 ∈ (second.result label root).present ∨ 21 ∈ (second.result label root).present
      decide

open Classical in
theorem no_branches :
    regionBranches A label alternatives₃ 1 root noOutcome = {Quot.mk _ [third]} := by
  ext trace
  rw [mem_regionBranches, branches₃]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨(rfl | rfl | rfl), inNo⟩
    · change 22 ∈ (first.result label root).present at inNo
      revert inNo
      decide
    · change 22 ∈ (second.result label root).present at inNo
      revert inNo
      decide
    · rfl
  · rintro rfl
    refine ⟨Or.inr (Or.inr rfl), ?_⟩
    change 22 ∈ (third.result label root).present
    decide

open Classical in
theorem yes_paths : branchAmplitudes A label shifted alternatives₃ 1 root yesOutcome = {1, -1} := by
  unfold branchAmplitudes
  have notFirst : (Quot.mk _ [first] : CausalClass A label root) ∉
      ({Quot.mk _ [second]} : Finset (CausalClass A label root)) := by
    rw [Finset.mem_singleton]
    exact fun same => first_ne_second (single_class_injective same)
  rw [yes_branches, Finset.insert_val_of_notMem notFirst, Finset.singleton_val]
  simp [classAmplitude_mk, runAmplitude, shifted_first, shifted_second]

open Classical in
theorem no_paths : branchAmplitudes A label shifted alternatives₃ 1 root noOutcome = {1} := by
  unfold branchAmplitudes
  rw [no_branches, Finset.singleton_val]
  simp [classAmplitude_mk, runAmplitude, shifted_third]

/-- **A dark fringe.** Three superposed alternatives: the first two, of amplitudes `1` and `-1`,
end in the outcome `yes`; the third, of amplitude `1`, ends in the outcome `no`. Each `yes` path
alone has Born weight `1`, and the incoherent readout gives `yes` the probability `2/3`. Coherently
the `yes` paths cancel, which the complete collection certifies, the regional amplitudes are `0`
and `1`, and the Born probability of `yes` is `0`. This reads the two `yes` histories as having one end, which
holds for the nominal end and fails for the identity-observing end. -/
theorem dark_fringe :
    branchAmplitudes A label shifted alternatives₃ 1 root yesOutcome = {1, -1} ∧
      branchAmplitudes A label shifted alternatives₃ 1 root noOutcome = {1} ∧
      CertifiesCancellation (amplitudeCollection A label shifted alternatives₃ 1 root yesOutcome) ∧
      regionalAmplitude A label shifted alternatives₃ 1 root yesOutcome = 0 ∧
      regionalAmplitude A label shifted alternatives₃ 1 root noOutcome = 1 ∧
      bornProbability (regionalAmplitude A label shifted alternatives₃ 1 root yesOutcome)
        (regionalAmplitude A label shifted alternatives₃ 1 root noOutcome) = 0 ∧
      incoherent (branchAmplitudes A label shifted alternatives₃ 1 root yesOutcome) /
          (incoherent (branchAmplitudes A label shifted alternatives₃ 1 root yesOutcome) +
            incoherent (branchAmplitudes A label shifted alternatives₃ 1 root noOutcome)) =
        2 / 3 := by
  have yesZero : regionalAmplitude A label shifted alternatives₃ 1 root yesOutcome = 0 := by
    rw [regionalAmplitude_eq_coherent, yes_paths, coherent_pair, add_neg_cancel]
  have noOne : regionalAmplitude A label shifted alternatives₃ 1 root noOutcome = 1 := by
    rw [regionalAmplitude_eq_coherent, no_paths]
    simp [coherent]
  refine ⟨yes_paths, no_paths, (certifiesCancellation_iff A label shifted).mpr
    ⟨closed₃, yes_paths ▸ opposite_phase_control.2.2⟩, yesZero, noOne, ?_, ?_⟩
  · rw [yesZero, noOne]
    simp [bornProbability]
  · rw [yes_paths, no_paths, incoherent_pair, born_neg, born_one]
    simp [incoherent]
    norm_num

end Fringe

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns.AmplitudeRuns.WaveControls

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns.AmplitudeRuns

#print axioms WaveControls.paths_two
#print axioms WaveControls.twoPaths_cancel
#print axioms WaveControls.threePaths_do_not_cancel
#print axioms WaveControls.guard_fires
#print axioms WaveControls.guard_refused_after_arrival
#print axioms WaveControls.guard_refused_three
#print axioms WaveControls.pairReader_valid
#print axioms WaveControls.reader_cannot_certify
#print axioms WaveControls.readGuard_valid
#print axioms WaveControls.query_needed
#print axioms WaveControls.paths_aligned
#print axioms WaveControls.reinforcement_fires
#print axioms WaveControls.reinforcement_refused_after_arrival
#print axioms WaveControls.gather_valid
#print axioms WaveControls.encodes
#print axioms WaveControls.superposition_gathered_cancels
#print axioms WaveControls.completeGather_valid
#print axioms WaveControls.incompleteGather_valid
#print axioms WaveControls.complete_published_fires
#print axioms WaveControls.incomplete_published_refused
#print axioms WaveControls.Fringe.yes_branches
#print axioms WaveControls.Fringe.no_branches
#print axioms WaveControls.Fringe.dark_fringe
