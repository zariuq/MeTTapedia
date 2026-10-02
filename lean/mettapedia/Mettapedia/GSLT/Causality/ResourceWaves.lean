import Mettapedia.GSLT.Causality.ResourceReads
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# Constructing parallel waves from a finite resource catalogue

The selector scans candidates in their declared order. It admits a candidate
only when the consumption of the entire proposed wave fits beside the union
of its persistent reads. Rejected occurrences remain in a deferred list.

The resulting wave is enabled, occurrence-conserving, and inclusion-maximal
relative to this catalogue and snapshot. Every permutation executes through
the existing resource semantics and reaches the same bag. Maximality does
not assert maximum cardinality, fairness, or exhaustive exploration of
conflicting alternatives.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

universe uRes uRule

namespace System

variable {R : Type uRes} [DecidableEq R] (S : System.{uRes, uRule} R)

omit [DecidableEq R] in
theorem stepConsume_add (U V : Multiset S.Entry) :
    S.stepConsume (U + V) = S.stepConsume U + S.stepConsume V := by
  simp [stepConsume]

theorem stepRead_add (U V : Multiset S.Entry) :
    S.stepRead (U + V) = S.stepRead U ∪ S.stepRead V := by
  simp [stepRead]

/-- Resource-by-resource admission uses the largest persistent read and
the sum of both consumption counts. The natural-number sum does not wrap. -/
theorem stepEnables_add_iff_count (M : Multiset R) (U V : Multiset S.Entry) :
    S.StepEnables M (U + V) ↔ ∀ resource,
      max ((S.stepRead U).count resource) ((S.stepRead V).count resource) +
        (S.stepConsume U).count resource + (S.stepConsume V).count resource ≤
          M.count resource := by
  unfold StepEnables
  rw [S.stepConsume_add, S.stepRead_add, Multiset.le_iff_count]
  simp only [Multiset.count_add, Multiset.count_union]
  constructor <;> intro checked resource <;> have fits := checked resource <;> omega

/-- Removing candidate occurrences cannot increase a wave's resource demand. -/
theorem stepEnables_of_le {M : Multiset R} {U V : Multiset S.Entry}
    (subset : U ≤ V) (enabled : S.StepEnables M V) : S.StepEnables M U := by
  obtain ⟨extra, rfl⟩ := Multiset.le_iff_exists_add.mp subset
  unfold StepEnables at enabled ⊢
  rw [S.stepConsume_add, S.stepRead_add] at enabled
  exact le_trans
    (add_le_add (Multiset.le_add_right _ _) Multiset.le_union_left) enabled

instance decidableStepEnables (M : Multiset R) (U : Multiset S.Entry) :
    Decidable (S.StepEnables M U) :=
  inferInstanceAs (Decidable (S.stepConsume U + S.stepRead U ≤ M))

/-- Scan one finite catalogue, retaining both selected and deferred
occurrences. `reserved` contains the decisions already made by the scan. -/
def selectWaveAux (M : Multiset R) :
    List S.Entry → List S.Entry → List S.Entry × List S.Entry
  | _, [] => ([], [])
  | reserved, entry :: rest =>
      if S.StepEnables M (reserved ++ [entry]) then
        let later := selectWaveAux M (reserved ++ [entry]) rest
        (entry :: later.1, later.2)
      else
        let later := selectWaveAux M reserved rest
        (later.1, entry :: later.2)

/-- An executable priority-respecting wave selection at one snapshot. -/
def selectWave (M : Multiset R) (candidates : List S.Entry) :
    List S.Entry × List S.Entry :=
  S.selectWaveAux M [] candidates

/-- The accepted occurrences retain their catalogue order. -/
theorem selectWaveAux_selected_sublist (M : Multiset R) :
    ∀ (candidates reserved : List S.Entry),
      (S.selectWaveAux M reserved candidates).1.Sublist candidates
  | [], _ => .slnil
  | entry :: rest, reserved => by
      simp only [selectWaveAux]
      split
      · exact (selectWaveAux_selected_sublist M rest (reserved ++ [entry])).cons_cons _
      · exact (selectWaveAux_selected_sublist M rest reserved).cons _

/-- Deferred occurrences also retain their catalogue order. -/
theorem selectWaveAux_deferred_sublist (M : Multiset R) :
    ∀ (candidates reserved : List S.Entry),
      (S.selectWaveAux M reserved candidates).2.Sublist candidates
  | [], _ => .slnil
  | entry :: rest, reserved => by
      simp only [selectWaveAux]
      split
      · exact (selectWaveAux_deferred_sublist M rest (reserved ++ [entry])).cons _
      · exact (selectWaveAux_deferred_sublist M rest reserved).cons_cons _

/-- Selection preserves the availability of the whole wave, including all
previously reserved occurrences. -/
theorem selectWaveAux_enabled (M : Multiset R) :
    ∀ (candidates reserved : List S.Entry), S.StepEnables M reserved →
      S.StepEnables M (reserved ++ (S.selectWaveAux M reserved candidates).1)
  | [], _, enabled => by simpa [selectWaveAux] using enabled
  | entry :: rest, reserved, enabled => by
      simp only [selectWaveAux]
      split
      · next admitted =>
          simpa [List.append_assoc] using
            selectWaveAux_enabled M rest (reserved ++ [entry]) admitted
      · exact selectWaveAux_enabled M rest reserved enabled

/-- Every selected batch has a collectively checked resource certificate. -/
theorem selectWave_enabled (M : Multiset R) (candidates : List S.Entry) :
    S.StepEnables M (S.selectWave M candidates).1 := by
  simpa [selectWave] using S.selectWaveAux_enabled M candidates []
    (by simpa [StepEnables, stepConsume, stepRead] using (Multiset.zero_le M))

/-- No accepted occurrence is invented or reordered. -/
theorem selectWave_selected_sublist (M : Multiset R) (candidates : List S.Entry) :
    (S.selectWave M candidates).1.Sublist candidates :=
  S.selectWaveAux_selected_sublist M candidates []

/-- Deferred work remains an ordered part of the original catalogue. -/
theorem selectWave_deferred_sublist (M : Multiset R) (candidates : List S.Entry) :
    (S.selectWave M candidates).2.Sublist candidates :=
  S.selectWaveAux_deferred_sublist M candidates []

/-- Each candidate occurrence goes to exactly one output list. Equal entry
values retain their full multiplicity. -/
theorem selectWaveAux_partition (M : Multiset R) :
    ∀ (candidates reserved : List S.Entry),
      ((S.selectWaveAux M reserved candidates).1 ++
        (S.selectWaveAux M reserved candidates).2).Perm candidates
  | [], _ => .nil
  | entry :: rest, reserved => by
      simp only [selectWaveAux]
      split
      · exact (selectWaveAux_partition M rest (reserved ++ [entry])).cons entry
      · exact List.perm_middle.trans
          ((selectWaveAux_partition M rest reserved).cons entry)

/-- Accepted plus deferred is an exact occurrence partition, rather than a
support-set approximation. -/
theorem selectWave_partition (M : Multiset R) (candidates : List S.Entry) :
    ((S.selectWave M candidates).1 ++
      (S.selectWave M candidates).2).Perm candidates :=
  S.selectWaveAux_partition M candidates []

/-- No deferred occurrence can be added to the completed wave at the same
snapshot. This is inclusion-maximality, not maximum-cardinality selection. -/
theorem selectWaveAux_maximal (M : Multiset R) :
    ∀ (candidates reserved : List S.Entry) (entry : S.Entry),
      entry ∈ (S.selectWaveAux M reserved candidates).2 →
      ¬ S.StepEnables M
        (entry :: (reserved ++ (S.selectWaveAux M reserved candidates).1))
  | [], _, _, member => by simp [selectWaveAux] at member
  | head :: rest, reserved, entry, member => by
      simp only [selectWaveAux] at member ⊢
      by_cases admitted : S.StepEnables M (reserved ++ [head])
      · simp only [if_pos admitted] at member ⊢
        simpa [List.append_assoc] using
          selectWaveAux_maximal M rest (reserved ++ [head]) entry member
      · simp only [if_neg admitted] at member ⊢
        rcases List.mem_cons.mp member with rfl | later
        · intro enabled
          apply admitted
          apply S.stepEnables_of_le ?_ enabled
          have move : (reserved ++ [entry]).Perm (entry :: reserved) := by
            simpa only [List.append_nil] using
              (List.perm_middle (a := entry) (l₁ := reserved) (l₂ := []))
          exact Multiset.coe_le.mpr
            (move.subperm.trans
              ((List.sublist_append_left reserved
                (S.selectWaveAux M reserved rest).1).cons_cons entry).subperm)
        · exact selectWaveAux_maximal M rest reserved entry later

theorem selectWave_maximal (M : Multiset R) (candidates : List S.Entry)
    (entry : S.Entry) (deferred : entry ∈ (S.selectWave M candidates).2) :
    ¬ S.StepEnables M (entry :: (S.selectWave M candidates).1) := by
  simpa [selectWave] using S.selectWaveAux_maximal M candidates [] entry deferred

/-- Resource conservation is exact: executing the admitted wave consumes
its complete demand and retains the untouched frame. -/
theorem selectWave_consumption_conservation (M : Multiset R) (candidates : List S.Entry) :
    (M - S.stepConsume (S.selectWave M candidates).1) +
      S.stepConsume (S.selectWave M candidates).1 = M := by
  exact tsub_add_cancel_of_le
    (le_trans (Multiset.le_add_right _ _) (S.selectWave_enabled M candidates))

@[simp] theorem stepEnables_singleton_iff (M : Multiset R) (entry : S.Entry) :
    S.StepEnables M {entry} ↔ S.Enables M entry.2 := by
  simp [StepEnables, stepConsume, stepRead, Enables]

/-- A scan returns no work exactly when no catalogued candidate is enabled.
This is local catalogue quiescence; undiscovered matches are outside it. -/
theorem selectWave_empty_iff (M : Multiset R) (candidates : List S.Entry) :
    (S.selectWave M candidates).1 = [] ↔
      ∀ entry ∈ candidates, ¬ S.Enables M entry.2 := by
  constructor
  · intro empty entry member enabled
    have retained : entry ∈ (S.selectWave M candidates).1 ++
        (S.selectWave M candidates).2 :=
      (S.selectWave_partition M candidates).mem_iff.mpr member
    have deferred : entry ∈ (S.selectWave M candidates).2 := by
      simpa [empty] using retained
    have fits : S.StepEnables M (entry :: (S.selectWave M candidates).1) := by
      simpa [empty] using (S.stepEnables_singleton_iff M entry).mpr enabled
    exact S.selectWave_maximal M candidates entry deferred fits
  · intro noneEnabled
    cases chosen : (S.selectWave M candidates).1 with
    | nil => rfl
    | cons entry rest =>
        have selected : entry ∈ (S.selectWave M candidates).1 := by simp [chosen]
        have inCatalogue := (S.selectWave_selected_sublist M candidates).subset selected
        have one : S.StepEnables M {entry} :=
          S.stepEnables_of_le (Multiset.singleton_le.mpr selected)
            (S.selectWave_enabled M candidates)
        exact False.elim (noneEnabled entry inCatalogue
          ((S.stepEnables_singleton_iff M entry).mp one))

/-- The common result computed from the admitted finite wave. -/
def waveTarget (M : Multiset R) (entries : List S.Entry) : Multiset R :=
  M - S.stepConsume entries + S.stepProduce entries

/-- A selected wave is a genuine execution of the original resource system. -/
theorem selectWave_fires (M : Multiset R) (candidates : List S.Entry) :
    S.Fires (S.selectWave M candidates).1 M
      (S.waveTarget M (S.selectWave M candidates).1) :=
  S.fires_of_stepEnables _ M (S.selectWave_enabled M candidates)

/-- Changing worker order within the selected wave preserves the complete
final resource bag. This does not identify chronology-sensitive observers. -/
theorem selectWave_every_order {M : Multiset R} {candidates order : List S.Entry}
    (permutation : (S.selectWave M candidates).1.Perm order) :
    S.Fires order M (S.waveTarget M (S.selectWave M candidates).1) :=
  (S.step_orders_meet permutation (S.selectWave_enabled M candidates)).2

end System

/-! ## Resource-sensitive scheduling controls -/

namespace WaveControls

inductive Resource where
  | token
  | gate
  | fact
  | answer (identity : ℕ)
deriving DecidableEq

/-- Stable task identity and its required number of tokens. -/
def packing : System Resource where
  Site := Unit
  Instance := fun _ => ℕ × ℕ
  consume := fun task => Multiset.replicate task.2 Resource.token
  read := fun _ => 0
  produce := fun task => {Resource.answer task.1}

def job (identity demand : ℕ) : packing.Entry := ⟨(), identity, demand⟩

instance : DecidableEq packing.Entry := by
  change DecidableEq (Σ _ : Unit, ℕ × ℕ)
  infer_instance

def twoTokens : Multiset Resource := {.token, .token}

/-- Whole-wave validation rejects a third claimant even though each pair of
one-token jobs fits. No candidate occurrence disappears. -/
theorem collective_demand_controls_admission :
    (packing.selectWave twoTokens [job 1 1, job 2 1, job 3 1]).1 =
        [job 1 1, job 2 1] ∧
      (packing.selectWave twoTokens [job 1 1, job 2 1, job 3 1]).2 = [job 3 1] := by
  exact ⟨rfl, rfl⟩

/-- A greedy priority choice is inclusion-maximal but need not select the
largest possible number of tasks. Priority is an explicit strategy choice. -/
theorem maximal_is_not_maximum_cardinality :
    (packing.selectWave twoTokens [job 0 2, job 1 1, job 2 1]).1 = [job 0 2] ∧
      packing.StepEnables twoTokens [job 1 1, job 2 1] ∧
      (packing.selectWave twoTokens [job 0 2, job 1 1, job 2 1]).1.length <
        [job 1 1, job 2 1].length := by
  decide +kernel

/-- Two accepted uses of one equal entry retain two consumption and output
occurrences. A support set would lose this distinction. -/
theorem equal_entries_retain_multiplicity :
    packing.waveTarget twoTokens
        (packing.selectWave twoTokens [job 7 1, job 7 1]).1 =
      ({Resource.answer 7, Resource.answer 7} : Multiset Resource) := by
  decide +kernel

/-- Following one selected wave is not exhaustive all-answer search: another
enabled packing reaches a different observable result. -/
theorem choosing_a_wave_is_not_exhaustive :
    packing.Fires [job 0 2] twoTokens {Resource.answer 0} ∧
      packing.Fires [job 1 1, job 2 1] twoTokens
        {Resource.answer 1, Resource.answer 2} ∧
      ({Resource.answer 0} : Multiset Resource) ≠
        {Resource.answer 1, Resource.answer 2} := by
  simp only [System.Fires, System.Enables]
  decide +kernel

/-- One task produces the fact needed by the other. -/
def generatedWork : System Resource where
  Site := Unit
  Instance := fun _ => Bool
  consume := fun first => if first then {.token} else {.gate}
  read := fun first => if first then 0 else {.fact}
  produce := fun first => if first then {.fact} else {Resource.answer 9}

def producer : generatedWork.Entry := ⟨(), true⟩
def consumer : generatedWork.Entry := ⟨(), false⟩
def waiting : Multiset Resource := {.token, .gate}

instance : DecidableEq generatedWork.Entry := by
  change DecidableEq (Σ _ : Unit, Bool)
  infer_instance

/-- A deferred candidate is revalidated at the next snapshot. Its required
fact can be generated by the preceding wave. -/
theorem deferred_work_can_become_enabled :
    generatedWork.selectWave waiting [producer, consumer] = ([producer], [consumer]) ∧
      generatedWork.selectWave (generatedWork.waveTarget waiting [producer]) [consumer] =
        ([consumer], []) ∧
      generatedWork.Fires [producer, consumer] waiting
        {Resource.fact, Resource.answer 9} := by
  simp only [System.Fires, System.Enables]
  decide +kernel

/-- The two tasks write disjoint resource kinds, but the reader needs the
fact that the other task removes. -/
def readRace : System Resource where
  Site := Unit
  Instance := fun _ => Bool
  consume := fun reader => if reader then {.token} else {.fact}
  read := fun reader => if reader then {.fact} else 0
  produce := fun reader => {Resource.answer (if reader then 1 else 2)}

/-- Disjoint writes and separate initial enablement do not suffice for a
parallel wave. Read-before-consume is a genuine operational dependency. -/
theorem disjoint_writes_do_not_remove_read_conflicts :
    Disjoint (readRace.consume (site := ()) true + readRace.produce (site := ()) true)
        (readRace.consume (site := ()) false + readRace.produce (site := ()) false) ∧
      readRace.Enables {.token, .fact} (site := ()) true ∧
      readRace.Enables {.token, .fact} (site := ()) false ∧
      ¬ readRace.Concurrent {.token, .fact} (site₁ := ()) (site₂ := ()) true false ∧
      ¬ readRace.Enables (readRace.fire {.token, .fact} (site := ()) false)
        (site := ()) true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [readRace]
  · unfold System.Enables
    decide +kernel
  · unfold System.Enables
    decide +kernel
  · unfold System.Concurrent
    decide +kernel
  · unfold System.Enables
    decide +kernel

end WaveControls

end Mettapedia.GSLT.Causality.ResourceInteraction
