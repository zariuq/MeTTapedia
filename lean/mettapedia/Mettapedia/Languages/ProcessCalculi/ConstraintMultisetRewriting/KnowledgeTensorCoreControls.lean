import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreFirstOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorFirstOrderControls

/-!
# Controls for the graded reading on the step

Terms are numbers under syntactic equality, with one substitution. The placements are those of
the first-order step: a configuration beside another.

* **A read is admitted beside every compatible context.** The firing `reads` has no check. It is
  stable (`reads_is_stable`), it is admitted beside the occurrence `9`
  (`reads_is_admitted_beside_nine`), and its one-firing run has a placed native run there
  (`reads_has_a_placed_run`).
* **Absence is graded.** The firing `unlessNine` is admitted alone, its placed candidate beside
  the occurrence `9` is prepared and leaves the context unchanged
  (`unless_nine_fits_beside_nine`), and it is refused there (`unless_nine_refused_beside_nine`).
  So admission is not stable (`absence_is_not_stable`, `admission_is_not_stable`), the grade of
  its run is strictly inside the structural part (`absence_grade_is_not_structural`), and no
  placed run exists (`unless_nine_has_no_placed_run`).
* **Counting is graded, in both directions.** With every occurrence labelled `5`, the firing
  `counts n` is admitted exactly at stores of `n` occurrences (`counts_valid_iff`). `counts 1` is
  admitted at one occurrence and refused beside a second (`counting_is_not_stable`). `counts 2`
  is refused at each of two one-occurrence configurations and admitted at their tensor
  (`a_count_is_enabled_by_its_context`): a native event that is the placed candidate of no
  admitted local firing.
* **The structural part has content.** Beside a context whose knowledge is inconsistent no
  candidate is prepared (`nothing_fits_beside_inconsistent_knowledge`), and beside a context that
  holds the occurrence the firing would make it is not prepared either
  (`nothing_fits_beside_an_occupied_output`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.Controls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open AnnotatedRuns (Firing firstOrder firstOrderTransport)
open FirstOrderNativeRuns
open KnowledgeTensorFirstOrder
open KnowledgeTensorFirstOrderControls (plain one unlessNine makeSeven twice pick)

/-- The occurrence `9` alone. -/
def nine : Configuration Nat Nat := ⟨[], {9}⟩

/-! ## A read is admitted beside every compatible context -/

def reads : Firing Nat Unit Nat := ⟨twice, [], pick⟩

theorem reads_admitted : reads.Valid plain id one :=
  (Firing.valid_ofPlain_iff plain id (twice, pick) one).mpr
    KnowledgeTensorFirstOrderControls.pick_is_admitted

theorem reads_is_stable (left right : Configuration Nat Nat) :
    StableAt (contextualRunInterpretation plain id) (left := left) (right := right) PUnit.unit reads :=
  FirstOrder.stableAt_of_guardsOnly plain id reads
    (by intro check member; cases member) rfl

theorem reads_prepared_beside_nine :
    (firstOrder plain id).toStep.Prepares (s := AnnotatedRuns.tensor one nine) reads := by
  refine ⟨⟨List.nodup_nil, List.nodup_singleton 7, rfl, rfl, rfl⟩, by decide, PUnit.unit, (), ?_⟩
  intro equation member
  have shape : pick.problem id twice (AnnotatedRuns.tensor one nine) = [(5, 5), (5, 5)] := rfl
  have inside : equation ∈ [((5 : Nat), (5 : Nat)), (5, 5)] := shape ▸ member
  rcases List.mem_cons.mp inside with rfl | later
  · exact rfl
  · rcases List.mem_cons.mp later with rfl | empty
    · exact rfl
    · cases empty

theorem reads_frames_nine :
    (contextualRunInterpretation plain id).domain (left := one) (right := nine) PUnit.unit reads := by
  show Disjoint ([] : List Nat).toFinset ({9} : Finset Nat)
  decide

theorem reads_is_admitted_beside_nine : reads.Valid plain id (AnnotatedRuns.tensor one nine) :=
  reads_is_stable one nine reads_admitted reads_frames_nine reads_prepared_beside_nine

def readsRun : (firstOrder plain id).toStep.Run one := .cons reads reads_admitted (.nil _)

theorem reads_has_a_placed_run :
    ∃ native : (firstOrder plain id).toStep.Run (AnnotatedRuns.tensor one nine),
      Places (contextualRunInterpretation plain id) (left := one) (right := nine) PUnit.unit
        readsRun native :=
  (exists_places_iff_checks (contextualRunInterpretation plain id) (left := one) (right := nine)
    PUnit.unit readsRun).mpr
    ⟨⟨reads_frames_nine, (valid_tensor_iff plain id reads reads_admitted).mp
      reads_is_admitted_beside_nine⟩, trivial⟩

/-! ## Absence is graded -/

def unlessNineFiring : Firing Nat Unit Nat := ⟨unlessNine, [], makeSeven⟩

theorem unless_nine_admitted : unlessNineFiring.Valid plain id one :=
  (Firing.valid_ofPlain_iff plain id (unlessNine, makeSeven) one).mpr
    KnowledgeTensorFirstOrderControls.unless_nine_is_admitted

theorem unless_nine_prepared_beside_nine :
    (firstOrder plain id).toStep.Prepares (s := AnnotatedRuns.tensor one nine) unlessNineFiring := by
  refine ⟨⟨List.nodup_nil, List.nodup_singleton 7, rfl, rfl, rfl⟩, by decide, PUnit.unit, (), ?_⟩
  intro equation member
  cases member

theorem unless_nine_frames_nine :
    (contextualRunInterpretation plain id).domain (left := one) (right := nine) PUnit.unit
      unlessNineFiring := by
  show Disjoint ([] : List Nat).toFinset ({9} : Finset Nat)
  decide

theorem unless_nine_refused_beside_nine :
    ¬ unlessNineFiring.Valid plain id (AnnotatedRuns.tensor one nine) := by
  intro valid
  have solved : plain.Models () (makeSeven.problem id unlessNine (AnnotatedRuns.tensor one nine)) := by
    intro equation member
    cases member
  have holds := valid.firing.checks (Check.absent 9) (List.mem_singleton.mpr rfl) () solved
  exact holds 9 (by decide) rfl

def unlessNineRun : (firstOrder plain id).toStep.Run one :=
  .cons unlessNineFiring unless_nine_admitted (.nil _)

theorem unless_nine_fits_beside_nine :
    Fits (contextualRunInterpretation plain id) (left := one) (right := nine) PUnit.unit
      unlessNineRun :=
  ⟨⟨unless_nine_frames_nine, unless_nine_prepared_beside_nine⟩, trivial⟩

theorem absence_is_not_stable :
    ¬ StableAt (contextualRunInterpretation plain id) (left := one) (right := nine) PUnit.unit
      unlessNineFiring :=
  fun stable => unless_nine_refused_beside_nine
    (stable unless_nine_admitted unless_nine_frames_nine unless_nine_prepared_beside_nine)

theorem admission_is_not_stable : ¬ Stable (contextualRunInterpretation plain id) :=
  fun stable => absence_is_not_stable (stable (left := one) (right := nine) PUnit.unit unlessNineFiring)

theorem absence_grade_is_not_structural :
    Fits (contextualRunInterpretation plain id) (left := one) (right := nine) PUnit.unit
        unlessNineRun ∧
      ¬ (contextualRunInterpretation plain id).Checks (left := one) (right := nine) PUnit.unit
        unlessNineRun :=
  ⟨unless_nine_fits_beside_nine, fun checked => unless_nine_refused_beside_nine
    ((valid_tensor_iff plain id unlessNineFiring unless_nine_admitted).mpr checked.1.2)⟩

theorem unless_nine_has_no_placed_run :
    ¬ ∃ native : (firstOrder plain id).toStep.Run (AnnotatedRuns.tensor one nine),
      Places (contextualRunInterpretation plain id) (left := one) (right := nine) PUnit.unit
        unlessNineRun native :=
  fun placed => absence_grade_is_not_structural.2
    ((exists_places_iff_checks (contextualRunInterpretation plain id) (left := one) (right := nine)
      PUnit.unit unlessNineRun).mp placed)

/-! ## Counting is graded, in both directions -/

/-- Every occurrence is labelled `5`. -/
def five (_ : Nat) : Nat := 5

/-- A firing that takes, reads and makes nothing, and checks that exactly `number` occurrences
are labelled `5`. -/
def counts (number : Nat) : Firing Nat Unit Nat :=
  ⟨⟨[], [], [], [Check.count 5 number], []⟩, [], ⟨[], [], []⟩⟩

theorem all_match (store : Finset Nat) : Check.matches plain () five store 5 = store := by
  ext occurrence
  simp only [Check.matches, Finset.mem_filter]
  exact ⟨And.left, fun inside => ⟨inside, rfl⟩⟩

theorem counts_valid_iff (number : Nat) (present : Finset Nat) :
    (counts number).Valid plain five ⟨[], present⟩ ↔ present.card = number := by
  constructor
  · intro valid
    have solved : plain.Models () ((counts number).selection.problem five (counts number).rule
        ⟨[], present⟩) := by
      intro equation member
      cases member
    have holds := valid.firing.checks (Check.count 5 number) (List.mem_singleton.mpr rfl) () solved
    have counted : (Check.matches plain () five present 5).card = number := holds
    rw [all_match] at counted
    exact counted
  · intro size
    refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, ?_, ⟨(), ?_⟩, ?_⟩, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Selection.commit, counts]
    · intro equation member
      cases member
    · intro check member σ _
      have only : check = Check.count 5 number := List.mem_singleton.mp member
      subst only
      show (Check.matches plain σ five present 5).card = number
      rw [all_match]
      exact size
    · intro query member
      cases member

def zero : Configuration Nat Nat := ⟨[], {0}⟩

def another : Configuration Nat Nat := ⟨[], {1}⟩

theorem counts_one_admitted : (counts 1).Valid plain five zero :=
  (counts_valid_iff 1 {0}).mpr (by decide)

theorem counts_one_refused_beside_another :
    ¬ (counts 1).Valid plain five (AnnotatedRuns.tensor zero another) := by
  intro valid
  have size := (counts_valid_iff 1 ({0} ∪ {1})).mp valid
  exact absurd size (by decide)

theorem counts_one_prepared_beside_another :
    (firstOrder plain five).toStep.Prepares (s := AnnotatedRuns.tensor zero another) (counts 1) := by
  refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl⟩, by decide, PUnit.unit, (), ?_⟩
  intro equation member
  cases member

theorem counting_is_not_stable :
    ¬ StableAt (contextualRunInterpretation plain five) (left := zero) (right := another) PUnit.unit
      (counts 1) := by
  intro stable
  refine counts_one_refused_beside_another (stable counts_one_admitted ?_ counts_one_prepared_beside_another)
  show Disjoint ([] : List Nat).toFinset ({1} : Finset Nat)
  decide

/-- **A count can be enabled by its context.** The native event at the tensor is the placed
candidate of no admitted local firing: the firing is refused at each part. -/
theorem a_count_is_enabled_by_its_context :
    (counts 2).Valid plain five (AnnotatedRuns.tensor zero another) ∧
      ¬ (counts 2).Valid plain five zero ∧ ¬ (counts 2).Valid plain five another := by
  refine ⟨(counts_valid_iff 2 ({0} ∪ {1})).mpr (by decide), ?_, ?_⟩
  · intro valid
    exact absurd ((counts_valid_iff 2 {0}).mp valid) (by decide)
  · intro valid
    exact absurd ((counts_valid_iff 2 {1}).mp valid) (by decide)

/-! ## The structural part has content -/

/-- A context whose knowledge is inconsistent. -/
def inconsistent : Configuration Nat Nat := ⟨[(1, 2)], ∅⟩

theorem nothing_fits_beside_inconsistent_knowledge :
    ¬ Fits (contextualRunInterpretation plain id) (left := one) (right := inconsistent) PUnit.unit
      readsRun := by
  intro fitted
  obtain ⟨_, _, solved⟩ := fitted.1.2.2.2
  have member : ((1 : Nat), (2 : Nat)) ∈ pick.problem id twice (AnnotatedRuns.tensor one inconsistent) := by
    have shape : pick.problem id twice (AnnotatedRuns.tensor one inconsistent) =
        [(1, 2), (5, 5), (5, 5)] := rfl
    rw [shape]
    exact List.mem_cons_self
  have wrong : (1 : Nat) = 2 := solved (1, 2) member
  exact absurd wrong (by decide)

/-- A context that already holds the occurrence the firing would make. -/
def occupied : Configuration Nat Nat := ⟨[], {7}⟩

theorem nothing_fits_beside_an_occupied_output :
    ¬ Fits (contextualRunInterpretation plain id) (left := one) (right := occupied) PUnit.unit
      readsRun := by
  intro fitted
  have fresh : Disjoint ({7} : Finset Nat) ({5} ∪ {7}) := fitted.1.2.2.1.fresh
  exact absurd fresh (by decide)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.Controls
