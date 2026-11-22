import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Waves
import Mettapedia.GSLT.Causality.ResourceWaves

/-!
# Waves by location footprints and waves by resource counts

`Regions.Waves` admits a wave by the footprints of its proposals: the writes of
each meet neither the reads nor the writes of another.
`GSLT.Causality.ResourceWaves` admits a wave of a resource system by counting at
a snapshot: the consumptions of all its instances, added, fit beside the largest
of their reads (`System.StepEnables`), and `System.selectWave_every_order` fires
the selected wave in every order to one bag.

The two are compared on what they share.  An instance of a resource system is a
local rule on multiplicities (`resourceRule`): it writes the kinds it consumes or
produces, and its guard asks that the consumed and the read resources are
present, which reads the kinds it reads.  The rule fires exactly as the instance
does (`resourceRule_fires_iff`).

* **A wave by footprints is a wave by counts**
  (`stepEnables_of_independent`): instances that are enabled one by one at a bag
  and independent in pairs as local rules are enabled together as a step.  So
  the selector takes all of them (`selectWave_of_stepEnables`), and
  `System.selectWave_every_order` fires them in every order to one bag
  (`independent_entries_every_order`).
* **The converse fails, for two reasons.**
  * *Counts are finer than kinds.*  Two consumers of two copies of one resource
    are a step, and as local rules both write the kind of that resource
    (`ResourceWaveControls.two_copies_step_not_independent`).
  * *A read of a resource system is a presence, and a production cannot remove a
    presence.*  A producer of a resource and a reader of it are a step when the
    resource is already there; as local rules the producer writes the kind that
    the reader reads (`ResourceWaveControls.producer_and_reader_step_not_independent`).  A
    guard of a local rule may ask for anything that is local, an absence
    included, and then a production does disable it
    (`FootprintedSpaceTransactions.SpaceRules.absence_guard_breaks_diamond`); such
    a guard is not a read of any resource system.
* The count is taken at one snapshot; the footprints are compared without one.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Causality.ResourceInteraction

universe uRes uRule

variable {R : Type uRes} [DecidableEq R] (S : System.{uRes, uRule} R)

/-- **An instance of a resource system, as a local rule on multiplicities.**  It
writes the kinds it consumes or produces.  Its guard asks that what it consumes
and what it reads are present together, and reads the kinds it reads. -/
def resourceRule {site : S.Site} (i : S.Instance site) : LocalRule R ℕ :=
  { markingRule (S.consume i) (S.produce i) with
    guard := fun state => ∀ resource, (S.consume i + S.read i).count resource ≤ state resource
    reads := (S.read i).toFinset
    guard_local := by
      intro source framed agrees holds resource
      by_cases inside : resource ∈
          (S.read i).toFinset ∪ ((S.consume i).toFinset ∪ (S.produce i).toFinset)
      · rw [← agrees resource inside]
        exact holds resource
      · have notRead : resource ∉ S.read i := fun member =>
          inside (Finset.mem_union_left _ (Multiset.mem_toFinset.mpr member))
        have notConsumed : resource ∉ S.consume i := fun member =>
          inside (Finset.mem_union_right _
            (Finset.mem_union_left _ (Multiset.mem_toFinset.mpr member)))
        rw [Multiset.count_add, Multiset.count_eq_zero.mpr notConsumed,
          Multiset.count_eq_zero.mpr notRead]
        exact Nat.zero_le _ }

/-- **The rule fires exactly as the instance does**: on the multiplicities of a
bag it is enabled when the instance is, and reaches the multiplicities of the bag
the instance fires to. -/
theorem resourceRule_fires_iff {site : S.Site} (i : S.Instance site) (M N : Multiset R) :
    (resourceRule S i).Fires (marking M) (marking N) ↔ S.Enables M i ∧ N = S.fire M i := by
  have guardIff :
      (∀ resource, (S.consume i + S.read i).count resource ≤ marking M resource) ↔
        S.Enables M i :=
    Multiset.le_iff_count.symm
  constructor
  · rintro ⟨guarded, frame, consumedSeparate, producedSeparate, decomposition, result⟩
    have enabled : S.Enables M i := guardIff.mp guarded
    refine ⟨enabled, ?_⟩
    obtain ⟨bagFrame, rfl, rfl⟩ :=
      (bagRule_iff_fires (S.consume i) (S.produce i) M N).mpr
        ⟨trivial, frame, consumedSeparate, producedSeparate, decomposition, result⟩
    show S.produce i + bagFrame = S.consume i + bagFrame - S.consume i + S.produce i
    rw [add_tsub_cancel_left, add_comm]
  · rintro ⟨enabled, rfl⟩
    have contained : S.consume i ≤ M := le_trans (Multiset.le_add_right _ _) enabled
    obtain ⟨-, frame, consumedSeparate, producedSeparate, decomposition, result⟩ :=
      (bagRule_iff_fires (S.consume i) (S.produce i) M (S.fire M i)).mp
        ⟨M - S.consume i, (add_tsub_cancel_of_le contained).symm, add_comm _ _⟩
    exact ⟨guardIff.mpr enabled, frame, consumedSeparate, producedSeparate, decomposition, result⟩

/-- A resource that no instance of a list consumes is not consumed by the list. -/
theorem count_stepConsume_eq_zero (entries : List S.Entry) (resource : R)
    (unused : ∀ entry ∈ entries, (S.consume entry.2).count resource = 0) :
    (S.stepConsume (entries : List S.Entry)).count resource = 0 := by
  induction entries with
  | nil => simp [System.stepConsume]
  | cons entry rest ih =>
      have split : S.stepConsume (entry :: rest : List S.Entry) =
          S.consume entry.2 + S.stepConsume rest := by
        simp [System.stepConsume]
      rw [split, Multiset.count_add, unused entry List.mem_cons_self,
        ih fun other member => unused other (List.mem_cons_of_mem entry member)]

/-- A resource that no instance of a list reads is not read by the list. -/
theorem count_stepRead_eq_zero (entries : List S.Entry) (resource : R)
    (unread : ∀ entry ∈ entries, (S.read entry.2).count resource = 0) :
    (S.stepRead (entries : List S.Entry)).count resource = 0 := by
  induction entries with
  | nil => simp [System.stepRead]
  | cons entry rest ih =>
      have split : S.stepRead (entry :: rest : List S.Entry) =
          S.read entry.2 ∪ S.stepRead rest := by
        simp [System.stepRead]
      rw [split, Multiset.count_union, unread entry List.mem_cons_self,
        ih fun other member => unread other (List.mem_cons_of_mem entry member)]
      rfl

/-- **A wave by footprints is a wave by counts.**  Instances that are enabled one
by one at a bag, and independent in pairs as local rules, are enabled together
as a step: their consumptions, added, fit beside the largest of their reads. -/
theorem stepEnables_of_independent (M : Multiset R) (entries : List S.Entry)
    (enabled : ∀ entry ∈ entries, S.Enables M entry.2)
    (independent : entries.Pairwise fun first second =>
      IndependentEffects (resourceRule S first.2).reads (resourceRule S first.2).writes
        (resourceRule S second.2).reads (resourceRule S second.2).writes) :
    S.StepEnables M (entries : List S.Entry) := by
  induction entries with
  | nil => simp [System.StepEnables, System.stepConsume, System.stepRead]
  | cons entry rest ih =>
      obtain ⟨headIndependent, restIndependent⟩ := List.pairwise_cons.mp independent
      have restEnabled : S.StepEnables M (rest : List S.Entry) :=
        ih (fun other member => enabled other (List.mem_cons_of_mem entry member)) restIndependent
      have headEnabled : S.consume entry.2 + S.read entry.2 ≤ M := enabled entry List.mem_cons_self
      have consumeSplit : S.stepConsume (entry :: rest : List S.Entry) =
          S.consume entry.2 + S.stepConsume rest := by
        simp [System.stepConsume]
      have readSplit : S.stepRead (entry :: rest : List S.Entry) =
          S.read entry.2 ∪ S.stepRead rest := by
        simp [System.stepRead]
      unfold System.StepEnables at restEnabled ⊢
      rw [consumeSplit, readSplit, Multiset.le_iff_count]
      intro resource
      have headFits := Multiset.le_iff_count.mp headEnabled resource
      have restFits := Multiset.le_iff_count.mp restEnabled resource
      simp only [Multiset.count_add, Multiset.count_union] at headFits restFits ⊢
      by_cases consumes : 0 < (S.consume entry.2).count resource
      · have written : resource ∈ (resourceRule S entry.2).writes :=
          Finset.mem_union_left _ (Multiset.mem_toFinset.mpr (Multiset.count_pos.mp consumes))
        have untouched : ∀ other ∈ rest,
            (S.consume other.2).count resource = 0 ∧ (S.read other.2).count resource = 0 := by
          intro other member
          have outside := Finset.disjoint_left.mp (headIndependent other member).1 written
          exact ⟨Multiset.count_eq_zero.mpr fun inConsume =>
              outside (Finset.mem_union_right _
                (Finset.mem_union_left _ (Multiset.mem_toFinset.mpr inConsume))),
            Multiset.count_eq_zero.mpr fun inRead =>
              outside (Finset.mem_union_left _ (Multiset.mem_toFinset.mpr inRead))⟩
        rw [count_stepConsume_eq_zero S rest resource fun other member =>
            (untouched other member).1,
          count_stepRead_eq_zero S rest resource fun other member => (untouched other member).2]
        omega
      · by_cases restConsumes : ∃ other ∈ rest, 0 < (S.consume other.2).count resource
        · obtain ⟨other, member, positive⟩ := restConsumes
          have written : resource ∈ (resourceRule S other.2).writes :=
            Finset.mem_union_left _ (Multiset.mem_toFinset.mpr (Multiset.count_pos.mp positive))
          have outside := Finset.disjoint_left.mp (headIndependent other member).2 written
          have noRead : (S.read entry.2).count resource = 0 :=
            Multiset.count_eq_zero.mpr fun inRead =>
              outside (Finset.mem_union_left _ (Multiset.mem_toFinset.mpr inRead))
          omega
        · have restNone : (S.stepConsume (rest : List S.Entry)).count resource = 0 :=
            count_stepConsume_eq_zero S rest resource fun other member => by
              have notPositive : ¬ 0 < (S.consume other.2).count resource :=
                fun positive => restConsumes ⟨other, member, positive⟩
              omega
          omega

/-- A list of candidates that is enabled together beside what is reserved is
selected whole. -/
theorem selectWaveAux_of_stepEnables (M : Multiset R) :
    ∀ (candidates reserved : List S.Entry),
      S.StepEnables M (reserved ++ candidates : List S.Entry) →
        S.selectWaveAux M reserved candidates = (candidates, [])
  | [], _, _ => rfl
  | entry :: rest, reserved, enabled => by
      have regroup : reserved ++ entry :: rest = (reserved ++ [entry]) ++ rest := by simp
      rw [regroup] at enabled
      have headEnabled : S.StepEnables M (reserved ++ [entry] : List S.Entry) :=
        S.stepEnables_of_le
          (Multiset.coe_le.mpr (List.sublist_append_left (reserved ++ [entry]) rest).subperm)
          enabled
      simp only [System.selectWaveAux, if_pos headEnabled]
      rw [selectWaveAux_of_stepEnables M rest (reserved ++ [entry]) enabled]

/-- **The selector takes a whole step**: candidates that are enabled together are
all selected and none is deferred. -/
theorem selectWave_of_stepEnables (M : Multiset R) (entries : List S.Entry)
    (enabled : S.StepEnables M (entries : List S.Entry)) :
    S.selectWave M entries = (entries, []) :=
  selectWaveAux_of_stepEnables S M entries [] (by simpa using enabled)

/-- **The wave of the footprints, fired by the resource selector.**  Instances
that are enabled one by one and independent in pairs as local rules fire in every
order to the one bag of the selected wave: this is
`System.selectWave_every_order` at a selection that kept them all. -/
theorem independent_entries_every_order {M : Multiset R} {entries order : List S.Entry}
    (enabled : ∀ entry ∈ entries, S.Enables M entry.2)
    (independent : entries.Pairwise fun first second =>
      IndependentEffects (resourceRule S first.2).reads (resourceRule S first.2).writes
        (resourceRule S second.2).reads (resourceRule S second.2).writes)
    (perm : entries.Perm order) :
    S.Fires order M (S.waveTarget M entries) := by
  have whole :=
    selectWave_of_stepEnables S M entries
      (stepEnables_of_independent S M entries enabled independent)
  have fired :=
    S.selectWave_every_order (M := M) (candidates := entries) (order := order)
      (by rw [whole]; exact perm)
  rwa [whole] at fired

/-! ## Controls -/

namespace ResourceWaveControls

open Mettapedia.GSLT.Causality.ResourceInteraction.WaveControls

/-- **Counts are finer than kinds.**  Two jobs that each take one of two tokens
are a step of the resource system; as local rules both write the kind `token`,
so they are not independent. -/
theorem two_copies_step_not_independent :
    packing.StepEnables WaveControls.twoTokens [job 1 1, job 2 1] ∧
      ¬ IndependentEffects (resourceRule packing (job 1 1).2).reads
        (resourceRule packing (job 1 1).2).writes (resourceRule packing (job 2 1).2).reads
        (resourceRule packing (job 2 1).2).writes := by
  constructor
  · decide +kernel
  · decide +kernel

/-- **A production does not disable a read of a resource system.**  With the fact
already present, its producer and its reader are a step; as local rules the
producer writes the kind the reader reads, so they are not independent. -/
theorem producer_and_reader_step_not_independent :
    generatedWork.StepEnables {.token, .gate, .fact} [producer, consumer] ∧
      ¬ IndependentEffects (resourceRule generatedWork producer.2).reads
        (resourceRule generatedWork producer.2).writes (resourceRule generatedWork consumer.2).reads
        (resourceRule generatedWork consumer.2).writes := by
  constructor
  · decide +kernel
  · decide +kernel

/-- **Positive**: two jobs with different answers and no token to take are
independent as local rules, and are a step. -/
theorem free_jobs_independent :
    IndependentEffects (resourceRule packing (job 1 0).2).reads
        (resourceRule packing (job 1 0).2).writes (resourceRule packing (job 2 0).2).reads
        (resourceRule packing (job 2 0).2).writes ∧
      packing.StepEnables 0 [job 1 0, job 2 0] := by
  constructor
  · decide +kernel
  · decide +kernel

end ResourceWaveControls

#print axioms resourceRule_fires_iff
#print axioms stepEnables_of_independent
#print axioms selectWave_of_stepEnables
#print axioms independent_entries_every_order
#print axioms ResourceWaveControls.two_copies_step_not_independent
#print axioms ResourceWaveControls.producer_and_reader_step_not_independent
#print axioms ResourceWaveControls.free_jobs_independent

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
