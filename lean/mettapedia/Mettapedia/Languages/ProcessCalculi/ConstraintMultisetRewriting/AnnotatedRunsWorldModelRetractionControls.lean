import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsWorldModelRetraction
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsNeighborhood

/-!
# The retracted sighting

A ledger holds four sightings of black birds: `s1`, `s2`, `s3` are ravens, `s4` is a crow. Three
claims rest on them: "ravens are black" on `{s1, s2, s3}`, "crows are black" on `{s4}`, and
"birds are black" on all four. The sighting `s4` is retracted.

* **Causal deletion is a firing**: the run of the sightings and the retraction of `s4` runs
  (`run_executable`). Afterwards the claims are `(3, 0)` on `{s1, s2, s3}`, `(0, 0)` on nothing, and
  `(3, 0)` on `{s1, s2, s3}` (`causal_rows`). It satisfies both laws
  (`causal_no_manufactured`, `causal_support_closed`).
* **Reset to a prior** puts `(1, 1)` with no support on every claim touching `s4`. It manufactures
  evidence (`reset_manufactures`), while every claim with evidence keeps a support avoiding `s4`
  (`reset_avoids_scope`); its prior is evidence without support (`reset_unsupported`).
* **Zeroing in scope** zeroes the claims supported only by `s4`. It manufactures no evidence
  (`zero_no_manufactured`), and the aggregate claim keeps standing on `s4`
  (`zero_not_support_closed`).
* Both policies are idempotent and change no claim outside the scope (`reset_idempotent`,
  `zero_idempotent`, `outside_unchanged`): the earlier interface admits all three.
* **Retraction removes evidence that runs keeping evidence would keep.** Read as provenance
  evidence over runs, there is evidence that the crow was sighted after the sightings
  (`crow_evidence_before`). Evidence is an invariant of the runs that keep evidence
  (`NeighborhoodRuns.ledgerEvidence_invariant`); the retraction is not such a run
  (`retract_not_keeper`), and after it the evidence is gone (`crow_evidence_after`).
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace WorldModelRuns

namespace RetractionControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (Run)
open MeTTaCalculus.OccurrenceCommits (regionOf)
open Mettapedia.PLN.WorldModel.EvidenceSpaces
open Mettapedia.PLN.WorldModel.EvidenceContracts

/-- Sightings: ravens `1`, `2`, `3` and the crow `4`, each with its own label. -/
def label : Nat → Term signature
  | 1 => .const 11
  | 2 => .const 12
  | 3 => .const 13
  | 4 => .const 24
  | _ => .const 2

/-- The evidence space: the four sightings. -/
def space : Term signature → Bool
  | .const 11 => true
  | .const 12 => true
  | .const 13 => true
  | .const 24 => true
  | _ => false

/-- Raven sightings. -/
def raven : Term signature → Bool
  | .const 11 => true
  | .const 12 => true
  | .const 13 => true
  | _ => false

/-- The crow sighting, the one withdrawn. -/
def crow : Term signature → Bool
  | .const 24 => true
  | _ => false

/-- Every sighting is of a black bird. -/
def isBlack : Term signature → Bool := fun _ => true

/-- The three claims. -/
inductive BirdClaim where
  | ravens
  | crows
  | birds

def claimOf : BirdClaim → Claim (Term signature)
  | .ravens => ⟨raven, isBlack⟩
  | .crows => ⟨crow, isBlack⟩
  | .birds => ⟨space, isBlack⟩

def empty : Configuration (Term signature) Nat := ⟨[], ∅⟩

/-- The four sightings. -/
def sightAll : Run :=
  ⟨⟨[], [], [], [], [.const 11, .const 12, .const 13, .const 24]⟩, [], ⟨[], [], [1, 2, 3, 4]⟩⟩

/-- **Causal deletion of `s4`**: the predicate query of the crow's space, and the take of what it
saw. -/
def retractCrow : Run := retractFiring label crow [4]

theorem sightAll_valid : sightAll.Valid A label empty := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨Subst.id signature, ?_⟩,
    by simp [sightAll]⟩, by simp [sightAll]⟩
  intro equation member
  simp [Selection.problem, Selection.equations, empty, sightAll] at member

abbrev sighted : Configuration (Term signature) Nat := sightAll.result label empty

theorem retractCrow_valid : retractCrow.Valid A label sighted := by
  rw [retractCrow, retractFiring_valid_iff]
  refine ⟨by decide, by decide, sightAll_valid.firing.consistent⟩

/-- **The run of the sightings and the retraction runs.** -/
theorem run_executable : Executable A label empty [sightAll, retractCrow] :=
  ⟨sightAll_valid, retractCrow_valid, retractCrow_valid.firing.consistent⟩

abbrev retracted : Configuration (Term signature) Nat := retractCrow.result label sighted

theorem sighted_ledger : ledger label space sighted = {1, 2, 3, 4} := by decide

theorem retracted_ledger : ledger label space retracted = {1, 2, 3} := by decide

/-- A claim table: the evidence and the support of each claim. -/
abbrev Table := BirdClaim → Evidence ℕ × Finset Nat

/-- The table of a ledger. -/
def tableOf (L : Finset Nat) : Table := fun q =>
  (claimEvidence label id (claimOf q) L, support label id (claimOf q) L)

/-- The table before the retraction. -/
abbrev before : Table := tableOf (ledger label space sighted)

/-- The table of causal deletion: the table of the ledger after the retraction firing. -/
abbrev causal : Table := tableOf (ledger label space retracted)

/-- The scope: the withdrawn sighting. -/
def scope : Finset Nat := {4}

/-- **Reset to a prior**: every claim touching the scope gets `(1, 1)` and no support. -/
def reset (t : Table) : Table := fun q => if ((t q).2 ∩ scope).Nonempty then (⟨1, 1⟩, ∅) else t q

theorem reset_apply (t : Table) (q : BirdClaim) :
    reset t q = if ((t q).2 ∩ scope).Nonempty then (⟨1, 1⟩, ∅) else t q := rfl

/-- **Zeroing in scope**: every claim supported only inside the scope gets `(0, 0)`. -/
def zero (t : Table) : Table := fun q => if (t q).2 ⊆ scope then (0, ∅) else t q

theorem zero_apply (t : Table) (q : BirdClaim) :
    zero t q = if (t q).2 ⊆ scope then (0, ∅) else t q := rfl

/-- No manufactured evidence, between two tables. -/
def NoManufactured (old new : Table) : Prop := ∀ q, (new q).1 ≤ (old q).1

/-- Support closure, between two tables: evidence has support, supports shrink, and avoid the
scope. -/
def SupportClosed (old new : Table) : Prop :=
  ∀ q, ((new q).1 ≠ 0 → (new q).2.Nonempty) ∧ (new q).2 ⊆ (old q).2 ∧ Disjoint (new q).2 scope

theorem before_rows :
    before .ravens = (⟨3, 0⟩, {1, 2, 3}) ∧ before .crows = (⟨1, 0⟩, {4}) ∧
      before .birds = (⟨4, 0⟩, {1, 2, 3, 4}) := by
  simp only [before, tableOf, sighted_ledger]
  refine ⟨Prod.ext ?_ (by decide), Prod.ext ?_ (by decide), Prod.ext ?_ (by decide)⟩ <;>
    (ext <;> decide)

/-- **The rows of causal deletion.** -/
theorem causal_rows :
    causal .ravens = (⟨3, 0⟩, {1, 2, 3}) ∧ causal .crows = (0, ∅) ∧
      causal .birds = (⟨3, 0⟩, {1, 2, 3}) := by
  simp only [causal, tableOf, retracted_ledger]
  refine ⟨Prod.ext ?_ (by decide), Prod.ext ?_ (by decide), Prod.ext ?_ (by decide)⟩ <;>
    (ext <;> decide)

/-- **Causal deletion manufactures no evidence**, by the law of the retraction firing. -/
theorem causal_no_manufactured : NoManufactured before causal := fun q =>
  retract_no_manufactured A label space id retractCrow_valid (claimOf q)

/-- **Causal deletion is support closed**, by the laws of the retraction firing. -/
theorem causal_support_closed : SupportClosed before causal := by
  intro q
  refine ⟨fun nonzero =>
      support_nonempty_of_ne_zero label id (claimOf q) (L := ledger label space retracted) nonzero,
    retract_support_subset A label space id retractCrow_valid (claimOf q), ?_⟩
  rw [Finset.disjoint_left]
  intro o member inScope
  have avoids := retract_support_avoids A label space id retractCrow_valid (claimOf q) o member
  rw [scope, Finset.mem_singleton] at inScope
  subst inScope
  revert avoids
  decide

theorem reset_rows :
    reset before .ravens = (⟨3, 0⟩, {1, 2, 3}) ∧ reset before .crows = (⟨1, 1⟩, ∅) ∧
      reset before .birds = (⟨1, 1⟩, ∅) := by
  obtain ⟨r, c, b⟩ := before_rows
  refine ⟨?_, ?_, ?_⟩
  · simp only [reset, r]
    rw [if_neg (by decide)]
  · simp only [reset, c]
    rw [if_pos (by decide)]
  · simp only [reset, b]
    rw [if_pos (by decide)]

theorem zero_rows :
    zero before .ravens = (⟨3, 0⟩, {1, 2, 3}) ∧ zero before .crows = (0, ∅) ∧
      zero before .birds = (⟨4, 0⟩, {1, 2, 3, 4}) := by
  obtain ⟨r, c, b⟩ := before_rows
  refine ⟨?_, ?_, ?_⟩
  · simp only [zero, r]
    rw [if_neg (by decide)]
  · simp only [zero, c]
    rw [if_pos (by decide)]
  · simp only [zero, b]
    rw [if_neg (by decide)]

/-- **Reset to a prior manufactures evidence**: the crow claim gains a negative count. -/
theorem reset_manufactures : ¬ NoManufactured before (reset before) := by
  intro law
  have crows := law .crows
  rw [reset_rows.2.1, before_rows.2.1] at crows
  exact absurd crows.2 (by decide)

/-- Every claim of the reset table with evidence keeps a support avoiding the scope. -/
theorem reset_avoids_scope :
    ∀ q, ((reset before) q).1 ≠ 0 → Disjoint ((reset before) q).2 scope := by
  intro q _
  cases q
  · rw [reset_rows.1]; decide
  · rw [reset_rows.2.1]; decide
  · rw [reset_rows.2.2]; decide

/-- **The prior is evidence without support.** -/
theorem reset_unsupported : ¬ SupportClosed before (reset before) := by
  intro law
  have crows := (law .crows).1
  rw [reset_rows.2.1] at crows
  have nonempty := crows (fun same => absurd (congrArg Evidence.pos same) (by decide))
  exact absurd nonempty (by decide)

/-- **Zeroing in scope manufactures no evidence.** -/
theorem zero_no_manufactured : NoManufactured before (zero before) := by
  intro q
  cases q
  · rw [zero_rows.1, before_rows.1]
  · rw [zero_rows.2.1, before_rows.2.1]
    exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  · rw [zero_rows.2.2, before_rows.2.2]

/-- **Zeroing in scope is not support closed**: the aggregate claim keeps standing on `s4`. -/
theorem zero_not_support_closed : ¬ SupportClosed before (zero before) := by
  intro law
  have birds := (law .birds).2.2
  rw [zero_rows.2.2] at birds
  exact absurd birds (by decide)

/-- Reset is idempotent on this table. -/
theorem reset_idempotent : ∀ q, reset (reset before) q = reset before q := by
  intro q
  rw [reset_apply (reset before) q]
  cases q
  · rw [reset_rows.1]
    exact if_neg (by decide)
  · rw [reset_rows.2.1]
    exact if_neg (by decide)
  · rw [reset_rows.2.2]
    exact if_neg (by decide)

/-- Zeroing is idempotent on this table. -/
theorem zero_idempotent : ∀ q, zero (zero before) q = zero before q := by
  intro q
  rw [zero_apply (zero before) q]
  cases q
  · rw [zero_rows.1]
    exact if_neg (by decide)
  · rw [zero_rows.2.1]
    exact if_pos (by decide)
  · rw [zero_rows.2.2]
    exact if_neg (by decide)

/-- **Outside the scope nothing changes**, under all three policies: the ravens claim. -/
theorem outside_unchanged :
    reset before .ravens = before .ravens ∧ zero before .ravens = before .ravens ∧
      causal .ravens = before .ravens := by
  rw [reset_rows.1, zero_rows.1, causal_rows.1, before_rows.1]
  exact ⟨rfl, rfl, rfl⟩

/-! ## Retraction removes evidence -/

open Mettapedia.GSLT.Causality.OccurrenceHistory (OccurrencePath)

abbrev root : Runs A label := runObject A label empty

/-- Provenance evidence over the runs from the empty configuration. -/
abbrev provenance : NeighborhoodRuns.EvidenceModel root :=
  NeighborhoodRuns.ledgerEvidenceModel A label space empty (NeighborhoodRuns.madeIn A label empty)

/-- One sighting alone. -/
def sightOne (i : Nat) : Run := ⟨⟨[], [], [], [], [label i]⟩, [], ⟨[], [], [i]⟩⟩

theorem sightOne_valid (i : Nat) : (sightOne i).Valid A label empty := by
  refine ⟨⟨by simp [sightOne], by simp [sightOne], rfl, rfl, rfl, ?_, ⟨Subst.id signature, ?_⟩,
    by simp [sightOne]⟩, by simp [sightOne]⟩
  · exact ⟨by simp [Selection.commit, sightOne], by simp [Selection.commit, sightOne],
      by simp [Selection.commit, sightOne], by simp [Selection.commit, sightOne, empty],
      by simp [Selection.commit]⟩
  · intro equation member
    simp [Selection.problem, Selection.equations, empty, sightOne] at member

/-- **After the sightings there is evidence that the crow was sighted.** -/
theorem crow_evidence_before (p : root ⟶ classOf A label sighted) :
    p ∈ NeighborhoodRuns.evidenceFor provenance (NeighborhoodRuns.madeIn A label empty 4)
      (classOf A label sighted) := by
  refine ⟨NeighborhoodRuns.madeIn A label empty 4, ⟨4, ?_, rfl⟩, le_rfl⟩
  rw [NeighborhoodRuns.ledgerClass_classOf, sighted_ledger]
  exact Finset.mem_coe.mpr (by decide)

/-- **The retraction does not keep evidence.** -/
theorem retract_not_keeper : retractCrow ∉ NeighborhoodRuns.keepers label space := by
  intro keeps
  have := keeps 4 (List.mem_singleton_self 4)
  revert this
  decide

/-- **After the retraction there is no evidence that the crow was sighted**: each remaining piece
is the provenance of a raven sighting, and that sighting alone does not make the crow's. -/
theorem crow_evidence_after (q : root ⟶ classOf A label retracted) :
    q ∉ NeighborhoodRuns.evidenceFor provenance (NeighborhoodRuns.madeIn A label empty 4)
      (classOf A label retracted) := by
  rintro ⟨X, ⟨o, inLedger, rfl⟩, below⟩
  rw [NeighborhoodRuns.ledgerClass_classOf, retracted_ledger] at inLedger
  obtain ⟨single, singleSites⟩ := exists_path A label empty [sightOne o]
    ⟨sightOne_valid o, (sightOne_valid o).firing.consistent⟩ _ rfl
  have made : single ∈ NeighborhoodRuns.madeIn A label empty o _ :=
    ⟨sightOne o, by rw [singleSites]; exact List.mem_singleton_self _, List.mem_singleton_self o⟩
  obtain ⟨f, inSites, four⟩ := below _ made
  rw [singleSites] at inSites
  obtain rfl : f = sightOne o := List.mem_singleton.mp inSites
  have same : 4 = o := List.mem_singleton.mp four
  subst same
  exact absurd (Finset.mem_coe.mp inLedger) (by decide)

end RetractionControls

end WorldModelRuns

open WorldModelRuns

#print axioms RetractionControls.run_executable
#print axioms RetractionControls.before_rows
#print axioms RetractionControls.causal_rows
#print axioms RetractionControls.causal_no_manufactured
#print axioms RetractionControls.causal_support_closed
#print axioms RetractionControls.reset_manufactures
#print axioms RetractionControls.reset_avoids_scope
#print axioms RetractionControls.reset_unsupported
#print axioms RetractionControls.zero_no_manufactured
#print axioms RetractionControls.zero_not_support_closed
#print axioms RetractionControls.reset_idempotent
#print axioms RetractionControls.zero_idempotent
#print axioms RetractionControls.outside_unchanged
#print axioms RetractionControls.crow_evidence_before
#print axioms RetractionControls.retract_not_keeper
#print axioms RetractionControls.crow_evidence_after

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
