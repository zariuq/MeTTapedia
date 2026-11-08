import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PredicateQueryAdmission

/-!
# Finite predicate tables retain candidate-dependent matching

A table records row data at finitely many occurrence identities. Its
predicate query validates each recorded row's matching behavior at the
current candidate and rules out matches outside the table. The matching
subset may vary with the candidate, although the table's support is fixed.

Support is constructed from the finite inventory across the declared
admissible candidates. This semantic construction supplies no algorithm
for deciding arbitrary matching or completing an unfinished search.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SymbolicPredicateTable

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uL uA uO

structure Table (Label : Type uL) (O : Type uO) where
  seen : Finset O
  payload : (occurrence : O) → occurrence ∈ seen → Label

variable {Label : Type uL} {A : Type uA} {O : Type uO} [DecidableEq O]
    (predicate : A → O → Label → Bool)

def Table.query (table : Table Label O) : PredicateQueryAdmission.Query (O × Label) A O :=
  ⟨(fun candidate label =>
    if member : label.1 ∈ table.seen then
      predicate candidate label.1 label.2 == predicate candidate label.1 (table.payload label.1 member)
    else predicate candidate label.1 label.2), table.seen⟩

def Table.matching (table : Table Label O) (candidate : A) : Finset O :=
  (table.seen.attach.filter fun occurrence =>
    predicate candidate occurrence.val (table.payload occurrence.val occurrence.property) = true).image Subtype.val

theorem Table.mem_matching (table : Table Label O) (candidate : A) (occurrence : O) :
    occurrence ∈ table.matching predicate candidate ↔
      ∃ member : occurrence ∈ table.seen, predicate candidate occurrence (table.payload occurrence member) = true := by
  simp only [Table.matching, Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨⟨original, member⟩, matched, same⟩
    change original = occurrence at same
    subst original
    exact ⟨member, matched⟩
  · rintro ⟨member, matched⟩
    exact ⟨⟨occurrence, member⟩, matched, rfl⟩

/-- The observation validates the recorded row against the actual supplied
label. It does not merely test the table against itself. -/
theorem Table.observed_member (table : Table Label O) (candidate : A) (label : O → Label) (world : Finset O)
    (observed : ((table.query predicate).atSolution candidate).Holds
      (fun occurrence => (occurrence, label occurrence)) world)
    (occurrence : O) (member : occurrence ∈ table.seen) :
    occurrence ∈ world ∧ predicate candidate occurrence (label occurrence) = predicate candidate occurrence (table.payload occurrence member) := by
  change regionOf (fun occurrence => (occurrence, label occurrence)) world
    ((table.query predicate).region candidate) = table.seen at observed
  have inside : occurrence ∈ regionOf (fun occurrence => (occurrence, label occurrence)) world
      ((table.query predicate).region candidate) := by
    rw [observed]
    exact member
  obtain ⟨present, compared⟩ := mem_regionOf.mp inside
  refine ⟨present, ?_⟩
  simpa only [Table.query, dif_pos member, beq_iff_eq] using compared

/-- A successful table read reconstructs the entire actual matching region,
including when different candidates have different matching subsets. -/
theorem Table.actual_region (table : Table Label O) (candidate : A) (label : O → Label) (world : Finset O)
    (observed : ((table.query predicate).atSolution candidate).Holds
      (fun occurrence => (occurrence, label occurrence)) world) :
    regionOf (fun occurrence => (occurrence, label occurrence)) world (fun value => predicate candidate value.1 value.2) = table.matching predicate candidate := by
  change regionOf (fun occurrence => (occurrence, label occurrence)) world
    ((table.query predicate).region candidate) = table.seen at observed
  ext occurrence
  constructor
  · intro inside
    obtain ⟨present, matched⟩ := mem_regionOf.mp inside
    by_cases member : occurrence ∈ table.seen
    · apply (table.mem_matching predicate candidate occurrence).mpr
      exact ⟨member, ((table.observed_member predicate candidate label world observed occurrence member).2).symm.trans matched⟩
    · have selected : occurrence ∈ regionOf (fun occurrence => (occurrence, label occurrence)) world
          ((table.query predicate).region candidate) := by
        apply mem_regionOf.mpr
        refine ⟨present, ?_⟩
        simpa only [Table.query, dif_neg member] using matched
      rw [observed] at selected
      exact False.elim (member selected)
  · intro recorded
    obtain ⟨member, matched⟩ := (table.mem_matching predicate candidate occurrence).mp recorded
    obtain ⟨present, agrees⟩ := table.observed_member predicate candidate label world observed occurrence member
    exact mem_regionOf.mpr ⟨present, agrees.trans matched⟩

theorem Table.actual_count (table : Table Label O) (candidate : A) (label : O → Label) (world : Finset O)
    (observed : ((table.query predicate).atSolution candidate).Holds
      (fun occurrence => (occurrence, label occurrence)) world) :
    (regionOf (fun occurrence => (occurrence, label occurrence)) world (fun value => predicate candidate value.1 value.2)).card = (table.matching predicate candidate).card :=
  congrArg Finset.card (table.actual_region predicate candidate label world observed)

noncomputable def support (admissible : A → Prop) (label : O → Label) (world : Finset O) : Finset O := by
  classical
  exact world.filter fun occurrence => ∃ candidate, admissible candidate ∧ predicate candidate occurrence (label occurrence) = true

noncomputable def snapshot (admissible : A → Prop) (label : O → Label) (world : Finset O) : Table Label O :=
  ⟨support predicate admissible label world, fun occurrence _member => label occurrence⟩

theorem snapshot_admitted (admissible : A → Prop) (label : O → Label) (world : Finset O)
    (candidate : A) (allowed : admissible candidate) :
    (((snapshot predicate admissible label world).query predicate).atSolution candidate).Holds
      (fun occurrence => (occurrence, label occurrence)) world := by
  classical
  change regionOf (fun occurrence => (occurrence, label occurrence)) world
    (((snapshot predicate admissible label world).query predicate).region candidate) = support predicate admissible label world
  ext occurrence
  constructor
  · intro selected
    obtain ⟨present, compared⟩ := mem_regionOf.mp selected
    by_cases member : occurrence ∈ support predicate admissible label world
    · exact member
    · have matched : predicate candidate occurrence (label occurrence) = true := by
        dsimp only [Table.query, snapshot] at compared
        split at compared
        · exact False.elim (member ‹occurrence ∈ support predicate admissible label world›)
        · exact compared
      exact False.elim (member (Finset.mem_filter.mpr ⟨present, candidate, allowed, matched⟩))
  · intro member
    have present := (Finset.mem_filter.mp member).1
    apply mem_regionOf.mpr
    refine ⟨present, ?_⟩
    simp only [Table.query, snapshot, dif_pos member, beq_self_eq_true]

/-- Every admissible candidate is reconstructed from the same conditional
table. No principal candidate or fixed matching subset is assumed. -/
theorem snapshot_matching (admissible : A → Prop) (label : O → Label) (world : Finset O)
    (candidate : A) (allowed : admissible candidate) :
    (snapshot predicate admissible label world).matching predicate candidate = regionOf (fun occurrence => (occurrence, label occurrence)) world (fun value => predicate candidate value.1 value.2) :=
  ((snapshot predicate admissible label world).actual_region predicate candidate label world
    (snapshot_admitted predicate admissible label world candidate allowed)).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SymbolicPredicateTable
