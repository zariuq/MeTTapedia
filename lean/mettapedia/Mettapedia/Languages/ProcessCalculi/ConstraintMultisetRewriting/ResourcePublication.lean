import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourceOccupation

/-!
# Preparing and publishing complete physical-region resource replacements

Each region is the fibre of the actual physical location map. Its private
replacement is computed by the existing occurrence commit, restricted to
that region. Every retained occurrence in the region is included. The
occupation operator verifies this private computation, and installing all
touched regions is proved to compute the original selected successor.

These are resource-state laws. Source equation consistency, guard readiness,
formation and authority are not consequences of successfully moving regions.
The sequential installation model assumes other writes are excluded while
the prepared replacements are published; it proves no native synchronization
or ownership implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourcePublication

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {O R T S : Type*} [DecidableEq O] [DecidableEq R]

/-- Restriction uses the existing occurrence-region observer. -/
def slice (location : O → R) (region : R) (world : Finset O) : Finset O :=
  regionOf location world fun actual => decide (actual = region)

omit [DecidableEq O] in
@[simp] theorem mem_slice {location : O → R} {region : R} {world : Finset O} {o : O} :
    o ∈ slice location region world ↔ o ∈ world ∧ location o = region := by
  simp [slice, regionOf]

omit [DecidableEq O] in
theorem slices_disjoint (location : O → R) {one two : R} (different : one ≠ two)
    (world : Finset O) : Disjoint (slice location one world) (slice location two world) := by
  apply Finset.disjoint_left.mpr
  intro o first second
  exact different ((mem_slice.mp first).2.symm.trans (mem_slice.mp second).2)

/-- All ports resolved to the same physical region contribute to one local
selection, regardless of which handle originally named that region. -/
def localSelection (location : O → R) (region : R) (picked : Selection O) : Selection O where
  taken := picked.taken.filter fun o => decide (location o = region)
  read := picked.read.filter fun o => decide (location o = region)
  made := picked.made.filter fun o => decide (location o = region)

/-- The complete private replacement includes the original in-region frame. -/
def replacement (location : O → R) (picked : Selection O) (before : Finset O)
    (region : R) : Finset O :=
  fire (slice location region before) ((localSelection location region picked).commit (T := T))

/-- Preparation uses the existing take/read/make occupation operator. -/
def prepareRegion (location : O → R) (picked : Selection O) (before : Finset O)
    (region : R) : Option (Finset O) :=
  let selected := localSelection location region picked
  ResourceOccupation.commit selected.taken selected.read selected.made (slice location region before)

theorem local_enabled (label : O → T) (location : O → R) (region : R)
    (picked : Selection O) (before : Finset O)
    (enabled : Enabled label before picked.commit) :
    Enabled label (slice location region before) (localSelection location region picked).commit := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro o taken
    have ports : o ∈ picked.taken ∧ location o = region := by
      simpa [Selection.commit, localSelection] using taken
    exact mem_slice.mpr ⟨enabled.taken_subset (by simpa [Selection.commit] using ports.1), ports.2⟩
  · intro o read
    have ports : o ∈ picked.read ∧ location o = region := by
      simpa [Selection.commit, localSelection] using read
    exact mem_slice.mpr ⟨enabled.kept_subset (by simpa [Selection.commit] using ports.1), ports.2⟩
  · apply Finset.disjoint_left.mpr
    intro o taken read
    have takes : o ∈ picked.taken ∧ location o = region := by
      simpa [Selection.commit, localSelection] using taken
    have reads : o ∈ picked.read ∧ location o = region := by
      simpa [Selection.commit, localSelection] using read
    exact Finset.disjoint_left.mp enabled.apart
      (by simpa [Selection.commit] using takes.1) (by simpa [Selection.commit] using reads.1)
  · apply Finset.disjoint_left.mpr
    intro o made old
    have ports : o ∈ picked.made ∧ location o = region := by
      simpa [Selection.commit, localSelection] using made
    exact Finset.disjoint_left.mp enabled.fresh
      (by simpa [Selection.commit] using ports.1) (mem_slice.mp old).1
  · intro query member
    cases member

theorem prepareRegion_eq_replacement (label : O → T) (location : O → R)
    (region : R) (picked : Selection O) (before : Finset O)
    (distinctTakes : picked.taken.Nodup) (distinctMade : picked.made.Nodup)
    (enabled : Enabled label before picked.commit) :
    prepareRegion location picked before region = some (replacement (T := T) location picked before region) := by
  apply ResourceOccupation.commit_eq_fire label
  · exact distinctTakes.filter _
  · exact distinctMade.filter _
  · exact local_enabled label location region picked before enabled

/-- The independent local computation is exactly the global successor's
physical-region restriction. No equation-store interpretation is erased. -/
theorem replacement_eq_source_slice (location : O → R) (region : R)
    (picked : Selection O) (before : Finset O) :
    replacement (T := T) location picked before region =
      slice location region (fire before (picked.commit (T := T))) := by
  ext o
  simp [replacement, localSelection, Selection.commit, fire]
  tauto

/-- Installing one complete private region leaves all other physical
regions where they are. -/
def install (location : O → R) (region : R) (prepared current : Finset O) : Finset O :=
  (current \ slice location region current) ∪ prepared

theorem mem_install_slice (location : O → R) (region : R) (target current : Finset O)
    (o : O) :
    o ∈ install location region (slice location region target) current ↔
      if location o = region then o ∈ target else o ∈ current := by
  by_cases here : location o = region <;> simp [install, here]

/-- The publication loop moves complete prepared regions one by one. -/
def publish (location : O → R) (prepared : R → Finset O) : List R → Finset O → Finset O
  | [], current => current
  | region :: later, current =>
      publish location prepared later (install location region (prepared region) current)

theorem publish_append (location : O → R) (prepared : R → Finset O)
    (first later : List R) (current : Finset O) :
    publish location prepared (first ++ later) current =
      publish location prepared later (publish location prepared first current) := by
  induction first generalizing current with
  | nil => rfl
  | cons region rest ih => exact ih _

/-- Each completed physical region has its final state; all other regions
retain the state before publication. -/
theorem publication_membership (location : O → R) (prepared : R → Finset O)
    (regions : List R) (target current : Finset O)
    (ready : ∀ region ∈ regions, prepared region = slice location region target) (o : O) :
    o ∈ publish location prepared regions current ↔
      if location o ∈ regions then o ∈ target else o ∈ current := by
  induction regions generalizing current with
  | nil => simp [publish]
  | cons region later ih =>
      rw [publish, ih _ (fun r member => ready r (List.mem_cons_of_mem _ member))]
      by_cases inLater : location o ∈ later
      · simp [inLater]
      · rw [if_neg inLater, ready region List.mem_cons_self, mem_install_slice]
        simp [inLater]

theorem selected_publication_membership (location : O → R) (picked : Selection O)
    (before : Finset O) (regions : List R) (o : O) :
    o ∈ publish location (replacement (T := T) location picked before) regions before ↔
      if location o ∈ regions then o ∈ fire before (picked.commit (T := T)) else o ∈ before :=
  publication_membership location _ regions _ before
    (fun region _ => replacement_eq_source_slice location region picked before) o

/-- Resolve aliases first, then schedule each physical region at most once. -/
def destinations {Handle : Type*} (resolve : Handle → R) (handles : List Handle) : List R :=
  (handles.map resolve).dedup

@[simp] theorem mem_destinations {Handle : Type*} (resolve : Handle → R)
    (handles : List Handle) (region : R) :
    region ∈ destinations resolve handles ↔ ∃ handle ∈ handles, resolve handle = region := by
  simp [destinations]

theorem destinations_nodup {Handle : Type*} (resolve : Handle → R) (handles : List Handle) :
    (destinations resolve handles).Nodup := List.nodup_dedup _

theorem aliases_share_destination {Handle : Type*} (resolve : Handle → R)
    (one two : Handle) (same : resolve one = resolve two) :
    destinations resolve [one, two] = [resolve one] := by simp [destinations, same]

theorem publish_all_eq_source (location : O → R) (picked : Selection O)
    (before : Finset O) (regions : List R)
    (covers : ∀ o ∈ picked.taken ++ picked.made, location o ∈ regions) :
    publish location (replacement (T := T) location picked before) regions before =
      fire before (picked.commit (T := T)) := by
  ext o
  rw [selected_publication_membership]
  by_cases covered : location o ∈ regions
  · simp [covered]
  · have notTaken : o ∉ picked.taken := fun member => covered (covers o (List.mem_append_left _ member))
    have notMade : o ∉ picked.made := fun member => covered (covers o (List.mem_append_right _ member))
    simp [covered, fire, Selection.commit, notTaken, notMade]

/-- Completion computes the actual selected successor, with source validity
checked separately from private resource preparation and publication. -/
theorem valid_publication_result (A : SubstitutionAction T S) (label : O → T)
    (location : O → R) (picked : Selection O) (rule : RuleInstance T)
    (before : Configuration T O) (valid : picked.Valid A label rule before) :
    (∀ region, prepareRegion location picked before.present region =
      some (replacement (T := T) location picked before.present region)) ∧
    publish location (replacement (T := T) location picked before.present)
      (destinations location (picked.taken ++ picked.made)) before.present =
        (picked.result label rule before).present := by
  refine ⟨fun region => prepareRegion_eq_replacement label location region picked before.present
    valid.take_distinct valid.output_distinct valid.occurrences, ?_⟩
  apply publish_all_eq_source
  intro o member
  exact (mem_destinations _ _ _).mpr ⟨o, member, rfl⟩

/-- Every region prefix preserves a retained read occurrence, including
reads in a region that also consumes or creates other rows. -/
theorem selected_read_survives_prefix (A : SubstitutionAction T S) (label : O → T)
    (location : O → R) (picked : Selection O) (rule : RuleInstance T)
    (before : Configuration T O) (valid : picked.Valid A label rule before)
    (regions : List R) {o : O} (read : o ∈ picked.read) :
    o ∈ publish location (replacement (T := T) location picked before.present) regions before.present := by
  rw [selected_publication_membership]
  have old := valid.occurrences.kept_subset (by simpa [Selection.commit] using read)
  have kept := valid.kept_survive read
  split
  · exact kept
  · exact old

theorem unwritten_membership_preserved (location : O → R) (picked : Selection O)
    (before : Finset O) (regions : List R) {o : O}
    (notTaken : o ∉ picked.taken) (notMade : o ∉ picked.made) :
    o ∈ publish location (replacement (T := T) location picked before) regions before ↔ o ∈ before := by
  rw [selected_publication_membership]
  by_cases moved : location o ∈ regions <;>
    simp [moved, fire, Selection.commit, notTaken, notMade]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourcePublication
