import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsAmplitudeMeasurement

/-!
# Gathering a branch collection into a region: where the branch level meets the cut level

R27's collection over the causal histories of a region gives a bag of path amplitudes with a
status (`amplitudeCollection`). The waveform guards of `AnnotatedRunsAmplitudeMeasurement` read the
rows of a region at one cut. A gather firing joins the two: it publishes the bag as rows.

* `gatherFiring pathRow paths rows` takes and reads nothing, has no guards and no predicate
  queries, and makes one row per path, labelled `pathRow z`. Where the region is empty, and every
  `pathRow z` lies in the region and carries `z` (`Encodes`), the region after the gather holds
  exactly the gathered paths (`gather_regionPaths`).
* **Gathering a complete collection makes the verdict at the cut the verdict over the branches**
  (`gather_certifies`): after the gather, the region cancels exactly when the collection certifies a
  cancellation, it reinforces exactly when the collection certifies a reinforcement, and its
  coherent amplitude is `Z_Q`.
* **The cancellation guard after the gather** fires exactly when the collection certifies the
  cancellation (`gather_then_guard_iff`).
* **Only complete collections are gathered** (`gatherable`, `gatherable_amplitudeCollection`): an
  incomplete collection has no gather, so a guard downstream never reads a partial bag as the
  regional amplitude.
* **The status travels with the rows** (`statusGatherFiring`, `certifiedCancellationFiring`): a
  gather may also make a status row, marked complete or incomplete by two terms that no substitution
  identifies. The certified guard reads that row with the complete mark as its pattern, so where
  the row is marked incomplete it is refused at every cut, whatever the gathered paths
  (`certified_refused_of_incomplete`, `statusGather_incomplete_refused`). After a status gather of
  a complete collection it fires exactly when the collection certifies the cancellation
  (`statusGather_complete_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace AmplitudeRuns

open Mettapedia.Algebra.RationalComplexAmplitude (Amplitude born)
open MeTTaCalculus.OccurrenceCommits (regionOf mem_regionOf fire mem_fire)
open AnnotatedRunBranchCollection (Closed Collection)
open WorldModelRuns (GuardBits)

universe uT uS uO

/-! ## Only complete collections are gathered -/

/-- **What may be gathered from a collection**: its bag when complete, nothing otherwise. -/
def gatherable : Collection Amplitude → Option (Multiset Amplitude)
  | .complete bag => some bag
  | .incomplete _ => none

theorem gatherable_eq_some_iff (collection : Collection Amplitude) (bag : Multiset Amplitude) :
    gatherable collection = some bag ↔ collection = .complete bag := by
  cases collection with
  | complete found =>
      simp only [gatherable, Option.some.injEq]
      exact ⟨fun same => same ▸ rfl, fun same => by cases same; rfl⟩
  | incomplete found =>
      simp only [gatherable, reduceCtorEq]

section Collections

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T) (amp : Firing T S O → Amplitude)

/-- **A region's collection is gathered only at a closed frontier**, and then its bag is the paths
of every causal history ending in the region. -/
theorem gatherable_amplitudeCollection {catalogue : List (Firing T S O)} {budget : ℕ}
    {root : Configuration T O} {Q : ConfigurationClass A O → Prop} (bag : Multiset Amplitude) :
    gatherable (amplitudeCollection A label amp catalogue budget root Q) = some bag ↔
      Closed A label catalogue budget root ∧
        bag = branchAmplitudes A label amp catalogue budget root Q := by
  rw [gatherable_eq_some_iff, amplitudeCollection_eq_complete_iff]

end Collections

/-! ## The gather firing -/

section Gather

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T) (wave : T → Amplitude)

omit [DecidableEq O] in
/-- **The gather firing**: one row per path, labelled `pathRow z`; it takes and reads nothing and
has no guards and no predicate queries. -/
def gatherFiring (pathRow : Amplitude → T) (paths : List Amplitude) (rows : List O) :
    Firing T S O :=
  ⟨⟨[], [], [], [], paths.map pathRow⟩, [], ⟨[], [], rows⟩⟩

omit [DecidableEq O] in
/-- Every row of a path lies in the region and carries the path. -/
def Encodes (region : T → Bool) (pathRow : Amplitude → T) (paths : List Amplitude) : Prop :=
  ∀ z ∈ paths, region (pathRow z) = true ∧ wave (pathRow z) = z

variable {region : T → Bool} {pathRow : Amplitude → T} {paths : List Amplitude} {rows : List O}

/-- **After a gather into an empty region, the region holds exactly the gathered paths.** -/
theorem gather_regionPaths {C : Configuration T O}
    (valid : (gatherFiring pathRow paths rows : Firing T S O).Valid A label C)
    (empty : regionOf label C.present region = ∅) (encodes : Encodes wave region pathRow paths) :
    regionPaths label wave region
        ((gatherFiring pathRow paths rows : Firing T S O).result label C) =
      (paths : Multiset Amplitude) := by
  have outputs : rows.map label = paths.map pathRow := valid.firing.outputs
  have distinct : rows.Nodup := valid.firing.output_distinct
  have rowsIn : ∀ o ∈ rows, region (label o) = true := by
    intro o member
    have mapped : label o ∈ paths.map pathRow := outputs ▸ List.mem_map_of_mem member
    obtain ⟨z, inPaths, same⟩ := List.mem_map.mp mapped
    rw [← same]
    exact (encodes z inPaths).1
  have regionAfter : regionOf label
      ((gatherFiring pathRow paths rows : Firing T S O).result label C).present region =
        rows.toFinset := by
    change regionOf label (fire C.present ((⟨[], [], rows⟩ : Selection O).commit (T := T))) region =
      rows.toFinset
    ext x
    rw [mem_regionOf, mem_fire, List.mem_toFinset]
    simp only [Selection.commit, List.toFinset_nil, Finset.notMem_empty, not_false_eq_true,
      and_true, List.mem_toFinset]
    constructor
    · rintro ⟨present | made, inside⟩
      · exfalso
        have inRegion : x ∈ regionOf label C.present region := mem_regionOf.mpr ⟨present, inside⟩
        rw [empty] at inRegion
        exact Finset.notMem_empty x inRegion
      · exact made
    · intro made
      exact ⟨Or.inr made, rowsIn x made⟩
  unfold regionPaths pathsOf
  rw [regionAfter, List.toFinset_val, distinct.dedup, Multiset.map_coe]
  congr 1
  calc rows.map (fun o => wave (label o)) = (rows.map label).map wave := by
        rw [List.map_map]
        rfl
    _ = (paths.map pathRow).map wave := by rw [outputs]
    _ = paths.map id := by
        rw [List.map_map]
        exact List.map_congr_left fun z member => (encodes z member).2
    _ = paths := List.map_id paths

variable {T' : Type uT} {S' : Type uS} {O' : Type uO} [DecidableEq O']
variable {A' : SubstitutionAction T' S'} {label' : O' → T'} {amp : Firing T' S' O' → Amplitude}
  {catalogue : List (Firing T' S' O')} {budget : ℕ} {root : Configuration T' O'}
  {Q : ConfigurationClass A' O' → Prop}

/-- **Gathering a complete collection makes the verdict at the cut the verdict over the
branches.** After the bag of a complete collection is gathered into an empty region, the region
cancels exactly when the collection certifies a cancellation, reinforces exactly when it
certifies a reinforcement, and its coherent amplitude is the regional amplitude `Z_Q`. -/
theorem gather_certifies {bag : Multiset Amplitude}
    (complete : amplitudeCollection A' label' amp catalogue budget root Q = .complete bag)
    (listed : (paths : Multiset Amplitude) = bag) {C : Configuration T O}
    (valid : (gatherFiring pathRow paths rows : Firing T S O).Valid A label C)
    (empty : regionOf label C.present region = ∅) (encodes : Encodes wave region pathRow paths) :
    (Destructive (regionPaths label wave region
        ((gatherFiring pathRow paths rows : Firing T S O).result label C)) ↔
      CertifiesCancellation (amplitudeCollection A' label' amp catalogue budget root Q)) ∧
    (Constructive (regionPaths label wave region
        ((gatherFiring pathRow paths rows : Firing T S O).result label C)) ↔
      CertifiesReinforcement (amplitudeCollection A' label' amp catalogue budget root Q)) ∧
    coherent (regionPaths label wave region
        ((gatherFiring pathRow paths rows : Firing T S O).result label C)) =
      regionalAmplitude A' label' amp catalogue budget root Q := by
  have gathered := gather_regionPaths A label wave valid empty encodes
  obtain ⟨-, exact⟩ := (amplitudeCollection_eq_complete_iff A' label' amp catalogue budget root Q
    bag).mp complete
  rw [gathered, listed, complete]
  exact ⟨Iff.rfl, Iff.rfl, by rw [exact, regionalAmplitude_eq_coherent]⟩

/-- **The cancellation guard after the gather fires exactly when the collection certifies the
cancellation**, given a fresh result row of amplitude zero and a consistent store. -/
theorem gather_then_guard_iff {bag : Multiset Amplitude}
    (complete : amplitudeCollection A' label' amp catalogue budget root Q = .complete bag)
    (listed : (paths : Multiset Amplitude) = bag) {C : Configuration T O}
    (valid : (gatherFiring pathRow paths rows : Firing T S O).Valid A label C)
    (empty : regionOf label C.present region = ∅) (encodes : Encodes wave region pathRow paths)
    (bits : GuardBits A) (row : Amplitude → T) {r : O}
    (fresh : r ∉ ((gatherFiring pathRow paths rows : Firing T S O).result label C).present)
    (rowEq : label r = row 0)
    (consistent :
      A.Consistent ((gatherFiring pathRow paths rows : Firing T S O).result label C).equations) :
    (cancellationFiring A label wave bits row region
        (regionOf label ((gatherFiring pathRow paths rows : Firing T S O).result label C).present
          region) r).Valid A label
        ((gatherFiring pathRow paths rows : Firing T S O).result label C) ↔
      CertifiesCancellation (amplitudeCollection A' label' amp catalogue budget root Q) := by
  have certifies := (gather_certifies A label wave complete listed valid empty encodes).1
  constructor
  · intro guard
    exact certifies.mp (cancellation_adequate A label wave guard).2.1
  · intro certified
    have cancels := certifies.mpr certified
    exact waveform_fires A label wave cancels fresh (rowEq.trans (congrArg row cancels.1.symm))
      consistent

end Gather

/-! ## Gathering with a status row -/

section StatusGather

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T) (wave : T → Amplitude)

omit [DecidableEq O] in
/-- **The status mark of a collection**: the `yes` term of the status bits when the collection is
complete, the `no` term when it is not. -/
def statusMark (status : GuardBits A) : Collection Amplitude → T
  | .complete _ => status.yes
  | .incomplete _ => status.no

omit [DecidableEq O] in
/-- **The gather with a status row**: one row per path, and the status row `s` marked with the
status of the collection. -/
def statusGatherFiring (status : GuardBits A) (collection : Collection Amplitude)
    (pathRow : Amplitude → T) (paths : List Amplitude) (rows : List O) (s : O) : Firing T S O :=
  ⟨⟨[], [], [], [], paths.map pathRow ++ [statusMark A status collection]⟩, [],
    ⟨[], [], rows ++ [s]⟩⟩

omit [DecidableEq O] in
/-- **The certified cancellation guard**: the cancellation guard that also reads the status row
`s`, with the complete mark as its pattern. -/
def certifiedCancellationFiring (status bits : GuardBits A) (row : Amplitude → T)
    (region : T → Bool) (seen : Finset O) (s r : O) : Firing T S O :=
  ⟨⟨[], [status.yes], [], [bits.check (decide (Destructive (pathsOf label wave seen)))],
      [row (coherent (pathsOf label wave seen))]⟩,
    [PredicateQueryAdmission.Query.fixed ⟨region, seen⟩], ⟨[], [s], [r]⟩⟩

variable {status bits : GuardBits A} {collection : Collection Amplitude} {pathRow : Amplitude → T}
  {paths : List Amplitude} {rows : List O} {s : O} {row : Amplitude → T} {region : T → Bool}

/-- **The status row records the status of the gathered collection.** -/
theorem statusGather_marks {C : Configuration T O}
    (valid : (statusGatherFiring A status collection pathRow paths rows s).Valid A label C) :
    rows.map label = paths.map pathRow ∧ label s = statusMark A status collection := by
  have outputs : (rows ++ [s]).map label = paths.map pathRow ++ [statusMark A status collection] :=
    valid.firing.outputs
  rw [List.map_append] at outputs
  have lengths : (rows.map label).length = (paths.map pathRow).length := by
    have total := congrArg List.length outputs
    simp only [List.length_append, List.length_map, List.length_singleton] at total ⊢
    omega
  obtain ⟨front, back⟩ := List.append_inj outputs lengths
  exact ⟨front, by simpa using back⟩

/-- **A guard that needs the complete mark is refused wherever the status row is marked
incomplete**, whatever the paths. -/
theorem certified_refused_of_incomplete {seen : Finset O} {r : O} {C : Configuration T O}
    (recorded : label s = status.no) :
    ¬ (certifiedCancellationFiring A label wave status bits row region seen s r).Valid
      A label C := by
  intro valid
  obtain ⟨σ, solved⟩ := valid.firing.consistent
  have read : A.Solves σ (status.yes, label s) := solved _ (by
    simp [Selection.problem, Selection.equations, certifiedCancellationFiring])
  rw [recorded] at read
  have related : A.E (A.apply σ status.yes) (A.apply σ status.no) := read
  exact status.apart σ (A.equivalence.symm related)

/-- **Admission of the certified guard**: its query saw the whole region, the status row is present,
the result row is fresh and carries the coherent amplitude of the paths the query saw, the store
has a solution with the status row read as complete, and those paths cancel. -/
theorem certified_valid_iff (seen : Finset O) (r : O) (C : Configuration T O) :
    (certifiedCancellationFiring A label wave status bits row region seen s r).Valid A label C ↔
      regionOf label C.present region = seen ∧ s ∈ C.present ∧ r ∉ C.present ∧
        label r = row (coherent (pathsOf label wave seen)) ∧
        A.Consistent (C.equations ++ [(status.yes, label s)]) ∧
        Destructive (pathsOf label wave seen) := by
  have problem : (⟨[], [s], [r]⟩ : Selection O).problem label
      (⟨[], [status.yes], [], [bits.check (decide (Destructive (pathsOf label wave seen)))],
        [row (coherent (pathsOf label wave seen))]⟩ : RuleInstance T) C =
        C.equations ++ [(status.yes, label s)] := by
    simp [Selection.problem, Selection.equations]
  change PredicateQueryAdmission.Valid A label
      (⟨[], [status.yes], [], [bits.check (decide (Destructive (pathsOf label wave seen)))],
        [row (coherent (pathsOf label wave seen))]⟩ : RuleInstance T)
      ([(⟨region, seen⟩ : MeTTaCalculus.OccurrenceCommits.PredicateQuery O T)].map
        PredicateQueryAdmission.Query.fixed) C (⟨[], [s], [r]⟩ : Selection O) ↔ _
  rw [PredicateQueryAdmission.valid_fixed_iff]
  constructor
  · rintro ⟨firing, holds⟩
    have consistent := firing.consistent
    have checksHold := firing.checks
    rw [problem] at consistent checksHold
    obtain ⟨σ, solved⟩ := consistent
    have decided := (GuardBits.holds_iff label bits σ C.present _).mp
      (checksHold _ (List.mem_singleton_self _) σ solved)
    refine ⟨holds _ (List.mem_singleton_self _),
      firing.occurrences.kept_subset (by simp [Selection.commit]),
      fun present => Finset.disjoint_left.mp firing.occurrences.fresh (by simp [Selection.commit])
        present,
      by simpa using firing.outputs, ⟨σ, solved⟩, of_decide_eq_true decided⟩
  · rintro ⟨saw, present, fresh, rowEq, consistent, cancels⟩
    refine ⟨⟨by simp, by simp, rfl, rfl, by simp [rowEq],
      ⟨by simp [Selection.commit], by simpa [Selection.commit] using present,
        by simp [Selection.commit], by simpa [Selection.commit] using fresh,
        by simp [Selection.commit]⟩,
      by rw [problem]; exact consistent, ?_⟩, ?_⟩
    · rw [problem]
      intro check member σ _
      rw [List.mem_singleton.mp member]
      exact (GuardBits.holds_iff label bits σ C.present _).mpr (decide_eq_true cancels)
    · intro query member
      rw [List.mem_singleton.mp member]
      exact saw

/-- **Adequacy of the certified guard**: an admitted certified guard saw the whole region, the
region cancels at its cut, its row is the row of amplitude zero, and the status row it read is
present and not marked incomplete. -/
theorem certified_adequate {seen : Finset O} {r : O} {C : Configuration T O}
    (valid : (certifiedCancellationFiring A label wave status bits row region seen s r).Valid
      A label C) :
    seen = regionOf label C.present region ∧ Destructive (regionPaths label wave region C) ∧
      label r = row 0 ∧ s ∈ C.present ∧ label s ≠ status.no := by
  obtain ⟨saw, present, -, rowEq, -, cancels⟩ :=
    (certified_valid_iff A label wave seen r C).mp valid
  subst saw
  exact ⟨rfl, cancels, rowEq.trans (congrArg row cancels.1), present,
    fun recorded => certified_refused_of_incomplete A label wave recorded valid⟩

/-- **After a status gather of an incomplete collection, no certified guard reading its status row
fires**, at any cut and whatever the gathered paths, even when they cancel. -/
theorem statusGather_incomplete_refused {found : Multiset Amplitude} {C : Configuration T O}
    (valid : (statusGatherFiring A status (.incomplete found) pathRow paths rows s).Valid A label C)
    {seen : Finset O} {r : O} {D : Configuration T O} :
    ¬ (certifiedCancellationFiring A label wave status bits row region seen s r).Valid A label D :=
  certified_refused_of_incomplete A label wave (statusGather_marks A label valid).2

/-- **After a status gather into an empty region, the region holds exactly the gathered paths**,
when the status mark lies outside the region. -/
theorem statusGather_regionPaths {C : Configuration T O}
    (valid : (statusGatherFiring A status collection pathRow paths rows s).Valid A label C)
    (empty : regionOf label C.present region = ∅) (encodes : Encodes wave region pathRow paths)
    (outside : region (statusMark A status collection) = false) :
    regionPaths label wave region
        ((statusGatherFiring A status collection pathRow paths rows s).result label C) =
      (paths : Multiset Amplitude) := by
  obtain ⟨outputs, marked⟩ := statusGather_marks A label valid
  have distinct : rows.Nodup := (List.nodup_append.mp valid.firing.output_distinct).1
  have rowsIn : ∀ o ∈ rows, region (label o) = true := by
    intro o member
    have mapped : label o ∈ paths.map pathRow := outputs ▸ List.mem_map_of_mem member
    obtain ⟨z, inPaths, same⟩ := List.mem_map.mp mapped
    rw [← same]
    exact (encodes z inPaths).1
  have statusOut : region (label s) = false := by rw [marked]; exact outside
  have regionAfter : regionOf label
      ((statusGatherFiring A status collection pathRow paths rows s).result label C).present
        region = rows.toFinset := by
    change regionOf label (fire C.present ((⟨[], [], rows ++ [s]⟩ : Selection O).commit (T := T)))
      region = rows.toFinset
    ext x
    rw [mem_regionOf, mem_fire, List.mem_toFinset]
    simp only [Selection.commit, List.toFinset_nil, Finset.notMem_empty, not_false_eq_true,
      and_true, List.mem_toFinset, List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨present | made | rfl, inside⟩
      · exfalso
        have inRegion : x ∈ regionOf label C.present region := mem_regionOf.mpr ⟨present, inside⟩
        rw [empty] at inRegion
        exact Finset.notMem_empty x inRegion
      · exact made
      · rw [statusOut] at inside
        cases inside
    · intro made
      exact ⟨Or.inr (Or.inl made), rowsIn x made⟩
  unfold regionPaths pathsOf
  rw [regionAfter, List.toFinset_val, distinct.dedup, Multiset.map_coe]
  congr 1
  calc rows.map (fun o => wave (label o)) = (rows.map label).map wave := by
        rw [List.map_map]
        rfl
    _ = (paths.map pathRow).map wave := by rw [outputs]
    _ = paths.map id := by
        rw [List.map_map]
        exact List.map_congr_left fun z member => (encodes z member).2
    _ = paths := List.map_id paths

variable {T' : Type uT} {S' : Type uS} {O' : Type uO} [DecidableEq O']
variable {A' : SubstitutionAction T' S'} {label' : O' → T'} {amp : Firing T' S' O' → Amplitude}
  {catalogue : List (Firing T' S' O')} {budget : ℕ} {root : Configuration T' O'}
  {Q : ConfigurationClass A' O' → Prop}

/-- **After a status gather of a complete collection, the certified guard fires exactly when the
collection certifies the cancellation**, given a fresh result row of amplitude zero and a store
that has a solution with the status row read. -/
theorem statusGather_complete_iff {bag : Multiset Amplitude}
    (complete : amplitudeCollection A' label' amp catalogue budget root Q = .complete bag)
    (listed : (paths : Multiset Amplitude) = bag) {C : Configuration T O}
    (valid : (statusGatherFiring A status (.complete bag) pathRow paths rows s).Valid A label C)
    (empty : regionOf label C.present region = ∅) (encodes : Encodes wave region pathRow paths)
    (outside : region status.yes = false) {r : O}
    (fresh : r ∉ ((statusGatherFiring A status (.complete bag) pathRow paths rows s).result
      label C).present)
    (rowEq : label r = row 0)
    (consistent : A.Consistent (((statusGatherFiring A status (.complete bag) pathRow paths rows
      s).result label C).equations ++ [(status.yes, label s)])) :
    (certifiedCancellationFiring A label wave status bits row region
        (regionOf label ((statusGatherFiring A status (.complete bag) pathRow paths rows s).result
          label C).present region) s r).Valid A label
        ((statusGatherFiring A status (.complete bag) pathRow paths rows s).result label C) ↔
      CertifiesCancellation (amplitudeCollection A' label' amp catalogue budget root Q) := by
  have gathered := statusGather_regionPaths A label wave valid empty encodes outside
  have made : s ∈ ((statusGatherFiring A status (.complete bag) pathRow paths rows s).result
      label C).present := by
    change s ∈ fire C.present ((⟨[], [], rows ++ [s]⟩ : Selection O).commit (T := T))
    rw [mem_fire]
    exact Or.inr (by simp [Selection.commit])
  rw [certified_valid_iff, complete]
  change _ ↔ Destructive bag
  constructor
  · rintro ⟨-, -, -, -, -, cancels⟩
    have paths' := gathered
    unfold regionPaths at paths'
    rw [paths', listed] at cancels
    exact cancels
  · intro cancels
    have cancelsAtCut : Destructive (pathsOf label wave (regionOf label
        ((statusGatherFiring A status (.complete bag) pathRow paths rows s).result label C).present
        region)) := by
      have paths' := gathered
      unfold regionPaths at paths'
      rw [paths', listed]
      exact cancels
    exact ⟨rfl, made, fresh, rowEq.trans (congrArg row cancelsAtCut.1.symm), consistent,
      cancelsAtCut⟩

end StatusGather

end AmplitudeRuns

open AmplitudeRuns

#print axioms gatherable_eq_some_iff
#print axioms gatherable_amplitudeCollection
#print axioms gather_regionPaths
#print axioms gather_certifies
#print axioms gather_then_guard_iff
#print axioms statusGather_marks
#print axioms certified_refused_of_incomplete
#print axioms certified_valid_iff
#print axioms certified_adequate
#print axioms statusGather_incomplete_refused
#print axioms statusGather_regionPaths
#print axioms statusGather_complete_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
