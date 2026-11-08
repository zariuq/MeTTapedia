import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsAmplitudeMeasurement

/-!
# When amplitude grades are the right grade: records, cross terms and four aggregations

## Records destroy interference

* A finite family of branches carries amplitudes and ends: the state each branch leaves at the
  cut. The **record-respecting Born readout** (`endReadout`) adds amplitudes over the branches that
  end in one state, and adds Born weights over different end states.
* It is the classical sum of the branch weights plus one cross term per end state
  (`endReadout_eq`).
* **Records destroy interference** (`endReadout_of_injOn`): when no two branches end in the same
  state, because each publishes a record that distinguishes it, the readout is the classical sum
  of the branch weights.
* **Two unrecorded branches** (`endReadout_unrecorded_pair`): when exactly two branches share an
  end and every other branch is distinguished, the readout differs from the classical sum by
  exactly their cross term `interference a₁ a₂ = 2 Re(a₁ ā₂)`.
* **One end** (`endReadout_of_one_end`): when every branch ends in one state, the readout is the
  Born weight of the coherent sum. Only then is `born Z_Q` the Born weight of a region.
* **Records add** (`endReadout_union_of_disjoint_ends`): families whose end states are disjoint
  have additive readouts; this is revision by adding weights.

## On causal histories

`branchReadout` is the readout of the causal histories of R27's unfolding that end in a region
`Q`, with the configuration class each history reaches as its end. A configuration class keeps
its present occurrence identities, so a made row is a record. At a closed frontier:

* recorded histories read classically (`branchReadout_of_recorded`);
* histories with one end read as `born Z_Q` (`branchReadout_of_one_end`);
* two unrecorded histories differ from the classical sum by their cross term
  (`branchReadout_unrecorded_pair`).

## Coherent sums and pairwise cross terms

The Born weight of a sum of paths is the sum of their Born weights plus the pairwise cross terms
(`born_sum_eq`), so coherent summation agrees with classical aggregation exactly when the pairwise
cross terms sum to zero (`born_sum_eq_classical_iff`).

## Four aggregations

* **Deduplicating causal histories against summing over interleavings**: they agree when every
  branch has one interleaving (`interleaving_eq_regional_of_single`); the diamond of
  `AnnotatedRunsAmplitudeControls` separates them.
* **Coherent summation against probabilistic aggregation over recorded outcomes**: they agree when
  the cross terms vanish, in particular when records separate the branches; `{1, -1}` separates
  them.
* **Ledger union against probabilistic aggregation**: union adds evidence when the ledgers are
  disjoint (`ledger_union_eq_add_of_disjoint`) and counts a shared observation once where the sum
  counts it twice (`ledger_overlap_control`).
* **What a ledger forgets**: no readout of a published ledger computes the weights of the runs it
  records (`no_weight_readout_after_publication`); `AnnotatedRunsAmplitudeMeasurement` shows that
  no readout of published Born weights computes the coherent weight.
-/

set_option autoImplicit false

open scoped QuadraticAlgebra

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace AmplitudeRuns

open Mettapedia.Algebra.RationalComplexAmplitude (Amplitude born)
open AnnotatedRunUnfolding (CausalClass)
open Mettapedia.PLN.WorldModel.EvidenceContracts (ledgerEvidence ledgerEvidence_union_of_disjoint
  ledgerEvidence_total)
open Mettapedia.PLN.WorldModel.EvidenceSpaces (Evidence)

universe uT uS uO

/-! ## The record-respecting Born readout -/

section Ends

variable {ι : Type*} {E : Type*} [DecidableEq E]

/-- **The branches of a family that end in the state `e`.** -/
def fiber (ends : ι → E) (branches : Finset ι) (e : E) : Finset ι :=
  branches.filter fun b => ends b = e

/-- **The record-respecting Born readout**: amplitudes add over the branches that end in one
state, and Born weights add over different end states. -/
def endReadout (ends : ι → E) (amp : ι → Amplitude) (branches : Finset ι) : ℚ :=
  ∑ e ∈ branches.image ends, born (∑ b ∈ fiber ends branches e, amp b)

/-- **The classical sum of the branch weights.** -/
def classicalWeight (amp : ι → Amplitude) (branches : Finset ι) : ℚ :=
  ∑ b ∈ branches, born (amp b)

/-- **The cross term of a family**: the Born weight of its coherent sum less its classical
weight. -/
def crossTerm (amp : ι → Amplitude) (branches : Finset ι) : ℚ :=
  born (∑ b ∈ branches, amp b) - classicalWeight amp branches

theorem crossTerm_singleton (amp : ι → Amplitude) (b : ι) : crossTerm amp {b} = 0 := by
  simp [crossTerm, classicalWeight]

/-- **The readout is the classical sum plus one cross term per end state.** -/
theorem endReadout_eq (ends : ι → E) (amp : ι → Amplitude) (branches : Finset ι) :
    endReadout ends amp branches =
      classicalWeight amp branches +
        ∑ e ∈ branches.image ends, crossTerm amp (fiber ends branches e) := by
  have split : classicalWeight amp branches =
      ∑ e ∈ branches.image ends, classicalWeight amp (fiber ends branches e) := by
    unfold classicalWeight fiber
    exact (Finset.sum_fiberwise_of_maps_to
      (fun b member => Finset.mem_image_of_mem ends member) _).symm
  rw [split, ← Finset.sum_add_distrib]
  unfold endReadout crossTerm
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-- The fiber of a branch's end is that branch alone when no other branch shares its end. -/
theorem fiber_eq_singleton {ends : ι → E} {branches : Finset ι} {b : ι} (inB : b ∈ branches)
    (alone : ∀ b' ∈ branches, ends b' = ends b → b' = b) :
    fiber ends branches (ends b) = {b} := by
  ext b'
  simp only [fiber, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨inB', same⟩
    exact alone b' inB' same
  · intro same
    rw [same]
    exact ⟨inB, rfl⟩

/-- **Records destroy interference.** If no two branches end in the same state, the
record-respecting readout is the classical sum of the branch weights. -/
theorem endReadout_of_injOn {ends : ι → E} (amp : ι → Amplitude) {branches : Finset ι}
    (recorded : Set.InjOn ends branches) :
    endReadout ends amp branches = classicalWeight amp branches := by
  rw [endReadout_eq]
  have zero : ∀ e ∈ branches.image ends, crossTerm amp (fiber ends branches e) = 0 := by
    intro e member
    obtain ⟨b, inB, rfl⟩ := Finset.mem_image.mp member
    rw [fiber_eq_singleton inB fun b' inB' same => recorded inB' inB same]
    exact crossTerm_singleton amp b
  rw [Finset.sum_eq_zero zero, add_zero]

/-- **Two unrecorded branches.** If two branches end in the same state and every other pair of
branches is distinguished by its ends, the readout differs from the classical sum by exactly their
cross term `2 Re(a₁ ā₂)`. -/
theorem endReadout_unrecorded_pair [DecidableEq ι] {ends : ι → E} (amp : ι → Amplitude)
    {branches : Finset ι} {first second : ι} (inFirst : first ∈ branches)
    (inSecond : second ∈ branches) (distinct : first ≠ second)
    (unrecorded : ends first = ends second) (others : Set.InjOn ends (branches.erase second)) :
    endReadout ends amp branches =
      classicalWeight amp branches + interference (amp first) (amp second) := by
  rw [endReadout_eq]
  congr 1
  have pairFiber : fiber ends branches (ends first) = {first, second} := by
    ext b
    simp only [fiber, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨inB, same⟩
      by_cases isSecond : b = second
      · exact Or.inr isSecond
      · exact Or.inl (others (Finset.mem_erase.mpr ⟨isSecond, inB⟩)
          (Finset.mem_erase.mpr ⟨distinct, inFirst⟩) same)
    · rintro (isFirst | isSecond)
      · rw [isFirst]
        exact ⟨inFirst, rfl⟩
      · rw [isSecond]
        exact ⟨inSecond, unrecorded.symm⟩
  have single : ∀ b ∈ branches, ends b ≠ ends first →
      fiber ends branches (ends b) = {b} := by
    intro b inB apart
    refine fiber_eq_singleton inB fun b' inB' same => ?_
    have notSecond' : b' ≠ second := fun isSecond =>
      apart (by rw [← same, isSecond, unrecorded])
    have notSecond : b ≠ second := fun isSecond => apart (by rw [isSecond, unrecorded])
    exact others (Finset.mem_erase.mpr ⟨notSecond', inB'⟩) (Finset.mem_erase.mpr ⟨notSecond, inB⟩)
      same
  rw [Finset.sum_eq_single_of_mem (ends first) (Finset.mem_image_of_mem ends inFirst)]
  · rw [pairFiber]
    simp only [crossTerm, classicalWeight]
    rw [Finset.sum_pair distinct, Finset.sum_pair distinct, born_add]
    ring
  · intro e member apart
    obtain ⟨b, inB, rfl⟩ := Finset.mem_image.mp member
    rw [single b inB apart]
    exact crossTerm_singleton amp b

/-- **One end state**: when every branch ends in one state, the readout is the Born weight of the
coherent sum of all the branches. -/
theorem endReadout_of_one_end {ends : ι → E} (amp : ι → Amplitude) {branches : Finset ι} {e : E}
    (nonempty : branches.Nonempty) (shared : ∀ b ∈ branches, ends b = e) :
    endReadout ends amp branches = born (∑ b ∈ branches, amp b) := by
  have image : branches.image ends = {e} := by
    ext e'
    simp only [Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨b, inB, rfl⟩
      exact shared b inB
    · intro same
      obtain ⟨b, inB⟩ := nonempty
      exact ⟨b, inB, (shared b inB).trans same.symm⟩
  have whole : fiber ends branches e = branches := Finset.filter_true_of_mem shared
  unfold endReadout
  rw [image, Finset.sum_singleton, whole]

/-- **Records add**: two families whose end states are disjoint have additive readouts. -/
theorem endReadout_union_of_disjoint_ends [DecidableEq ι] (ends : ι → E) (amp : ι → Amplitude)
    {first second : Finset ι}
    (apart : Disjoint (first.image ends) (second.image ends)) :
    endReadout ends amp (first ∪ second) =
      endReadout ends amp first + endReadout ends amp second := by
  have fibersFirst : ∀ e ∈ first.image ends,
      fiber ends (first ∪ second) e = fiber ends first e := by
    intro e member
    ext b
    simp only [fiber, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨inFirst | inSecond, same⟩
      · exact ⟨inFirst, same⟩
      · exact absurd (same ▸ Finset.mem_image_of_mem ends inSecond)
          (Finset.disjoint_left.mp apart member)
    · rintro ⟨inFirst, same⟩
      exact ⟨Or.inl inFirst, same⟩
  have fibersSecond : ∀ e ∈ second.image ends,
      fiber ends (first ∪ second) e = fiber ends second e := by
    intro e member
    ext b
    simp only [fiber, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨inFirst | inSecond, same⟩
      · exact absurd (same ▸ Finset.mem_image_of_mem ends inFirst)
          (Finset.disjoint_right.mp apart member)
      · exact ⟨inSecond, same⟩
    · rintro ⟨inSecond, same⟩
      exact ⟨Or.inr inSecond, same⟩
  unfold endReadout
  rw [Finset.image_union, Finset.sum_union apart]
  congr 1
  · exact Finset.sum_congr rfl fun e member => by rw [fibersFirst e member]
  · exact Finset.sum_congr rfl fun e member => by rw [fibersSecond e member]

end Ends

/-! ## The readout of causal histories -/

section Branches

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T) (amp : Firing T S O → Amplitude)
variable (catalogue : List (Firing T S O)) (budget : ℕ) (root : Configuration T O)
  (Q : ConfigurationClass A O → Prop)

open Classical in
/-- **The record-respecting readout of a region**: the causal histories that end in `Q`, each
with the configuration class it reaches as its end. -/
noncomputable def branchReadout : ℚ :=
  endReadout (classEnd A label root) (classAmplitude A label amp root)
    (regionBranches A label catalogue budget root Q)

theorem incoherent_branchAmplitudes :
    incoherent (branchAmplitudes A label amp catalogue budget root Q) =
      classicalWeight (classAmplitude A label amp root)
        (regionBranches A label catalogue budget root Q) := by
  unfold incoherent branchAmplitudes classicalWeight
  rw [Multiset.map_map]
  rfl

/-! ### Two ends: identities kept, or renamed

`classEnd` keeps the occurrence identities of a configuration class: two histories that make
rows of one label under different identities end in different classes, so every made row is a
record there. The **nominal end** (`nominalEnd`) reads a class up to renaming of its occurrence
identities: the solutions of its knowledge and the bag of the labels present
(`nominalEnd_rename`). The identity end refines it, so a nominal record is an identity record and,
when the nominal end separates the histories, the two readouts are the same classical sum
(`nominalReadout_of_recorded`). They differ exactly on histories that differ only in names. -/

/-- Equation stores with the same solutions. -/
def knowledgeSetoid : Setoid (EquationStore T) where
  r := A.Equivalent
  iseqv := ⟨fun _ _ => Iff.rfl, fun same σ => (same σ).symm,
    fun first second σ => (first σ).trans (second σ)⟩

/-- **The nominal end of a configuration class**: its knowledge up to solutions and the bag of the
labels of its present occurrences, without their identities. -/
def nominalEnd : ConfigurationClass A O → Quotient (knowledgeSetoid A) × Multiset T :=
  Quotient.lift (fun C => (Quotient.mk (knowledgeSetoid A) C.equations, C.present.val.map label))
    fun C D same => by
      obtain ⟨equivalent, present⟩ := same
      have store : Quotient.mk (knowledgeSetoid A) C.equations =
          Quotient.mk (knowledgeSetoid A) D.equations := Quotient.sound equivalent
      simp only [store, present]

omit [DecidableEq O] in
theorem nominalEnd_mk (C : Configuration T O) :
    nominalEnd A label (ConfigurationClass.mk A C) =
      (Quotient.mk (knowledgeSetoid A) C.equations, C.present.val.map label) := rfl

omit [DecidableEq O] in
/-- **Renaming occurrence identities without changing their labels keeps the nominal end.** -/
theorem nominalEnd_rename (π : O ≃ O) (labels : ∀ o, label (π o) = label o)
    (C : Configuration T O) :
    nominalEnd A label (ConfigurationClass.mk A ⟨C.equations, C.present.map π.toEmbedding⟩) =
      nominalEnd A label (ConfigurationClass.mk A C) := by
  rw [nominalEnd_mk, nominalEnd_mk, Finset.map_val, Multiset.map_map]
  have same : label ∘ π.toEmbedding = label := funext labels
  rw [same]

open Classical in
/-- **The nominal readout of a region**: the causal histories that end in `Q`, each with the nominal
end of the class it reaches. -/
noncomputable def nominalReadout : ℚ :=
  endReadout (fun trace => nominalEnd A label (classEnd A label root trace))
    (classAmplitude A label amp root) (regionBranches A label catalogue budget root Q)

variable {catalogue budget root Q}

/-- **Recorded causal histories read classically**: if the histories that end in `Q` reach
pairwise different configuration classes, the readout is their incoherent weight. -/
theorem branchReadout_of_recorded
    (recorded : Set.InjOn (classEnd A label root)
      (regionBranches A label catalogue budget root Q)) :
    branchReadout A label amp catalogue budget root Q =
      incoherent (branchAmplitudes A label amp catalogue budget root Q) := by
  classical
  rw [incoherent_branchAmplitudes]
  unfold branchReadout
  convert endReadout_of_injOn (classAmplitude A label amp root) recorded

/-- **Histories with one end read as `born Z_Q`.** -/
theorem branchReadout_of_one_end {e : ConfigurationClass A O}
    (nonempty : (regionBranches A label catalogue budget root Q).Nonempty)
    (shared : ∀ trace ∈ regionBranches A label catalogue budget root Q,
      classEnd A label root trace = e) :
    branchReadout A label amp catalogue budget root Q =
      born (regionalAmplitude A label amp catalogue budget root Q) := by
  classical
  unfold branchReadout regionalAmplitude
  convert endReadout_of_one_end (classAmplitude A label amp root) nonempty shared

open Classical in
/-- **Two unrecorded causal histories**: the readout differs from the incoherent weight by their
cross term. -/
theorem branchReadout_unrecorded_pair {first second : CausalClass A label root}
    (inFirst : first ∈ regionBranches A label catalogue budget root Q)
    (inSecond : second ∈ regionBranches A label catalogue budget root Q)
    (distinct : first ≠ second)
    (unrecorded : classEnd A label root first = classEnd A label root second)
    (others : Set.InjOn (classEnd A label root)
      ((regionBranches A label catalogue budget root Q).erase second)) :
    branchReadout A label amp catalogue budget root Q =
      incoherent (branchAmplitudes A label amp catalogue budget root Q) +
        interference (classAmplitude A label amp root first)
          (classAmplitude A label amp root second) := by
  classical
  rw [incoherent_branchAmplitudes]
  unfold branchReadout
  convert endReadout_unrecorded_pair (classAmplitude A label amp root) inFirst inSecond distinct
    unrecorded others

/-- **When the nominal end separates the histories, the two readouts agree**: both are the
classical sum, since a nominal record is an identity record. -/
theorem nominalReadout_of_recorded
    (recorded : Set.InjOn (fun trace => nominalEnd A label (classEnd A label root trace))
      (regionBranches A label catalogue budget root Q)) :
    nominalReadout A label amp catalogue budget root Q =
      branchReadout A label amp catalogue budget root Q := by
  classical
  have identity : Set.InjOn (classEnd A label root) (regionBranches A label catalogue budget root Q) := by
    intro first inFirst second inSecond same
    exact recorded inFirst inSecond (congrArg (nominalEnd A label) same)
  rw [branchReadout_of_recorded A label amp identity, incoherent_branchAmplitudes]
  unfold nominalReadout
  convert endReadout_of_injOn (classAmplitude A label amp root) recorded

/-- **Histories with one nominal end read as `born Z_Q`.** -/
theorem nominalReadout_of_one_end {e : Quotient (knowledgeSetoid A) × Multiset T}
    (nonempty : (regionBranches A label catalogue budget root Q).Nonempty)
    (shared : ∀ trace ∈ regionBranches A label catalogue budget root Q,
      nominalEnd A label (classEnd A label root trace) = e) :
    nominalReadout A label amp catalogue budget root Q =
      born (regionalAmplitude A label amp catalogue budget root Q) := by
  classical
  unfold nominalReadout regionalAmplitude
  convert endReadout_of_one_end (classAmplitude A label amp root) nonempty shared

end Branches

/-! ## Coherent sums and pairwise cross terms -/

section Pairwise

/-- **The pairwise interference of a list of paths**: `interference zᵢ zⱼ` summed over `i < j`. -/
def pairwiseInterference : List Amplitude → ℚ
  | [] => 0
  | z :: rest => (rest.map (interference z)).sum + pairwiseInterference rest

theorem interference_add_right (z w u : Amplitude) :
    interference z (w + u) = interference z w + interference z u := by
  unfold interference
  simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
  ring

theorem interference_sum_right (z : Amplitude) (paths : List Amplitude) :
    interference z paths.sum = (paths.map (interference z)).sum := by
  induction paths with
  | nil => simp [interference]
  | cons w rest ih =>
      rw [List.sum_cons, interference_add_right, ih, List.map_cons, List.sum_cons]

/-- **Coherent is classical plus the pairwise cross terms.** -/
theorem born_sum_eq (paths : List Amplitude) :
    born paths.sum = (paths.map born).sum + pairwiseInterference paths := by
  induction paths with
  | nil => simp [pairwiseInterference]
  | cons z rest ih =>
      have unfolded : pairwiseInterference (z :: rest) =
          (rest.map (interference z)).sum + pairwiseInterference rest := rfl
      rw [List.sum_cons, born_add, ih, interference_sum_right, List.map_cons, List.sum_cons,
        unfolded]
      ring

/-- **Coherent summation agrees with classical aggregation exactly when the pairwise cross terms
sum to zero.** -/
theorem born_sum_eq_classical_iff (paths : List Amplitude) :
    born paths.sum = (paths.map born).sum ↔ pairwiseInterference paths = 0 := by
  rw [born_sum_eq]
  constructor <;> intro h <;> linarith

/-- **Controls**: `1, -1` and `1, 1` have pairwise interference `-2` and `2`; `1, i` has `0`. -/
theorem pairwise_controls :
    pairwiseInterference [1, -1] = -2 ∧ pairwiseInterference [1, 1] = 2 ∧
      pairwiseInterference [1, unitI] = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [pairwiseInterference, interference, unitI]

end Pairwise

/-! ## Four aggregations -/

section Aggregations

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T) (amp : Firing T S O → Amplitude)
variable {catalogue : List (Firing T S O)} {budget : ℕ} {root : Configuration T O}
  {Q : ConfigurationClass A O → Prop}

/-- **Deduplication against interleavings**: when every branch of the region has exactly one
interleaving, summing over interleavings is summing over causal histories. -/
theorem interleaving_eq_regional_of_single
    (single : ∀ trace ∈ regionBranches A label catalogue budget root Q,
      interleavings A label catalogue budget root Q trace = 1) :
    interleavingAmplitude A label amp catalogue budget root Q =
      regionalAmplitude A label amp catalogue budget root Q := by
  rw [interleavingAmplitude_eq_sum_count]
  unfold regionalAmplitude
  refine Finset.sum_congr rfl fun trace member => ?_
  rw [single trace member, one_smul]

/-- **Ledger union is aggregation for disjoint records** (R30's revision). -/
theorem ledger_union_eq_add_of_disjoint {Id W : Type*} [DecidableEq Id] (world : Id → W)
    (φ : W → Bool) {first second : Finset Id} (apart : Disjoint first second) :
    ledgerEvidence world φ (first ∪ second) =
      ledgerEvidence world φ first + ledgerEvidence world φ second :=
  ledgerEvidence_union_of_disjoint world φ apart

/-- **Union is not aggregation when records overlap**: an observation in both ledgers is one
sample of their union and two samples of the sum of their evidence. -/
theorem ledger_overlap_control {Id W : Type*} [DecidableEq Id] (world : Id → W) (φ : W → Bool)
    (i : Id) :
    (ledgerEvidence world φ ({i} ∪ {i})).total = 1 ∧
      (ledgerEvidence world φ {i} + ledgerEvidence world φ {i}).total = 2 := by
  have one := ledgerEvidence_total world φ ({i} : Finset Id)
  refine ⟨by rw [ledgerEvidence_total, Finset.union_self, Finset.card_singleton], ?_⟩
  rw [Finset.card_singleton] at one
  simp only [Mettapedia.PLN.WorldModel.EvidenceSpaces.Evidence.total,
    Mettapedia.PLN.WorldModel.EvidenceSpaces.Evidence.add_pos,
    Mettapedia.PLN.WorldModel.EvidenceSpaces.Evidence.add_neg] at one ⊢
  omega

/-- **A ledger forgets the weights.** Publishing the runs `true` (yes) and `false` (no) gives one
ledger whatever weights the runs carry, so no readout of the ledger computes the probability of
yes. -/
theorem no_weight_readout_after_publication :
    ¬ ∃ readout : Evidence ℕ → ℚ, ∀ weight : Bool → ℚ, 0 < weight true → 0 < weight false →
      readout (ledgerEvidence (fun b : Bool => b) (fun b => b) Finset.univ) =
        weight true / (weight true + weight false) := by
  rintro ⟨readout, computes⟩
  have even := computes (fun _ => 1) one_pos one_pos
  have uneven := computes (fun b => if b then 1 else 2) (by norm_num) (by norm_num)
  rw [even] at uneven
  norm_num at uneven

end Aggregations

end AmplitudeRuns

open AmplitudeRuns

#print axioms endReadout_eq
#print axioms fiber_eq_singleton
#print axioms endReadout_of_injOn
#print axioms endReadout_unrecorded_pair
#print axioms endReadout_of_one_end
#print axioms endReadout_union_of_disjoint_ends
#print axioms incoherent_branchAmplitudes
#print axioms branchReadout_of_recorded
#print axioms branchReadout_of_one_end
#print axioms branchReadout_unrecorded_pair
#print axioms nominalEnd_rename
#print axioms nominalReadout_of_recorded
#print axioms nominalReadout_of_one_end
#print axioms interference_add_right
#print axioms interference_sum_right
#print axioms born_sum_eq
#print axioms born_sum_eq_classical_iff
#print axioms pairwise_controls
#print axioms interleaving_eq_regional_of_single
#print axioms ledger_union_eq_add_of_disjoint
#print axioms ledger_overlap_control
#print axioms no_weight_readout_after_publication

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
