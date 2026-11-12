import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreControls

/-!
# Every native event is a framed leaf at its footprint

The footprint of a firing at a configuration keeps the whole knowledge and only the occurrences
the firing takes or reads. The rest keeps no knowledge and every occurrence the firing does not
take. The configuration is their tensor, and the two overlap exactly in the occurrences the
firing reads: the lent zone of the logical reading is the overlap of a placement.

* `tensor_footprint_rest`: the tensor of the footprint and the rest is the configuration, up to
  the isomorphism of the transport.
* `footprint_inter_rest`: the footprint and the rest share exactly the read occurrences.
* `valid_footprint`: a firing without predicate queries whose checks hold of every smaller store
  (equality and absence checks) is admitted at its footprint.
* `event_is_framed_leaf`: such an admitted firing is the placed candidate of its own leaf run at
  its footprint, beside the rest. So every native run of such firings is a cut of framed leaves.
* `a_count_is_no_leaf_at_its_footprint`: a counting check admitted at a configuration can be
  refused at the footprint, so the leaves of counting checks are prepared candidates, not
  admitted firings.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.FirstOrder

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open AnnotatedRuns (Firing firstOrder firstOrderTransport)
open GuardFreeProcessOrders (SameUpTo)
open FirstOrderNativeRuns
open KnowledgeTensorFirstOrder

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-- The footprint of a firing: the knowledge of the configuration, and the occurrences the
firing takes or reads. -/
def footprint (C : Configuration T O) (f : Firing T S O) : Configuration T O :=
  ⟨C.equations, f.selection.taken.toFinset ∪ f.selection.read.toFinset⟩

/-- The rest of the configuration: no knowledge, and every occurrence the firing does not take. -/
def rest (C : Configuration T O) (f : Firing T S O) : Configuration T O :=
  ⟨[], C.present \ f.selection.taken.toFinset⟩

/-- The checks of a rule hold of every smaller store: each is an equality or an absence check. -/
def Shrinks (rule : RuleInstance T) : Prop :=
  ∀ check ∈ rule.checks, (∃ one two, check = Check.equal one two) ∨ ∃ pattern, check = Check.absent pattern

/-- The tensor of the footprint and the rest is the configuration. -/
theorem tensor_footprint_rest (A : SubstitutionAction T S) {C : Configuration T O} {f : Firing T S O}
    (takenIn : f.selection.taken.toFinset ⊆ C.present)
    (readIn : f.selection.read.toFinset ⊆ C.present) :
    SameUpTo A (AnnotatedRuns.tensor (footprint C f) (rest C f)) C := by
  refine ⟨fun σ => ?_, ?_⟩
  · show A.Models σ (C.equations ++ []) ↔ A.Models σ C.equations
    rw [List.append_nil]
  · show f.selection.taken.toFinset ∪ f.selection.read.toFinset ∪
        (C.present \ f.selection.taken.toFinset) = C.present
    ext occurrence
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ((taken | read) | ⟨present, _⟩)
      · exact takenIn taken
      · exact readIn read
      · exact present
    · intro present
      by_cases taken : occurrence ∈ f.selection.taken.toFinset
      · exact Or.inl (Or.inl taken)
      · exact Or.inr ⟨present, taken⟩

/-- **The lent zone is the overlap of the placement**: the footprint and the rest share exactly
the occurrences the firing reads. -/
theorem footprint_inter_rest {C : Configuration T O} {f : Firing T S O}
    (readIn : f.selection.read.toFinset ⊆ C.present)
    (apart : Disjoint f.selection.taken.toFinset f.selection.read.toFinset) :
    (footprint C f).present ∩ (rest C f).present = f.selection.read.toFinset := by
  show (f.selection.taken.toFinset ∪ f.selection.read.toFinset) ∩
      (C.present \ f.selection.taken.toFinset) = f.selection.read.toFinset
  ext occurrence
  simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro ⟨taken | read, _, untaken⟩
    · exact absurd taken untaken
    · exact read
  · intro read
    exact ⟨Or.inr read, readIn read, fun taken => Finset.disjoint_left.mp apart taken read⟩

/-- A firing whose checks hold of every smaller store is admitted at its footprint. -/
theorem valid_footprint (A : SubstitutionAction T S) (label : O → T) {C : Configuration T O}
    {f : Firing T S O} (valid : f.Valid A label C) (shrinks : Shrinks f.rule)
    (plain : f.queries = []) : f.Valid A label (footprint C f) := by
  have occurrences := valid.firing.occurrences
  have inside : f.selection.taken.toFinset ∪ f.selection.read.toFinset ⊆ C.present :=
    Finset.union_subset occurrences.taken_subset occurrences.kept_subset
  refine ⟨⟨valid.firing.take_distinct, valid.firing.output_distinct, valid.firing.take_length,
    valid.firing.read_length, valid.firing.outputs, ?_, valid.firing.consistent, ?_⟩, ?_⟩
  · refine ⟨Finset.subset_union_left, Finset.subset_union_right, occurrences.apart,
      Finset.disjoint_of_subset_right inside occurrences.fresh, ?_⟩
    intro query member
    simp [Selection.commit] at member
  · intro check member σ solved
    have here := valid.firing.checks check member σ solved
    rcases shrinks check member with ⟨one, two, rfl⟩ | ⟨pattern, rfl⟩
    · exact here
    · intro occurrence present
      exact here occurrence (inside present)
  · intro query member
    rw [plain] at member
    cases member

/-- **Every native event whose checks shrink is a framed leaf.** The firing is admitted at its
footprint, and its one-firing leaf run there has a placed native run beside the rest, at a state
isomorphic to the configuration. -/
theorem event_is_framed_leaf (A : SubstitutionAction T S) (label : O → T) {C : Configuration T O}
    {f : Firing T S O} (valid : f.Valid A label C) (shrinks : Shrinks f.rule)
    (plain : f.queries = []) :
    ∃ (leaf : f.Valid A label (footprint C f))
      (native : (firstOrder A label).toStep.Run (AnnotatedRuns.tensor (footprint C f) (rest C f))),
      Places (contextualRunInterpretation A label) (left := footprint C f) (right := rest C f)
        PUnit.unit (.cons f leaf (.nil _)) native ∧
      Nonempty ((firstOrderTransport A label).Iso
        (AnnotatedRuns.tensor (footprint C f) (rest C f)) C) := by
  have occurrences := valid.firing.occurrences
  have same : SameUpTo A (AnnotatedRuns.tensor (footprint C f) (rest C f)) C :=
    tensor_footprint_rest A occurrences.taken_subset occurrences.kept_subset
  have leaf := valid_footprint A label valid shrinks plain
  have placed : f.Valid A label (AnnotatedRuns.tensor (footprint C f) (rest C f)) :=
    (Firing.valid_congr A label same).mpr valid
  have framed : (contextualRunInterpretation A label).domain (left := footprint C f)
      (right := rest C f) PUnit.unit f := by
    show Disjoint f.selection.taken.toFinset (C.present \ f.selection.taken.toFinset)
    exact Finset.disjoint_sdiff
  obtain ⟨native, places⟩ :=
    (exists_places_iff_checks (contextualRunInterpretation A label) (left := footprint C f)
      (right := rest C f) PUnit.unit (.cons f leaf (.nil _))).mpr
      ⟨⟨framed, (valid_tensor_iff A label f leaf).mp placed⟩, trivial⟩
  exact ⟨leaf, native, places, ⟨⟨same⟩⟩⟩

/-! ## Controls -/

open KnowledgeTensorFirstOrderControls (plain unlessNine) in
/-- Positive control: an absence check holds of every smaller store. -/
theorem absence_shrinks : Shrinks unlessNine := by
  intro check member
  have which : check = Check.absent 9 := List.mem_singleton.mp member
  exact Or.inr ⟨9, which⟩

/-- Negative control: a counting check does not. -/
theorem counting_does_not_shrink : ¬ Shrinks (Controls.counts 2).rule := by
  intro shrinks
  rcases shrinks (Check.count 5 2) (List.mem_singleton.mpr rfl) with ⟨one, two, same⟩ | ⟨pattern, same⟩
  · cases same
  · cases same

open KnowledgeTensorFirstOrderControls (plain) in
/-- **A counting check is no leaf at its footprint.** The firing `counts 2` is admitted at two
occurrences and refused at its footprint, which holds none. -/
theorem a_count_is_no_leaf_at_its_footprint :
    (Controls.counts 2).Valid plain Controls.five ⟨[], {0} ∪ {1}⟩ ∧
      ¬ (Controls.counts 2).Valid plain Controls.five
        (footprint ⟨[], {0} ∪ {1}⟩ (Controls.counts 2)) := by
  refine ⟨(Controls.counts_valid_iff 2 ({0} ∪ {1})).mpr (by decide), fun valid => ?_⟩
  have size := (Controls.counts_valid_iff 2
    (([] : List Nat).toFinset ∪ ([] : List Nat).toFinset)).mp valid
  exact absurd size (by decide)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.FirstOrder
