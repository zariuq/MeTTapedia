import Mettapedia.GSLT.LanguageDef.SupportRestrictedSourceViewCompilation

/-!
# Support-restricted finite source families

An ordered finite family of source terms may share one immutable environment
snapshot.  The snapshot retains exactly the distinct slots observed by at
least one family member, while the family itself remains an unquotiented list:
source order and duplicate occurrences are preserved.

This is the family form of support-restricted source-view compilation.  It is
independent of any scheduler or parallel realization.  Complete forcing of
the captured family agrees pointwise with complete forcing under the original
environment, and every individual member obtains the existing exact
one-layer source-view semantics.

The generated support is minimal under universal pointwise agreement.  If a
candidate representation omits one family-observable slot, an explicit
environment distinguishes it.  The result concerns logical support cells,
not byte-optimal layout or a permission to share mutable storage.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.SupportRestrictedSourceFamilyCompilation

open CompiledPlanAdmission
open CompiledPlanActivationViewCompilation
open CompiledPlanOpenActivationViewCompilation
open CompiledPlanTermSemantics
open DelayedSourceBindingCompilation
open FiniteEnvironmentCompilation
open SupportRestrictedSourceViewCompilation

universe uOwner uRevision

variable {Owner : Type uOwner} {Revision : Type uRevision}

/-! ## Ordered-family support -/

/-- Every variable-slot occurrence read by an ordered source family. -/
def familyUsedSlots (sources : List Term) : List UInt32 :=
  sources.flatMap usedSlots

/-- First-occurrence order of the distinct slots read by the family. -/
def familySupportKeys (sources : List Term) : List UInt32 :=
  (familyUsedSlots sources).dedup

theorem familySupportKeys_nodup (sources : List Term) :
    (familySupportKeys sources).Nodup := by
  exact List.nodup_dedup _

theorem mem_familySupportKeys_iff (slot : UInt32) (sources : List Term) :
    slot ∈ familySupportKeys sources ↔
      ∃ source ∈ sources, slot ∈ usedSlots source := by
  simp [familySupportKeys, familyUsedSlots]

/-- Dense family support removes repeated reads without quotienting sources. -/
def familySupportInventory (sources : List Term) : Inventory UInt32 where
  keys := familySupportKeys sources
  nodup := familySupportKeys_nodup sources

/-- The extensional set of all slots observable by the family. -/
def familySupport (sources : List Term) : Finset UInt32 :=
  (familyUsedSlots sources).toFinset

/-- A physical key set covers every environment observation of the family. -/
def CoversFamily (sources : List Term) (keys : Finset UInt32) : Prop :=
  familySupport sources ⊆ keys

theorem familySupportInventory_width_eq (sources : List Term) :
    (familySupportInventory sources).keys.length =
      (familySupport sources).card := by
  calc
    (familySupportInventory sources).keys.length =
        (familySupportKeys sources).toFinset.card :=
      (List.toFinset_card_of_nodup
        (familySupportKeys_nodup sources)).symm
    _ = (familySupport sources).card := by
      congr 1
      ext slot
      simp [familySupportKeys, familySupport, familyUsedSlots]

theorem familySupportInventory_width_minimal (sources : List Term)
    (candidate : Finset UInt32) (covers : CoversFamily sources candidate) :
    (familySupportInventory sources).keys.length ≤ candidate.card := by
  rw [familySupportInventory_width_eq]
  exact Finset.card_le_card covers

/-! ## Owned family snapshots -/

/-- One revision-pinned semantic environment with an ordered source family. -/
structure SourceFamilyView
    (Owner : Type uOwner) (Revision : Type uRevision) where
  owner : Owner
  revision : Revision
  generation : UInt32
  environment : OpenEnvironment
  sources : List Term

/-- Complete pointwise meaning of an ordered source family. -/
def SourceFamilyView.force
    (view : SourceFamilyView Owner Revision) : List OpenTerm :=
  view.sources.map
    (instantiateOpen view.generation view.environment)

/-- An immutable dense environment for exactly the family's support. -/
structure FamilySupportSnapshot
    (Owner : Type uOwner) (Revision : Type uRevision) where
  owner : Owner
  revision : Revision
  generation : UInt32
  sources : List Term
  slots : DenseEnvironment (familySupportInventory sources) OpenTerm

/-- Capture the union of the supports of all family occurrences. -/
def FamilySupportSnapshot.capture
    (view : SourceFamilyView Owner Revision) :
    FamilySupportSnapshot Owner Revision where
  owner := view.owner
  revision := view.revision
  generation := view.generation
  sources := view.sources
  slots := fun slot =>
    view.environment ((familySupportInventory view.sources).reify slot)

/-- Decode the owned dense family snapshot to the semantic interface. -/
def FamilySupportSnapshot.environment
    (snapshot : FamilySupportSnapshot Owner Revision) : OpenEnvironment :=
  decodeDense (familySupportInventory snapshot.sources) snapshot.slots

/-- Re-expose the snapshot as one semantic family view. -/
def FamilySupportSnapshot.toSourceFamilyView
    (snapshot : FamilySupportSnapshot Owner Revision) :
    SourceFamilyView Owner Revision where
  owner := snapshot.owner
  revision := snapshot.revision
  generation := snapshot.generation
  environment := snapshot.environment
  sources := snapshot.sources

/-- Re-expose one occurrence of the family through the existing source-view
coalgebra. -/
def FamilySupportSnapshot.toSourceView
    (snapshot : FamilySupportSnapshot Owner Revision) (source : Term) :
    SourceView Owner Revision where
  owner := snapshot.owner
  revision := snapshot.revision
  generation := snapshot.generation
  environment := snapshot.environment
  source := source

/-- Family capture agrees with the original environment on every slot read by
any particular family member. -/
theorem FamilySupportSnapshot.capture_agreesOn
    (view : SourceFamilyView Owner Revision)
    (source : Term) (member : source ∈ view.sources) :
    AgreesOn source view.environment
      (FamilySupportSnapshot.capture view).environment := by
  intro slot used
  have present :
      slot ∈ (familySupportInventory view.sources).keys := by
    exact (mem_familySupportKeys_iff slot view.sources).2
      ⟨source, member, used⟩
  obtain ⟨denseSlot, selected⟩ :=
    ((familySupportInventory view.sources).exists_resolve?_eq_some_iff slot).2
      present
  have reified :
      (familySupportInventory view.sources).reify denseSlot = slot :=
    ((familySupportInventory view.sources).resolve?_eq_some_iff
      slot denseSlot).1 selected
  simp [FamilySupportSnapshot.environment,
    FamilySupportSnapshot.capture, decodeDense, selected, reified]

/-- Every ordered family occurrence has exactly the same complete meaning
after support-restricted capture. -/
theorem FamilySupportSnapshot.capture_force_exact
    (view : SourceFamilyView Owner Revision) :
    (FamilySupportSnapshot.capture view).toSourceFamilyView.force =
      view.force := by
  simp only [SourceFamilyView.force,
    FamilySupportSnapshot.toSourceFamilyView,
    FamilySupportSnapshot.capture]
  apply List.map_congr_left
  intro source member
  exact (instantiateOpen_eq_of_agreesOn
    view.generation
    (FamilySupportSnapshot.capture view).environment
    view.environment source
    (fun slot used =>
      (FamilySupportSnapshot.capture_agreesOn view source member slot used).symm))

/-- Each captured family occurrence also retains exact direct one-layer
observation without reconstructing the other occurrences. -/
theorem FamilySupportSnapshot.capture_out_exact
    (view : SourceFamilyView Owner Revision)
    (source : Term) (member : source ∈ view.sources) :
    (outBinding
        (.delayed
          ((FamilySupportSnapshot.capture view).toSourceView source))).map
        (BindingValue.denote (Owner := Owner) (Revision := Revision)) =
      outOpen (instantiateOpen view.generation view.environment source) := by
  rw [outBinding_exact]
  congr 1
  exact instantiateOpen_eq_of_agreesOn view.generation
    (FamilySupportSnapshot.capture view).environment
    view.environment source
    (fun slot used =>
      (FamilySupportSnapshot.capture_agreesOn view source member slot used).symm)

/-! ## Exact family lower bound -/

/-- A candidate key set is universally adequate when restriction through it
preserves every observation of every family member. -/
def UniversallyFamilyAdequate (sources : List Term)
    (keys : Finset UInt32) : Prop :=
  ∀ environment source, source ∈ sources →
    AgreesOn source environment (restrictEnvironment keys environment)

theorem universallyFamilyAdequate_of_covers
    (sources : List Term) (keys : Finset UInt32)
    (covers : CoversFamily sources keys) :
    UniversallyFamilyAdequate sources keys := by
  intro environment source member slot used
  have retained : slot ∈ keys := covers (by
    simp only [familySupport, familyUsedSlots, List.mem_toFinset,
      List.mem_flatMap]
    exact ⟨source, member, used⟩)
  simp [restrictEnvironment, retained]

/-- Omitting one family-observable slot has an explicit distinguishing
environment and source occurrence. -/
theorem missing_family_support_slot_distinguishes
    (sources : List Term) (keys : Finset UInt32) (slot : UInt32)
    (used : ∃ source ∈ sources, slot ∈ usedSlots source)
    (missing : slot ∉ keys) :
    ∃ environment source, source ∈ sources ∧
      ¬ AgreesOn source environment
        (restrictEnvironment keys environment) := by
  obtain ⟨source, member, sourceUses⟩ := used
  obtain ⟨environment, distinguishes⟩ :=
    missing_support_slot_distinguishes
      source keys slot sourceUses missing
  exact ⟨environment, source, member, distinguishes⟩

theorem covers_of_universallyFamilyAdequate
    (sources : List Term) (keys : Finset UInt32)
    (adequate : UniversallyFamilyAdequate sources keys) :
    CoversFamily sources keys := by
  intro slot membership
  have used : ∃ source ∈ sources, slot ∈ usedSlots source := by
    simpa [familySupport, familyUsedSlots] using membership
  by_contra missing
  obtain ⟨environment, source, member, distinguishes⟩ :=
    missing_family_support_slot_distinguishes
      sources keys slot used missing
  exact distinguishes (adequate environment source member)

theorem universallyFamilyAdequate_iff_covers
    (sources : List Term) (keys : Finset UInt32) :
    UniversallyFamilyAdequate sources keys ↔ CoversFamily sources keys := by
  exact ⟨covers_of_universallyFamilyAdequate sources keys,
    universallyFamilyAdequate_of_covers sources keys⟩

theorem familySupportInventory_width_minimal_of_universal_agreement
    (sources : List Term) (candidate : Finset UInt32)
    (adequate : UniversallyFamilyAdequate sources candidate) :
    (familySupportInventory sources).keys.length ≤ candidate.card :=
  familySupportInventory_width_minimal sources candidate
    (covers_of_universallyFamilyAdequate sources candidate adequate)

/-! ## Positive and negative controls -/

namespace Canaries

private def before : OpenEnvironment
  | 0 => some (.integer 7)
  | 1 => some (.symbol [8])
  | _ => none

private def first : Term :=
  .application [1] (.cons (.variable 0) .nil)

private def second : Term :=
  .application [2]
    (.cons (.variable 1) (.cons (.variable 0) .nil))

private def family : SourceFamilyView Unit Nat where
  owner := ()
  revision := 11
  generation := 13
  environment := before
  sources := [first, first, second]

/-- Capture preserves source order and duplicate occurrences as well as
pointwise term meaning. -/
example :
    (FamilySupportSnapshot.capture family).toSourceFamilyView.force =
        family.force ∧
      family.sources.length = 3 ∧
      family.sources[0]? = family.sources[1]? := by
  refine ⟨FamilySupportSnapshot.capture_force_exact family, ?_⟩
  decide

/-- Repeated reads across repeated sources share two support cells rather
than allocating one cell per occurrence. -/
example : (familySupportInventory family.sources).keys.length = 2 := by
  norm_num [family, familySupportInventory, familySupportKeys,
    familyUsedSlots, first, second, usedSlots, usedSlotsTerms]
  decide

/-- Mutation of the borrowed environment can change family meaning, while an
already captured owned family remains unchanged. -/
example :
    let after := writeOpen before 0 (.integer 9)
    let borrowedAfter : SourceFamilyView Unit Nat :=
      { family with environment := after }
    (FamilySupportSnapshot.capture family).toSourceFamilyView.force =
        family.force ∧
      borrowedAfter.force ≠ family.force := by
  dsimp only
  constructor
  · exact FamilySupportSnapshot.capture_force_exact family
  · norm_num [SourceFamilyView.force, family, first, second, before,
      writeOpen, instantiateOpen, instantiateOpenTerms]
    decide

/-- An empty support cannot universally represent this non-closed family. -/
example : ¬ UniversallyFamilyAdequate family.sources ∅ := by
  intro adequate
  have covers :=
    covers_of_universallyFamilyAdequate family.sources ∅ adequate
  have retained : (0 : UInt32) ∈ (∅ : Finset UInt32) :=
    covers (by
      norm_num [familySupport, familyUsedSlots, family, first, second,
        usedSlots, usedSlotsTerms])
  simp at retained

end Canaries

#print axioms familySupportInventory_width_eq
#print axioms FamilySupportSnapshot.capture_agreesOn
#print axioms FamilySupportSnapshot.capture_force_exact
#print axioms FamilySupportSnapshot.capture_out_exact
#print axioms universallyFamilyAdequate_iff_covers
#print axioms familySupportInventory_width_minimal_of_universal_agreement

end Mettapedia.GSLT.LanguageDef.SupportRestrictedSourceFamilyCompilation
