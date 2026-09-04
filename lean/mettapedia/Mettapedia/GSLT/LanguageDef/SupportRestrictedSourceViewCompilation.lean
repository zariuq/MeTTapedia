import Mettapedia.GSLT.LanguageDef.DelayedSourceBindingCompilation

/-!
# Support-restricted source-view compilation

A delayed source view needs only the environment slots named by its source.
Retaining a pointer to a mutable environment is nevertheless unsound: a later
write to one of those slots can change the view's meaning, while rollback can
invalidate the physical state that pointer names.

This module compiles an immutable source view to a source-ordered dense
snapshot of exactly its distinct support keys.  Decoding that snapshot agrees
with the original environment on every observable slot, so complete forcing
and layerwise observation retain their existing semantics.

The support layout is minimal under the declared agreement contract.  Any
candidate key set that works for every environment must contain every distinct
source slot; omitting one has an explicit distinguishing environment.  This is
a key-count result, not a claim about byte-optimal physical encoding.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.SupportRestrictedSourceViewCompilation

open CompiledPlanAdmission
open CompiledPlanActivationViewCompilation
open CompiledPlanOpenActivationViewCompilation
open CompiledPlanTermSemantics
open DelayedSourceBindingCompilation
open FiniteEnvironmentCompilation

universe uOwner uRevision

variable {Owner : Type uOwner} {Revision : Type uRevision}

/-! ## Exact finite support -/

/-- Source-order support with repeated variable occurrences represented once. -/
def supportKeys (source : Term) : List UInt32 :=
  (usedSlots source).dedup

theorem supportKeys_nodup (source : Term) :
    (supportKeys source).Nodup := by
  exact List.nodup_dedup _

theorem mem_supportKeys_iff (slot : UInt32) (source : Term) :
    slot ∈ supportKeys source ↔ slot ∈ usedSlots source := by
  exact List.mem_dedup

/-- Dense slots retain first-occurrence source order while removing duplicate
reads of the same logical variable. -/
def supportInventory (source : Term) : Inventory UInt32 where
  keys := supportKeys source
  nodup := supportKeys_nodup source

/-- The extensional set of slots observable from a source. -/
def sourceSupport (source : Term) : Finset UInt32 :=
  (usedSlots source).toFinset

/-- A candidate physical key set covers every slot the source may observe. -/
def CoversSource (source : Term) (keys : Finset UInt32) : Prop :=
  sourceSupport source ⊆ keys

theorem supportInventory_width_eq (source : Term) :
    (supportInventory source).keys.length = (sourceSupport source).card := by
  calc
    (supportInventory source).keys.length =
        (supportKeys source).toFinset.card :=
      (List.toFinset_card_of_nodup (supportKeys_nodup source)).symm
    _ = (sourceSupport source).card := by
      congr 1
      ext slot
      simp [supportKeys, sourceSupport]

/-- The generated support has no avoidable key slots among representations
that promise pointwise agreement on every source-observable variable. -/
theorem supportInventory_width_minimal (source : Term)
    (candidate : Finset UInt32) (covers : CoversSource source candidate) :
    (supportInventory source).keys.length ≤ candidate.card := by
  rw [supportInventory_width_eq]
  exact Finset.card_le_card covers

/-! ## Owned dense snapshots -/

/-- An immutable dense snapshot owns values for precisely the generated source
support.  The dense environment is a value, not a borrowed mutable builder. -/
structure SupportSnapshot (Owner : Type uOwner) (Revision : Type uRevision) where
  owner : Owner
  revision : Revision
  generation : UInt32
  source : Term
  slots : DenseEnvironment (supportInventory source) OpenTerm

/-- Capture every source-observable value from one immutable semantic view. -/
def SupportSnapshot.capture (view : SourceView Owner Revision) :
    SupportSnapshot Owner Revision where
  owner := view.owner
  revision := view.revision
  generation := view.generation
  source := view.source
  slots := fun slot => view.environment ((supportInventory view.source).reify slot)

/-- Decode the owned dense snapshot to the semantic environment interface. -/
def SupportSnapshot.environment (snapshot : SupportSnapshot Owner Revision) :
    OpenEnvironment :=
  decodeDense (supportInventory snapshot.source) snapshot.slots

/-- Re-expose an owned snapshot through the generic source-view semantics. -/
def SupportSnapshot.toSourceView
    (snapshot : SupportSnapshot Owner Revision) : SourceView Owner Revision where
  owner := snapshot.owner
  revision := snapshot.revision
  generation := snapshot.generation
  environment := snapshot.environment
  source := snapshot.source

/-- Dense capture agrees with the original environment on every slot the
source can inspect. -/
theorem SupportSnapshot.capture_agreesOn (view : SourceView Owner Revision) :
    AgreesOn view.source view.environment (SupportSnapshot.capture view).environment := by
  intro slot member
  have present : slot ∈ (supportInventory view.source).keys := by
    exact (mem_supportKeys_iff slot view.source).2 member
  obtain ⟨denseSlot, selected⟩ :=
    ((supportInventory view.source).exists_resolve?_eq_some_iff slot).2 present
  have reified : (supportInventory view.source).reify denseSlot = slot :=
    ((supportInventory view.source).resolve?_eq_some_iff slot denseSlot).1 selected
  simp [SupportSnapshot.environment, SupportSnapshot.capture, decodeDense,
    selected, reified]

/-- Capturing only the source support preserves complete term meaning. -/
theorem SupportSnapshot.capture_force_exact
    (view : SourceView Owner Revision) :
    (SupportSnapshot.capture view).toSourceView.force = view.force := by
  symm
  exact SourceView.force_eq_of_agreesOn view
    (SupportSnapshot.capture view).toSourceView rfl rfl
    (SupportSnapshot.capture_agreesOn view)

/-- Direct one-layer observation of the captured view remains exact without
reconstructing the complete term. -/
theorem SupportSnapshot.capture_out_exact
    (view : SourceView Owner Revision) :
    (outBinding (.delayed (SupportSnapshot.capture view).toSourceView)).map
        (BindingValue.denote (Owner := Owner) (Revision := Revision)) =
      outOpen view.force := by
  rw [outBinding_exact]
  exact congrArg outOpen (SupportSnapshot.capture_force_exact view)

/-! ## The exact lower bound and its negative witness -/

/-- Project an environment through an arbitrary retained key set. -/
def restrictEnvironment (keys : Finset UInt32)
    (environment : OpenEnvironment) : OpenEnvironment :=
  fun slot => if slot ∈ keys then environment slot else none

/-- A key set is universally agreement-adequate when restricting through it
preserves every environment on the source's observable support. -/
def UniversallyAgreementAdequate (source : Term)
    (keys : Finset UInt32) : Prop :=
  ∀ environment, AgreesOn source environment
    (restrictEnvironment keys environment)

theorem universallyAgreementAdequate_of_covers
    (source : Term) (keys : Finset UInt32)
    (covers : CoversSource source keys) :
    UniversallyAgreementAdequate source keys := by
  intro environment slot member
  have retained : slot ∈ keys := covers (by simpa [sourceSupport] using member)
  simp [restrictEnvironment, retained]

/-- If one observable slot is omitted, a single bound value distinguishes the
projected environment from the source environment. -/
theorem missing_support_slot_distinguishes
    (source : Term) (keys : Finset UInt32) (slot : UInt32)
    (used : slot ∈ usedSlots source) (missing : slot ∉ keys) :
    ∃ environment, ¬ AgreesOn source environment
      (restrictEnvironment keys environment) := by
  let environment : OpenEnvironment :=
    writeOpen emptyOpenEnvironment slot (.symbol [1])
  refine ⟨environment, ?_⟩
  intro agrees
  have same := agrees slot used
  simp [environment, writeOpen, restrictEnvironment, missing] at same

theorem covers_of_universallyAgreementAdequate
    (source : Term) (keys : Finset UInt32)
    (adequate : UniversallyAgreementAdequate source keys) :
    CoversSource source keys := by
  intro slot membership
  have used : slot ∈ usedSlots source := by
    simpa [sourceSupport] using membership
  by_contra missing
  obtain ⟨environment, distinguishes⟩ :=
    missing_support_slot_distinguishes source keys slot used missing
  exact distinguishes (adequate environment)

theorem universallyAgreementAdequate_iff_covers
    (source : Term) (keys : Finset UInt32) :
    UniversallyAgreementAdequate source keys ↔ CoversSource source keys := by
  exact ⟨covers_of_universallyAgreementAdequate source keys,
    universallyAgreementAdequate_of_covers source keys⟩

/-- Consequently every universally exact support projection needs at least as
many distinct keys as the generated source support. -/
theorem supportInventory_width_minimal_of_universal_agreement
    (source : Term) (candidate : Finset UInt32)
    (adequate : UniversallyAgreementAdequate source candidate) :
    (supportInventory source).keys.length ≤ candidate.card :=
  supportInventory_width_minimal source candidate
    (covers_of_universallyAgreementAdequate source candidate adequate)

/-! ## Positive and negative controls -/

namespace Canaries

private def before : OpenEnvironment
  | 0 => some (.symbol [9])
  | _ => none

private def source : Term :=
  .application [1]
    (.cons (.variable 0)
      (.cons (.application [2] (.cons (.variable 0) .nil)) .nil))

private def view : SourceView Unit Nat :=
  { owner := (), revision := 5, generation := 7, environment := before, source }

/-- Repeated uses of one slot occupy one dense support cell and retain exact
meaning. -/
example :
    (supportInventory source).keys.length = 1 ∧
      (SupportSnapshot.capture view).toSourceView.force = view.force := by
  constructor
  · norm_num [supportInventory, supportKeys, source, usedSlots, usedSlotsTerms]
  · exact SupportSnapshot.capture_force_exact view

/-- A later write to the original mutable environment changes a borrowed view
but cannot change the already captured owned snapshot. -/
example :
    let after := writeOpen before 0 (.symbol [10])
    let borrowedAfter : SourceView Unit Nat := { view with environment := after }
    (SupportSnapshot.capture view).toSourceView.force = view.force ∧
      borrowedAfter.force ≠ view.force := by
  dsimp only
  constructor
  · exact SupportSnapshot.capture_force_exact view
  · norm_num [SourceView.force, view, source, before,
      writeOpen, instantiateOpen, instantiateOpenTerms]
    decide

/-- The empty key set cannot represent a source that observes slot zero for
all environments. -/
example : ¬ UniversallyAgreementAdequate source ∅ := by
  intro adequate
  have covers := covers_of_universallyAgreementAdequate source ∅ adequate
  have retained : (0 : UInt32) ∈ (∅ : Finset UInt32) :=
    covers (by
      norm_num [sourceSupport, source, usedSlots, usedSlotsTerms])
  simp at retained

end Canaries

#print axioms supportInventory_width_eq
#print axioms SupportSnapshot.capture_agreesOn
#print axioms SupportSnapshot.capture_force_exact
#print axioms SupportSnapshot.capture_out_exact
#print axioms universallyAgreementAdequate_iff_covers
#print axioms supportInventory_width_minimal_of_universal_agreement

end Mettapedia.GSLT.LanguageDef.SupportRestrictedSourceViewCompilation
