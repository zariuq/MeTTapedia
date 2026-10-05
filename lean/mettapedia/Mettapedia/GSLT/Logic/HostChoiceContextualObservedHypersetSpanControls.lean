import Mettapedia.GSLT.Logic.HostChoiceContextualObservedHypersetHistory
import Mettapedia.GSLT.Logic.HostChoiceContextualObservedHypersetControls

/-!
# Infinite history, predecessor and receipt controls for the joined model

The predecessor negative uses the declared future-only profile whose atoms
are all zero. Task and result have the same full structured observation in
that profile, yet their actual executable predecessor boxes differ. This
does not identify result and fault under a profile that observes them.

Actual typed receipt copies have equal labelled endpoints and different
continuations. Their original-bound dependent body has an inhabited fibre
at one copy and an empty fibre at the other, so endpoint erasure cannot
replace the full receipt family. The same infinite history site also has
an actual material member family that becomes inhabited after an authored
script arrow. No occurrence inverse is extracted from modal endpoint laws.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Mettapedia.GSLT.HostChoiceContextualObservedHypersetSpanControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open HostChoiceContextualSetInterpretation HostChoiceContextualSetInterpretation.Finality
open HostChoiceContextualObservedHypersetTriangle
open HennessyMilner ObservationSpans ObservedMaterialization
open Mettapedia.OSLF.Framework.DerivedModalities
open Distinction.HistoryGrammar Distinction.HistoryContextCategory Distinction.HistoryContextTwoSided
open Distinction.HistoryObserver (Reading NodeReadings reading)
open Distinction.HistoryCoverageControls (Node grammar scale readings listing)
open Distinction.HistoryContextControls (nodeCoding integerCoding zeroReadings zero_reading notSingle)


abbrev coarse := futureOnly grammar
abbrev coarseAtoms := observes (G := grammar) scale zeroReadings
abbrev exactAtoms := observes (G := grammar) scale readings

noncomputable abbrev coarseRead (point : World grammar) :=
  HostChoiceContextualObservedHypersetHistory.freshRead coarse coarseAtoms nodeCoding listing (atomCoding integerCoding) point

theorem coarse_kernel (point : World grammar) (left right : Multiset Node) :
    coarseRead point left = coarseRead point right ↔ Multiset.card left = Multiset.card right :=
  (HostChoiceContextualObservedHypersetHistory.fresh_kernel coarse coarseAtoms nodeCoding listing (atomCoding integerCoding) point left right).trans
    (Distinction.HistoryContextControls.futureOnly_fresh_observed_iff scale zeroReadings
      (fun observation first second _ => (zero_reading observation first).trans (zero_reading observation second).symm)
      point left right)

theorem coarse_task_result_equal (point : World grammar) :
    coarseRead point (Node.task ::ₘ 0) = coarseRead point (Node.done ::ₘ 0) :=
  (coarse_kernel point _ _).mpr rfl

theorem notSingle_descends (point : World grammar) : PredicateDescends (coarseRead point) notSingle := by
  rw [predicateDescends_iff]
  intro first second same
  apply propext
  unfold notSingle
  rw [(coarse_kernel point first second).mp same]

theorem predecessor_box_does_not_descend (point : World grammar) :
    ¬ PredicateDescends (coarseRead point) (derivedBox (eventSpan grammar) notSingle) := by
  rintro ⟨observed, truth⟩
  have past := (truth (Node.task ::ₘ 0)).mpr Distinction.HistoryContextControls.box_task
  rw [coarse_task_result_equal point] at past
  exact Distinction.HistoryContextControls.not_box_done ((truth (Node.done ::ₘ 0)).mp past)

theorem incoming_matching_fails (point : World grammar) :
    ¬ PastMatching (eventSpan grammar) (HostChoiceContextualObservedHypersetSpans.Retained.kernel (coarseRead point)) := by
  intro matching
  exact predecessor_box_does_not_descend point
    ((HostChoiceContextualObservedHypersetSpans.Retained.map (eventSpan grammar) (coarseRead point)).box_descends
      ((HostChoiceContextualObservedHypersetSpans.Retained.targetLifts_iff _ _).mpr matching) notSingle (notSingle_descends point))

theorem actual_native_formula_descends (formula : Formula (Reading × ℤ) (ContextualCoalgebraLabelledGraph.Label (World grammar))) :
    PredicateDescends (HostChoiceContextualObservedHypersetSpans.packedReadout (coalgebra coarse) coarseAtoms (worldCoding grammar)
      (arrowCoding nodeCoding listing) (atomCoding integerCoding))
      (Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes.formulaPredicate
        (ContextualObservedCoalgebra.system (coalgebra coarse) coarseAtoms) formula) :=
  HostChoiceContextualObservedHypersetSpans.native_formula_descends _ _ _ _ _ formula

/-! ## Receipt-sensitive continuations over equal endpoints -/

abbrev firstWorld : World grammar := ⟨1⟩

def taggedReceipt (copy : Bool) : HostChoiceContextualObservedHypersetHistory.Receipt (exact grammar) firstWorld where
  source := Distinction.HistoryContextControls.pendingEvolution grammar .task .forward
  target := fresh firstWorld (.done ::ₘ 0)
  written := (.forward, .evolve .task)
  actual := (.forward, .evolve .task)
  rest := []
  copy := copy
  script := rfl
  admitted := rfl
  moves := ⟨0, rfl, rfl⟩
  origin := rfl
  residual := rfl

noncomputable abbrev receiptFamily := HostChoiceContextualObservedHypersetHistory.structuredReceiptFamily (exact grammar) exactAtoms nodeCoding listing
  (atomCoding integerCoding)

noncomputable abbrev receiptEndpoints := HostChoiceContextualObservedHypersetReceipts.endpoints (coalgebra (exact grammar)) exactAtoms (worldCoding grammar)
  (arrowCoding nodeCoding listing) (atomCoding integerCoding) (HostChoiceContextualObservedHypersetHistory.sourceEndpoint (exact grammar)) (HostChoiceContextualObservedHypersetHistory.targetEndpoint (exact grammar))

noncomputable def receiptPoint : (HostChoiceContextualObservedHypersetReceipts.endpointPairs (coalgebra (exact grammar)) exactAtoms (worldCoding grammar)
    (arrowCoding nodeCoding listing) (atomCoding integerCoding)).Elements :=
  ⟨firstWorld, receiptEndpoints.app firstWorld (taggedReceipt false)⟩

noncomputable def receiptCode (copy : Bool) : receiptFamily.obj receiptPoint := ⟨taggedReceipt copy, rfl⟩

theorem receipt_copies_differ : receiptCode false ≠ receiptCode true := by
  intro same
  exact Bool.false_ne_true (congrArg (fun receipt => receipt.val.copy) same)

theorem same_observed_endpoints : receiptEndpoints.app firstWorld (taggedReceipt false) =
    receiptEndpoints.app firstWorld (taggedReceipt true) := rfl

theorem receipt_continuation_no_endpoint_factor :
    ¬ ∃ consumer : NaturalHom (HostChoiceContextualObservedHypersetReceipts.endpointPairs (coalgebra (exact grammar)) exactAtoms (worldCoding grammar)
        (arrowCoding nodeCoding listing) (atomCoding integerCoding)) (HostChoiceContextualObservedHypersetHistory.copyFamily (G := grammar)),
      receiptEndpoints.comp consumer = HostChoiceContextualObservedHypersetHistory.copyReading (exact grammar) := by
  rintro ⟨consumer, factors⟩
  have first := congrArg (fun map : NaturalHom (HostChoiceContextualObservedHypersetHistory.eventFamily (exact grammar)) (HostChoiceContextualObservedHypersetHistory.copyFamily (G := grammar)) =>
    map.app firstWorld (taggedReceipt false)) factors
  have second := congrArg (fun map : NaturalHom (HostChoiceContextualObservedHypersetHistory.eventFamily (exact grammar)) (HostChoiceContextualObservedHypersetHistory.copyFamily (G := grammar)) =>
    map.app firstWorld (taggedReceipt true)) factors
  exact Bool.false_ne_true (first.symm.trans (second))

noncomputable def receiptBody : receiptFamily.Elements ⥤ Type where
  obj point := {_unit : PUnit.{1} // point.2.val.copy = false}
  map {first second} step := TypeCat.ofHom fun value => ⟨value.val, by
    have saved := congrArg (fun receipt => receipt.val.copy) step.2
    change first.2.val.copy = second.2.val.copy at saved
    exact saved ▸ value.property⟩
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro value
    exact Subtype.ext rfl
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro value
    exact Subtype.ext rfl

theorem receipt_body_varies :
    Nonempty (receiptBody.obj ⟨receiptPoint, receiptCode false⟩) ∧
      ¬ Nonempty (receiptBody.obj ⟨receiptPoint, receiptCode true⟩) :=
  ⟨⟨⟨PUnit.unit, rfl⟩⟩, fun ⟨value⟩ => Bool.false_ne_true value.property.symm⟩

theorem receipt_sum_inhabited : Nonempty ((ContextualSmallFamilyTypeFormers.sigma receiptFamily receiptBody).obj receiptPoint) :=
  ⟨⟨receiptCode false, ⟨PUnit.unit, rfl⟩⟩⟩

theorem receipt_full_product_empty : ¬ Nonempty ((ContextualSmallFamilyTypeFormers.pi receiptFamily receiptBody).obj receiptPoint) := by
  rintro ⟨function⟩
  exact receipt_body_varies.2 ⟨ContextualSmallFamilyTypeFormers.evaluateValue receiptFamily receiptBody
    receiptPoint function (receiptCode true)⟩

theorem receipt_full_native_empty :
    ¬ Nonempty (WiderPresheafDependentFunctions.DependentSection receiptFamily receiptBody receiptPoint) := by
  rintro ⟨function⟩
  exact receipt_full_product_empty ⟨ContextualSmallFamilyNativeAdjunction.nativeSmallEquiv receiptFamily receiptBody receiptPoint function⟩

theorem receipt_comprehension_retains_copy (copy : Bool) :
    ((HostChoiceContextualObservedHypersetReceipts.comprehensionBackward (coalgebra (exact grammar)) exactAtoms (worldCoding grammar)
      (arrowCoding nodeCoding listing) (atomCoding integerCoding) (HostChoiceContextualObservedHypersetHistory.sourceEndpoint (exact grammar))
      (HostChoiceContextualObservedHypersetHistory.targetEndpoint (exact grammar))).app firstWorld
        ((HostChoiceContextualObservedHypersetReceipts.comprehensionForward (coalgebra (exact grammar)) exactAtoms (worldCoding grammar)
          (arrowCoding nodeCoding listing) (atomCoding integerCoding) (HostChoiceContextualObservedHypersetHistory.sourceEndpoint (exact grammar))
          (HostChoiceContextualObservedHypersetHistory.targetEndpoint (exact grammar))).app firstWorld (taggedReceipt copy))).copy = copy := rfl

/-! ## Actual changing material members on the infinite history site -/

abbrev oldWorld : World grammar := ⟨0⟩
abbrev runTask := entryArrow oldWorld (.forward, .evolve .task)
abbrev oldTask : Placed oldWorld := fresh oldWorld (.task ::ₘ 0)
abbrev pendingTask : Placed (next oldWorld) := transport runTask oldTask
abbrev finishedTask : Placed (next oldWorld) := fresh (next oldWorld) (.done ::ₘ 0)

def duplicateContextEvent (copy : Bool) : ActionOccurrences.Event (HostChoiceContextualObservedHypersetHistory.authoredOccurrences (exact grammar) exactAtoms) :=
  ⟨.context oldWorld oldWorld (𝟙 oldWorld), ⟨oldWorld, oldTask⟩, ⟨oldWorld, oldTask⟩,
    (⟨oldTask, rfl, congrArg (Sigma.mk oldWorld) (transport_id oldTask).symm⟩, copy)⟩

def copyCoding : ArgumentCoding Bool := comapCoding natCoding (fun tag => if tag then 1 else 0) (by decide)

def unitCoding : ArgumentCoding PUnit where
  graph _ := AccessiblePointedGraph.empty
  injective _ _ _ := Subsingleton.elim _ _

theorem declared_receipt_fingerprint_separates :
    HostChoiceContextualObservedHypersetSpans.eventFingerprint (coalgebra (exact grammar)) exactAtoms (worldCoding grammar) (arrowCoding nodeCoding listing)
        (atomCoding integerCoding) (HostChoiceContextualObservedHypersetHistory.authoredOccurrences (exact grammar) exactAtoms)
        (HostChoiceContextualObservedHypersetHistory.occurrenceCopy (exact grammar) exactAtoms) copyCoding (duplicateContextEvent false) ≠
      HostChoiceContextualObservedHypersetSpans.eventFingerprint (coalgebra (exact grammar)) exactAtoms (worldCoding grammar) (arrowCoding nodeCoding listing)
        (atomCoding integerCoding) (HostChoiceContextualObservedHypersetHistory.authoredOccurrences (exact grammar) exactAtoms)
        (HostChoiceContextualObservedHypersetHistory.occurrenceCopy (exact grammar) exactAtoms) copyCoding (duplicateContextEvent true) := by
  intro same
  exact Bool.false_ne_true ((HostChoiceContextualObservedHypersetSpans.eventFingerprint_kernel _ _ _ _ _ _ _ _ _ _).mp same).2.1

theorem label_and_endpoints_alone_forget_copy :
    HostChoiceContextualObservedHypersetSpans.eventFingerprint (coalgebra (exact grammar)) exactAtoms (worldCoding grammar) (arrowCoding nodeCoding listing)
        (atomCoding integerCoding) (HostChoiceContextualObservedHypersetHistory.authoredOccurrences (exact grammar) exactAtoms)
        (fun _ => PUnit.unit) unitCoding (duplicateContextEvent false) =
      HostChoiceContextualObservedHypersetSpans.eventFingerprint (coalgebra (exact grammar)) exactAtoms (worldCoding grammar) (arrowCoding nodeCoding listing)
        (atomCoding integerCoding) (HostChoiceContextualObservedHypersetHistory.authoredOccurrences (exact grammar) exactAtoms)
        (fun _ => PUnit.unit) unitCoding (duplicateContextEvent true) := rfl

theorem erased_receipt_test_does_not_descend :
    ¬ PredicateDescends
      (HostChoiceContextualObservedHypersetSpans.eventFingerprint (coalgebra (exact grammar)) exactAtoms (worldCoding grammar) (arrowCoding nodeCoding listing)
        (atomCoding integerCoding) (HostChoiceContextualObservedHypersetHistory.authoredOccurrences (exact grammar) exactAtoms)
        (fun _ => PUnit.unit) unitCoding)
      (fun event => HostChoiceContextualObservedHypersetHistory.occurrenceCopy (exact grammar) exactAtoms event = false) := by
  rintro ⟨predicate, truth⟩
  have holds := (truth (duplicateContextEvent false)).mpr rfl
  rw [label_and_endpoints_alone_forget_copy] at holds
  exact Bool.false_ne_true ((truth (duplicateContextEvent true)).mp holds).symm

theorem no_current_children_fresh (point : World grammar) (live : Multiset Node) (child : Placed point) :
    ¬ ((coalgebra (exact grammar)).app point (fresh point live)).val.holds ⟨⟨point, 𝟙 point⟩, child⟩ := by
  intro available
  change Advances (exact grammar) (transport (𝟙 point) (fresh point live)) child at available
  rw [transport_id] at available
  obtain ⟨written, actual, rest, script, _⟩ := available
  change ([] : List (Entry Node)) = written :: rest at script
  cases script

theorem fresh_set_has_no_current_member (point : World grammar) (live : Multiset Node) (child : sets.obj point) :
    ¬ Member point child ((setReadout (coalgebra (exact grammar))).app point (fresh point live)) := by
  intro available
  obtain ⟨original, _, admitted⟩ := (setReadout_future (coalgebra (exact grammar)) point point (𝟙 point) _ child).mp available
  exact no_current_children_fresh point live original admitted

theorem pending_task_admits_result :
    ((coalgebra (exact grammar)).app (next oldWorld) pendingTask).val.holds
      ⟨⟨next oldWorld, 𝟙 (next oldWorld)⟩, finishedTask⟩ := by
  change Advances (exact grammar) (transport (𝟙 (next oldWorld)) pendingTask) finishedTask
  rw [transport_id]
  exact ⟨(.forward, .evolve .task), (.forward, .evolve .task), [], rfl, rfl, ⟨0, rfl, rfl⟩, rfl, rfl⟩

theorem pending_set_has_actual_member :
    Member (next oldWorld) ((setReadout (coalgebra (exact grammar))).app (next oldWorld) finishedTask)
      ((setReadout (coalgebra (exact grammar))).app (next oldWorld) pendingTask) :=
  (setReadout_future (coalgebra (exact grammar)) (next oldWorld) (next oldWorld) (𝟙 (next oldWorld)) _ _).mpr
    ⟨finishedTask, rfl, pending_task_admits_result⟩

noncomputable abbrev exactRead := HostChoiceContextualObservedHypersetHistory.structuredRead (exact grammar) exactAtoms nodeCoding listing (atomCoding integerCoding)
noncomputable def oldParameter : (HostChoiceContextualObservedHypersetTypes.parameters (coalgebra (exact grammar)) exactAtoms (worldCoding grammar)
    (arrowCoding nodeCoding listing) (atomCoding integerCoding)).Elements := ⟨oldWorld, exactRead.app oldWorld oldTask⟩
noncomputable def newParameter : (HostChoiceContextualObservedHypersetTypes.parameters (coalgebra (exact grammar)) exactAtoms (worldCoding grammar)
    (arrowCoding nodeCoding listing) (atomCoding integerCoding)).Elements :=
  ⟨next oldWorld, exactRead.app (next oldWorld) pendingTask⟩

noncomputable def actualMemberFamily := HostChoiceContextualObservedHypersetTypes.members (coalgebra (exact grammar)) exactAtoms (worldCoding grammar)
  (arrowCoding nodeCoding listing) (atomCoding integerCoding)

theorem actual_member_family_changes : ¬ Nonempty (actualMemberFamily.obj oldParameter) ∧
    Nonempty (actualMemberFamily.obj newParameter) := by
  constructor
  · rintro ⟨code⟩
    let literal := HostChoiceContextualObservedHypersetTypes.actualMembers (coalgebra (exact grammar)) exactAtoms (worldCoding grammar)
      (arrowCoding nodeCoding listing) (atomCoding integerCoding) oldParameter code
    have same := congrArg (fun map => map.app oldWorld oldTask)
      (structured_material_square (coalgebra (exact grammar)) exactAtoms (worldCoding grammar)
        (arrowCoding nodeCoding listing) (atomCoding integerCoding))
    have member := literal.property
    change Member oldWorld literal.val (exactRead.app oldWorld oldTask).2 at member
    change (exactRead.app oldWorld oldTask).2 =
      (setReadout (coalgebra (exact grammar))).app oldWorld oldTask at same
    exact fresh_set_has_no_current_member oldWorld (.task ::ₘ 0) literal.val
      (Eq.mp (congrArg (fun parent : sets.obj oldWorld => Member oldWorld literal.val parent) same) member)
  · apply Nonempty.map (HostChoiceContextualObservedHypersetTypes.actualMembers (coalgebra (exact grammar)) exactAtoms (worldCoding grammar)
      (arrowCoding nodeCoding listing) (atomCoding integerCoding) newParameter).symm
    refine ⟨⟨(setReadout (coalgebra (exact grammar))).app (next oldWorld) finishedTask, ?_⟩⟩
    have same := congrArg (fun map => map.app (next oldWorld) pendingTask)
      (structured_material_square (coalgebra (exact grammar)) exactAtoms (worldCoding grammar)
        (arrowCoding nodeCoding listing) (atomCoding integerCoding))
    change Member (next oldWorld) _ (exactRead.app (next oldWorld) pendingTask).2
    change (exactRead.app (next oldWorld) pendingTask).2 =
      (setReadout (coalgebra (exact grammar))).app (next oldWorld) pendingTask at same
    exact Eq.mpr (congrArg (fun parent : sets.obj (next oldWorld) =>
      Member (next oldWorld) ((setReadout (coalgebra (exact grammar))).app (next oldWorld) finishedTask) parent) same)
      pending_set_has_actual_member


/-- The exact observed class still erases a pending direction that no future
result test distinguishes. Its authored script continuation remains data. -/
theorem provenance_no_structured_factor :
    ¬ ∃ consumer : NaturalHom
        (structured (coalgebra (exact grammar)) exactAtoms (worldCoding grammar)
          (arrowCoding nodeCoding listing) (atomCoding integerCoding))
        (Distinction.HistoryContextControls.pendingScripts grammar),
      exactRead.comp consumer = Distinction.HistoryContextControls.provenance grammar := by
  rintro ⟨consumer, factors⟩
  have aliases := (structured_kernel (coalgebra (exact grammar)) exactAtoms (worldCoding grammar)
    (arrowCoding nodeCoding listing) (atomCoding integerCoding) firstWorld
    (Distinction.HistoryContextControls.pendingEvolution grammar .done .forward)
    (Distinction.HistoryContextControls.pendingEvolution grammar .done .backward)).mpr
      (Distinction.HistoryContextControls.fixed_evolution_observed grammar scale readings (x := .done) rfl)
  have first := congrArg (fun map : NaturalHom (placed grammar)
      (Distinction.HistoryContextControls.pendingScripts grammar) =>
    map.app firstWorld (Distinction.HistoryContextControls.pendingEvolution grammar .done .forward)) factors
  have second := congrArg (fun map : NaturalHom (placed grammar)
      (Distinction.HistoryContextControls.pendingScripts grammar) =>
    map.app firstWorld (Distinction.HistoryContextControls.pendingEvolution grammar .done .backward)) factors
  have scripts := congrArg Distinction.HistoryContextControls.Pending.script
    (first.symm.trans ((congrArg (consumer.app firstWorld) aliases).trans second))
  change [((.forward : Direction), Event.evolve Node.done)] =
    [((.backward : Direction), Event.evolve Node.done)] at scripts
  cases scripts

/-- This is an authored, nonidentity substitution in the same parameter
presheaf used by the actual member family. -/
noncomputable def runParameter : oldParameter ⟶ newParameter :=
  CategoryOfElements.homMk oldParameter newParameter runTask (exactRead.naturality runTask oldTask)

noncomputable def resultCode : actualMemberFamily.obj newParameter :=
  (HostChoiceContextualObservedHypersetTypes.actualMembers (coalgebra (exact grammar)) exactAtoms
    (worldCoding grammar) (arrowCoding nodeCoding listing) (atomCoding integerCoding) newParameter).symm
      ⟨(setReadout (coalgebra (exact grammar))).app (next oldWorld) finishedTask, by
        have same := congrArg (fun map => map.app (next oldWorld) pendingTask)
          (structured_material_square (coalgebra (exact grammar)) exactAtoms (worldCoding grammar)
            (arrowCoding nodeCoding listing) (atomCoding integerCoding))
        change (exactRead.app (next oldWorld) pendingTask).2 =
          (setReadout (coalgebra (exact grammar))).app (next oldWorld) pendingTask at same
        exact Eq.mpr (congrArg (fun parent : sets.obj (next oldWorld) =>
          Member (next oldWorld) ((setReadout (coalgebra (exact grammar))).app (next oldWorld) finishedTask) parent) same)
          pending_set_has_actual_member⟩

noncomputable abbrev actualSelectedBody := HostChoiceContextualObservedHypersetTypes.selectedBody
  (coalgebra (exact grammar)) exactAtoms (worldCoding grammar) (arrowCoding nodeCoding listing) (atomCoding integerCoding)

noncomputable abbrev actualSelectedMap := HostChoiceContextualObservedHypersetTypes.selectedSet
  (coalgebra (exact grammar)) exactAtoms (worldCoding grammar) (arrowCoding nodeCoding listing) (atomCoding integerCoding)

noncomputable abbrev actualParent := HostChoiceContextualObservedHypersetTypes.parent
  (coalgebra (exact grammar)) exactAtoms (worldCoding grammar) (arrowCoding nodeCoding listing) (atomCoding integerCoding)

theorem resultCode_value :
    (HostChoiceContextualObservedHypersetTypes.actualMembers (coalgebra (exact grammar)) exactAtoms
      (worldCoding grammar) (arrowCoding nodeCoding listing) (atomCoding integerCoding) newParameter resultCode).val =
        (setReadout (coalgebra (exact grammar))).app (next oldWorld) finishedTask :=
  congrArg Subtype.val ((HostChoiceContextualObservedHypersetTypes.actualMembers (coalgebra (exact grammar)) exactAtoms
    (worldCoding grammar) (arrowCoding nodeCoding listing) (atomCoding integerCoding) newParameter).apply_symm_apply _)

theorem selected_result_body_empty : ¬ Nonempty (actualSelectedBody.obj ⟨newParameter, resultCode⟩) := by
  rintro ⟨code⟩
  have available := (HostChoiceContextualHypersetFamilyClosure.bodyDecoder actualParent actualSelectedMap
    ⟨newParameter, resultCode⟩ code).property
  change Member (next oldWorld) _
    (HostChoiceContextualObservedHypersetTypes.actualMembers (coalgebra (exact grammar)) exactAtoms
      (worldCoding grammar) (arrowCoding nodeCoding listing) (atomCoding integerCoding) newParameter resultCode).val at available
  exact fresh_set_has_no_current_member (next oldWorld) (.done ::ₘ 0) _
    (Eq.mp (congrArg (fun parent : sets.obj (next oldWorld) => Member (next oldWorld)
      (HostChoiceContextualHypersetFamilyClosure.bodyDecoder actualParent actualSelectedMap
        ⟨newParameter, resultCode⟩ code).val parent) resultCode_value) available)

theorem all_present_arguments_have_results :
    ∀ argument : actualMemberFamily.obj oldParameter,
      Nonempty (actualSelectedBody.obj ⟨oldParameter, argument⟩) := by
  intro argument
  exact False.elim (actual_member_family_changes.1 ⟨argument⟩)

/-- The future result argument is real and its selected member body is empty.
Consequently the complete native product is empty at the earlier point,
even though every present argument admits a result. -/
theorem actual_full_future_product_empty :
    ¬ Nonempty ((ContextualSmallFamilyTypeFormers.pi actualMemberFamily actualSelectedBody).obj oldParameter) := by
  rintro ⟨function⟩
  exact selected_result_body_empty ⟨ContextualSmallFamilyTypeFormers.evaluateValue actualMemberFamily actualSelectedBody
    newParameter ((ContextualSmallFamilyTypeFormers.pi actualMemberFamily actualSelectedBody).map runParameter function) resultCode⟩

theorem actual_native_full_future_product_empty :
    ¬ Nonempty (WiderPresheafDependentFunctions.DependentSection actualMemberFamily actualSelectedBody oldParameter) := by
  rintro ⟨function⟩
  exact actual_full_future_product_empty
    ⟨ContextualSmallFamilyNativeAdjunction.nativeSmallEquiv actualMemberFamily actualSelectedBody oldParameter function⟩

section NonidentityContext

open Distinction.HistoryObserverControls (swapGrammar)

def swapAtoms (tag : Bool) (state : ContextualCoalgebraLabelledGraph.State (placed swapGrammar)) : Prop :=
  tag ∈ state.2.live

noncomputable abbrev swapFace := structured (coalgebra (exact swapGrammar)) swapAtoms (worldCoding swapGrammar)
  (arrowCoding copyCoding Distinction.HistoryCoverageControls.boolListing) copyCoding

noncomputable abbrev swapRead (point : World swapGrammar) := HostChoiceContextualObservedHypersetHistory.freshRead (exact swapGrammar) swapAtoms copyCoding
  Distinction.HistoryCoverageControls.boolListing copyCoding point

abbrev swapContext := Context.ofRenaming Distinction.HistoryContextControls.swapRenaming

theorem actual_swap_changes_state : swapContext.apply (true ::ₘ 0) ≠ (true ::ₘ 0) := by
  change (false ::ₘ 0) + (0 : Multiset Bool) ≠ true ::ₘ 0
  rw [Multiset.add_zero]
  intro same
  exact Bool.false_ne_true (Multiset.singleton_inj.mp same)

/-- A genuinely nonidentity authored context satisfies both modal squares
because its renaming is onto and its frame is empty. -/
theorem actual_swap_modal_squares (point : World swapGrammar) (predicate : swapFace.obj point → Prop) (live : Multiset Bool) :
    (derivedDiamond (eventSpan swapGrammar) (predicate ∘ swapRead point) (swapContext.apply live) ↔
      derivedDiamond (eventSpan swapGrammar) (fun next => predicate (swapFace.map (inContext point swapContext) (swapRead point next))) live) ∧
    (derivedBox (eventSpan swapGrammar) (predicate ∘ swapRead point) (swapContext.apply live) ↔
      derivedBox (eventSpan swapGrammar) (fun next => predicate (swapFace.map (inContext point swapContext) (swapRead point next))) live) :=
  ⟨HostChoiceContextualObservedHypersetHistory.diamond_context_square (exact swapGrammar) swapAtoms copyCoding
      Distinction.HistoryCoverageControls.boolListing copyCoding point swapContext predicate rfl live,
    HostChoiceContextualObservedHypersetHistory.box_context_square (exact swapGrammar) swapAtoms copyCoding
      Distinction.HistoryCoverageControls.boolListing copyCoding point swapContext predicate
      ⟨rfl, fun tag => ⟨!tag, Bool.not_not tag⟩⟩ live⟩

end NonidentityContext

end Mettapedia.GSLT.HostChoiceContextualObservedHypersetSpanControls
