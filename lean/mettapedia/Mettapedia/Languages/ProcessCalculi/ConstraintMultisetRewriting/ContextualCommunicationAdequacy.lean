import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunicationProfiles
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.TransitionMaps
import Mettapedia.OSLF.Syntax.RhoScopedParallelSourceAdequacy
import Mettapedia.OSLF.Syntax.RhoPayloadResources
import Mettapedia.OSLF.Syntax.RhoPayloadParameterizedRuntime
import Mettapedia.OSLF.Syntax.RhoCanonicalWholeNameAdmission

/-!
# Scoped rho/CMR adequacy with one shared interpretation of every occurrence

An interpreted firing retains its original source root, an ordinary CMR step,
and one model of the complete result equation store. Its observed endpoints
are related by the independently defined source event relation.

Conversely every source event lifts from any normalized physical occurrence
representation, provided its existing equations hold at the identity model.
The lift constructs distinct takes and fresh outputs through the existing
occurrence supply. It retains normalized output, so the representation
invariant is available for subsequent steps.

Contextual closure is the source's declared parallel reaction permission.
The source equations include name quote/drop; admitting operational process
Drop remains a separate choice of rule profile. Event identities and physical
selection order are not quotiented into the endpoint comparison.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunicationAdequacy

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open RhoSchema RhoQuotationClassFibres
open RhoScopedParallelInventory RhoScopedEventPresheaf
open ContextualCommunicationProfiles
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {admitted : RhoScopedParallelEvents.SourceRule → Prop} {context : Ctx sig}

local instance : DecidableEq (Process context) := Classical.decEq _

/-- Existing CMR execution, with the exact admitted source origin and the
shared interpretation needed by its source-class observation. -/
def InterpretedStep (admitted : RhoScopedParallelEvents.SourceRule → Prop)
    (assignment : Sub sig context context)
    (before after : Configuration (Process context) (Occurrence context)) : Prop :=
  ∃ root : Root admitted context,
    ConstraintMultisetRewriting.Step (action context) label (instanceRule root) before after ∧
      (action context).Models assignment after.equations

theorem selected_firing_no_invention (root : Root admitted context)
    (assignment : Sub sig context context)
    {before : Configuration (Process context) (Occurrence context)} {selection : Selection (Occurrence context)}
    (valid : selection.Valid (action context) label (instanceRule root) before)
    (solved : (action context).Models assignment (selection.result label (instanceRule root) before).equations) :
    RhoScopedParallelEvents.Step (rules := RhoScopedParallelEvents.sourceRules) (admitted := admitted)
      (observe assignment before.present)
      (observe assignment (selection.result label (instanceRule root) before).present) := by
  obtain ⟨frame, sourceRead, targetRead, _reads⟩ :=
    PositiveResourceProjection.observed_frame (action context) rfl valid solved
  have sourceClass := congrArg assemble sourceRead
  have targetClass := congrArg assemble targetRead
  rw [assemble_add, assemble_mapped_take] at sourceClass
  rw [assemble_add, assemble_mapped_produce] at targetClass
  apply (RhoScopedParallelEvents.step_iff_root_surrounding _ _).mpr
  refine ⟨root.map assignment, assemble frame, ?_, ?_⟩
  · rw [RhoScopedParallelEvents.Root.source_map]
    exact sourceClass.trans (join_commutes _ _)
  · rw [RhoScopedParallelEvents.Root.target_map]
    exact targetClass.trans (join_commutes _ _)

theorem InterpretedStep.no_invention {assignment : Sub sig context context}
    {before after : Configuration (Process context) (Occurrence context)}
    (executed : InterpretedStep admitted assignment before after) :
    RhoScopedParallelEvents.Step (rules := RhoScopedParallelEvents.sourceRules) (admitted := admitted)
      (observe assignment before.present) (observe assignment after.present) := by
  obtain ⟨root, ⟨selection, valid, rfl⟩, solved⟩ := executed
  exact selected_firing_no_invention root assignment valid solved

theorem source_step_has_firing (source target : Process context)
    (before : Configuration (Process context) (Occurrence context))
    (background : (action context).Models (action context).identity before.equations)
    (represents : labels label before.present = normalized source)
    (event : RhoScopedParallelEvents.Step (rules := RhoScopedParallelEvents.sourceRules)
      (admitted := admitted) source target) :
    ∃ after : Configuration (Process context) (Occurrence context),
      InterpretedStep admitted (action context).identity before after ∧
        labels label after.present = normalized target := by
  obtain ⟨root, surrounding, sourceShape, targetShape⟩ :=
    (RhoScopedParallelEvents.step_iff_root_surrounding source target).mp event
  have identity : (action context).apply (action context).identity = id := by
    funext process
    exact (action context).apply_identity process
  have labelsFixed : PositiveResourceProjection.realized (action context)
      (action context).identity (label (context := context)) = label := by
    funext occurrence
    exact (action context).apply_identity _
  have sourceFrame : labels (PositiveResourceProjection.realized (action context)
      (action context).identity label) before.present = normalized surrounding +
        ((instanceRule root).take.map ((action context).apply (action context).identity) : Multiset (Process context)) := by
    rw [labelsFixed, identity, List.map_id, instance_take, represents, sourceShape, normalized_join]
    exact add_comm _ _
  obtain ⟨selection, valid, solved, targetRead⟩ :=
    PositiveResourceProjection.lift_no_read_frame (action context) (action context).identity label rfl
      IndexedOccurrences.supply (instanceRule root) rfl rfl before background
      ((action context).models_nil _) (normalized surrounding) sourceFrame
  refine ⟨selection.result label (instanceRule root) before,
    ⟨root, ⟨selection, valid, rfl⟩, solved⟩, ?_⟩
  rw [labelsFixed, identity, List.map_id, instance_produce] at targetRead
  rw [targetRead, targetShape, normalized_join]
  exact add_comm _ _

/-- Exact source-event support from a declared normalized occurrence store. -/
theorem source_step_iff_firing (source target : Process context)
    (before : Configuration (Process context) (Occurrence context))
    (background : (action context).Models (action context).identity before.equations)
    (represents : labels label before.present = normalized source) :
    RhoScopedParallelEvents.Step (rules := RhoScopedParallelEvents.sourceRules) (admitted := admitted)
      source target ↔
      ∃ after : Configuration (Process context) (Occurrence context),
        InterpretedStep admitted (action context).identity before after ∧
          labels label after.present = normalized target := by
  constructor
  · exact source_step_has_firing source target before background represents
  · rintro ⟨after, executed, targetRead⟩
    have event := executed.no_invention
    rw [observe_identity_of_normalized before.present source represents,
      observe_identity_of_normalized after.present target targetRead] at event
    exact event

theorem every_source_step_has_occurrence_execution (source target : Process context)
    (event : RhoScopedParallelEvents.Step (rules := RhoScopedParallelEvents.sourceRules)
      (admitted := admitted) source target) :
    ∃ before after : Configuration (Process context) (Occurrence context),
      before.equations = [] ∧ labels label before.present = normalized source ∧
      InterpretedStep admitted (action context).identity before after ∧
      labels label after.present = normalized target := by
  obtain ⟨world, represented⟩ := every_source_class_has_occurrences source
  let before : Configuration (Process context) (Occurrence context) := ⟨[], world⟩
  obtain ⟨after, executed, targetRead⟩ := source_step_has_firing source target before
    ((action context).models_nil _) represented event
  exact ⟨before, after, rfl, represented, executed, targetRead⟩

/-- The same admitted source event remains executable under every declared
parallel surrounding process, including an open ambient continuation. -/
theorem parallel_plugging (source target surrounding : Process context)
    (event : RhoScopedParallelEvents.Step (rules := RhoScopedParallelEvents.sourceRules)
      (admitted := admitted) source target)
    (before : Configuration (Process context) (Occurrence context))
    (background : (action context).Models (action context).identity before.equations)
    (represents : labels label before.present = normalized (join source surrounding)) :
    ∃ after : Configuration (Process context) (Occurrence context),
      InterpretedStep admitted (action context).identity before after ∧
        labels label after.present = normalized (join target surrounding) :=
  source_step_has_firing _ _ before background represents
    (RhoScopedParallelEvents.step_join event surrounding)

theorem substitution_plugging {destination : Ctx sig}
    (change : Sub sig context destination) (source target : Process context)
    (event : RhoScopedParallelEvents.Step (rules := RhoScopedParallelEvents.sourceRules)
      (admitted := admitted) source target) :
    ∃ before after : Configuration (Process destination) (Occurrence destination),
      before.equations = [] ∧ labels label before.present = normalized (bindQ change source) ∧
      InterpretedStep admitted (action destination).identity before after ∧
      labels label after.present = normalized (bindQ change target) :=
  every_source_step_has_occurrence_execution _ _ (RhoScopedParallelEvents.step_substitution change event)

/-- At closed context the comparison reaches the existing declared
parallel source reduction relation, including source equation closure. -/
theorem closed_parallel_source_iff (source target : Term sig [] Srt.pr)
    (before : Configuration (Process []) (Occurrence []))
    (background : (action []).Models (action []).identity before.equations)
    (represents : labels label before.present = normalized (RhoEquationConstructorControls.project source)) :
    RhoSchema.ParallelStepModE source target ↔
      ∃ after : Configuration (Process []) (Occurrence []),
        InterpretedStep RhoScopedParallelEvents.withReflection (action []).identity before after ∧
          labels label after.present = normalized (RhoEquationConstructorControls.project target) := by
  rw [RhoScopedParallelSourceAdequacy.parallelStepModE_iff_event]
  exact source_step_iff_firing _ _ before background represents

/-- The source representation retains the whole incoming equation store;
identity is one shared model of it, not a reset before the next event. -/
def Represents (state : Configuration (Process context) (Occurrence context)) (process : Process context) : Prop :=
  (action context).Models (action context).identity state.equations ∧
    labels label state.present = normalized process

theorem InterpretedStep.retains_model
    {before after : Configuration (Process context) (Occurrence context)}
    (executed : InterpretedStep admitted (action context).identity before after) :
    (action context).Models (action context).identity after.equations := by
  obtain ⟨root, step, modeled⟩ := executed
  exact modeled

/-- Source paths compose through the actual occurrence states returned by
the previous firings. Every old equation remains present and satisfied. -/
theorem source_path_has_firings (source target : Process context)
    (before : Configuration (Process context) (Occurrence context))
    (represented : Represents before source)
    (path : Relation.ReflTransGen
      (RhoScopedParallelEvents.Step (rules := RhoScopedParallelEvents.sourceRules) (admitted := admitted)) source target) :
    ∃ after, Relation.ReflTransGen (InterpretedStep admitted (action context).identity) before after ∧
      Represents after target := by
  induction path with
  | refl => exact ⟨before, .refl, represented⟩
  | tail prior event ih =>
      obtain ⟨middle, executed, models, represented⟩ := ih
      obtain ⟨after, firing, targetRead⟩ := source_step_has_firing _ _ middle models represented event
      exact ⟨after, executed.tail firing, firing.retains_model, targetRead⟩

theorem interpreted_path_no_invention
    {before after : Configuration (Process context) (Occurrence context)}
    (path : Relation.ReflTransGen (InterpretedStep admitted (action context).identity) before after) :
    Relation.ReflTransGen
      (RhoScopedParallelEvents.Step (rules := RhoScopedParallelEvents.sourceRules) (admitted := admitted))
      (observe (action context).identity before.present) (observe (action context).identity after.present) := by
  induction path with
  | refl => exact .refl
  | tail prior event ih => exact ih.tail event.no_invention

/-- Finite reachability for the declared intrinsic source profile. This
does not identify semantic COMM substitution with ordinary substitution or
turn the optional free-Drop profile into the paper-faithful rho core. -/
theorem source_path_iff_firings (source target : Process context)
    (before : Configuration (Process context) (Occurrence context))
    (represented : Represents before source) :
    Relation.ReflTransGen
      (RhoScopedParallelEvents.Step (rules := RhoScopedParallelEvents.sourceRules) (admitted := admitted)) source target ↔
    ∃ after, Relation.ReflTransGen (InterpretedStep admitted (action context).identity) before after ∧
      Represents after target := by
  constructor
  · exact source_path_has_firings source target before represented
  · rintro ⟨after, executed, _, targetRead⟩
    have sourcePath := interpreted_path_no_invention executed
    rw [observe_identity_of_normalized before.present source represented.2,
      observe_identity_of_normalized after.present target targetRead] at sourcePath
    exact sourcePath

namespace Payload

open RhoPayloadPresentation (Cls CommInstance commConsume commProduce strictSystem
  cls outT inpT atoms atomsQ atomsQ_cls realize AtomBag atomBag_atoms atomBag_add atomBag_of_le
  atoms_realize atomsQ_bindQ foldQ cls_eq_foldQ)
open RhoPayloadParameterizedRuntime (classStep)

local notation "PSig" => RhoPayloadPresentation.sig
local notation "proc" => RhoPayloadPresentation.Srt.pr

abbrev Process (Γ : Ctx PSig) := Cls Γ proc
abbrev Occurrence (Γ : Ctx PSig) := IndexedOccurrences.Occurrence (Process Γ)
abbrev Store (Γ : Ctx PSig) := Configuration (Process Γ) (Occurrence Γ)

variable {Γ : Ctx PSig}

attribute [local instance] Classical.propDecidable

abbrev label : Occurrence Γ → Process Γ := IndexedOccurrences.label
abbrev action (Γ : Ctx PSig) := equationAction RhoPayloadPresentation.equations Γ proc

/-- Install the communication from its authored channel, payload and
continuation. Emit one fresh row per atom of the instantiated continuation,
not one row per distinct label. -/
def instanceRule (i : CommInstance Γ) : RuleInstance (Process Γ) :=
  ⟨[cls (outT i.1 i.2.1), cls (inpT i.1 i.2.2)], [], [], [], (commProduce i).toList⟩

theorem instance_take (i : CommInstance Γ) :
    ((instanceRule i).take : Multiset (Process Γ)) = commConsume i := rfl

theorem instance_produce (i : CommInstance Γ) :
    ((instanceRule i).produce : Multiset (Process Γ)) = commProduce i :=
  Multiset.coe_toList _

/-- Match at a fixed ambient scope. The actual CMR result must admit
the identity interpretation there; a substitution that merely could
identify two currently unequal channels does not authorize a reaction. -/
def InterpretedStep (before after : Store Γ) : Prop :=
  ∃ i : CommInstance Γ,
    ConstraintMultisetRewriting.Step (action Γ) label (instanceRule i) before after ∧
      (action Γ).Models (action Γ).identity after.equations

def Represents (state : Store Γ) (process : Process Γ) : Prop :=
  (action Γ).Models (action Γ).identity state.equations ∧ labels label state.present = atomsQ process

def observe (state : Store Γ) : Process Γ := foldQ (labels label state.present)

theorem Represents.readback {state : Store Γ} {process : Process Γ}
    (represented : Represents state process) : observe state = process := by
  rw [observe, represented.2]
  simpa only [← atomsQ_cls, RhoPayloadPresentation.cls_out] using
    (cls_eq_foldQ (Quotient.out process)).symm

theorem every_source_has_store (source : Process Γ) : ∃ before : Store Γ, Represents before source := by
  obtain ⟨world, reconstructed⟩ := IndexedOccurrences.realize (atomsQ source)
  exact ⟨⟨[], world⟩, (action Γ).models_nil _, reconstructed⟩

private theorem label_identity :
    PositiveResourceProjection.realized (action Γ) (action Γ).identity (label (Γ := Γ)) = label := by
  funext occurrence
  exact (action Γ).apply_identity _

private theorem apply_identity : (action Γ).apply (action Γ).identity = id :=
  funext (action Γ).apply_identity

private theorem take_identity (i : CommInstance Γ) :
    ((instanceRule i).take.map ((action Γ).apply (action Γ).identity) : Multiset _) = commConsume i := by
  rw [apply_identity, List.map_id, instance_take]

private theorem produce_identity (i : CommInstance Γ) :
    ((instanceRule i).produce.map ((action Γ).apply (action Γ).identity) : Multiset _) = commProduce i := by
  rw [apply_identity, List.map_id, instance_produce]

theorem class_step_iff_resources (source target : Process Γ) :
    classStep source target ↔ (strictSystem Γ).theory.Step (atomsQ source) (atomsQ target) := by
  simpa only [classStep, ← atomsQ_cls, RhoPayloadPresentation.cls_out] using
    RhoPayloadPresentation.strict_step_iff (Quotient.out source) (Quotient.out target)

/-- Read back the surviving frame of an actual firing in its fixed scope. -/
theorem InterpretedStep.frame {before after : Store Γ} (executed : InterpretedStep before after) :
    ∃ (i : CommInstance Γ) (surviving : Multiset (Process Γ)),
      labels label before.present = surviving + commConsume i ∧
      labels label after.present = surviving + commProduce i := by
  obtain ⟨i, ⟨selection, valid, rfl⟩, solved⟩ := executed
  obtain ⟨surviving, source, target, _⟩ :=
    PositiveResourceProjection.observed_frame (action Γ) rfl valid solved
  rw [label_identity, take_identity] at source
  rw [label_identity, produce_identity] at target
  exact ⟨i, surviving, source, target⟩

/-- Every equation-class step lifts from any represented occurrence store,
with its earlier knowledge kept in the new configuration. -/
theorem source_step_has_firing {source target : Process Γ} {before : Store Γ}
    (represented : Represents before source) (step : classStep source target) :
    ∃ after, InterpretedStep before after ∧ Represents after target := by
  obtain ⟨site, i, enabled, targetBag⟩ := (class_step_iff_resources source target).mp step
  cases site
  change CommInstance Γ at i
  have available : commConsume i ≤ atomsQ source := by
    change commConsume i + 0 ≤ _ at enabled
    simpa only [add_zero] using enabled
  have cut : labels label before.present = (atomsQ source - commConsume i) + commConsume i :=
    represented.2.trans (tsub_add_cancel_of_le available).symm
  have targetBag' : atomsQ target = (atomsQ source - commConsume i) + commProduce i := targetBag
  have observed : labels (PositiveResourceProjection.realized (action Γ) (action Γ).identity label)
      before.present =
      (atomsQ source - commConsume i) +
        ((instanceRule i).take.map ((action Γ).apply (action Γ).identity) : Multiset _) := by
    rw [label_identity, take_identity]
    exact cut
  obtain ⟨picked, admitted, solved, result⟩ :=
    PositiveResourceProjection.lift_no_read_frame (action Γ) (action Γ).identity label rfl
      IndexedOccurrences.supply (instanceRule i) rfl rfl before represented.1
      ((action Γ).models_nil _) (atomsQ source - commConsume i) observed
  rw [label_identity, produce_identity, ← targetBag'] at result
  exact ⟨_, ⟨i, ⟨picked, admitted, rfl⟩, solved⟩, solved, result⟩

/-- Arbitrary admitted target work in this profile reads back to a source
step with an inhabitant of the same representation invariant. -/
theorem target_step_reads_back {before after : Store Γ} {source : Process Γ}
    (represented : Represents before source) (step : InterpretedStep before after) :
    ∃ target : Process Γ, classStep source target ∧ Represents after target := by
  obtain ⟨i, surviving, start, finish⟩ := step.frame
  have sourceBag : AtomBag (labels label before.present) := by
    rw [represented.2, ← RhoPayloadPresentation.cls_out source, atomsQ_cls]
    exact atomBag_atoms (Quotient.out source)
  have survivingBag : AtomBag surviving :=
    atomBag_of_le sourceBag (by rw [start]; exact Multiset.le_add_right _ _)
  have resultBag : AtomBag (labels label after.present) := by
    rw [finish]
    exact atomBag_add survivingBag (atomBag_atoms _)
  let target := cls (realize (labels label after.present))
  have reads : atomsQ target = labels label after.present := atoms_realize resultBag
  have solved : (action Γ).Models (action Γ).identity after.equations := by
    obtain ⟨_, _, solved⟩ := step
    exact solved
  refine ⟨target, (class_step_iff_resources source target).mpr ⟨(), i, ?_, ?_⟩, solved, reads.symm⟩
  · change commConsume i + 0 ≤ atomsQ source
    rw [add_zero, ← represented.2, start]
    exact Multiset.le_add_left _ _
  · change atomsQ target = atomsQ source - commConsume i + commProduce i
    rw [reads, ← represented.2, start, add_tsub_cancel_right, finish]

open FragmentsOfTheStep.TransitionMaps (IsBisimulation)

/-- Each strict-class reaction matches exactly one physical commit, and
every admitted commit matches one reaction. -/
theorem bisimulation (Γ : Ctx PSig) :
    IsBisimulation InterpretedStep classStep (Represents (Γ := Γ)) :=
  ⟨target_step_reads_back, source_step_has_firing⟩

theorem source_path_has_firings {source target : Process Γ} {before : Store Γ}
    (represented : Represents before source) (path : Relation.ReflTransGen classStep source target) :
    ∃ after, Relation.ReflTransGen InterpretedStep before after ∧ Represents after target := by
  induction path with
  | refl => exact ⟨before, .refl, represented⟩
  | tail _ step earlier =>
    obtain ⟨middle, executed, ready⟩ := earlier
    obtain ⟨after, firing, completed⟩ := source_step_has_firing ready step
    exact ⟨after, executed.tail firing, completed⟩

theorem target_path_reads_back {before after : Store Γ} {source : Process Γ}
    (represented : Represents before source) (path : Relation.ReflTransGen InterpretedStep before after) :
    Relation.ReflTransGen classStep source (observe after) ∧ Represents after (observe after) := by
  induction path with
  | refl => rw [represented.readback]; exact ⟨.refl, represented⟩
  | tail _ step earlier =>
    obtain ⟨executed, ready⟩ := earlier
    obtain ⟨target, firing, completed⟩ := target_step_reads_back ready step
    rw [completed.readback]
    exact ⟨executed.tail firing, completed⟩

/-- Rebinding the ambient scope preserves the reaction. It may require
repacking occurrences: an ambient process variable can become a parallel
process. No preservation of physical addresses under repacking is assumed. -/
theorem reindexed_step_has_firing {Δ : Ctx PSig} (change : Sub PSig Γ Δ)
    {source : Process Γ} {before after : Store Γ} {reindexed : Store Δ}
    (represented : Represents before source) (step : InterpretedStep before after)
    (repacked : Represents reindexed (bindQ change source)) :
    ∃ (target : Process Γ) (result : Store Δ),
      Represents after target ∧ InterpretedStep reindexed result ∧
        Represents result (bindQ change target) ∧
        labels label result.present =
          (labels label after.present).bind (fun atom => atomsQ (bindQ change atom)) := by
  obtain ⟨target, sourceStep, readback⟩ := target_step_reads_back represented step
  obtain ⟨result, fired, related⟩ := source_step_has_firing repacked
    (RhoPayloadParameterizedRuntime.classStep_substitute change sourceStep)
  refine ⟨target, result, readback, fired, related, ?_⟩
  rw [related.2, readback.2, atomsQ_bindQ]

/-- Compose the physical occurrence bridge with the independent authored
semantic-COMM interpretation. The source profile does not admit free Drop. -/
theorem authored_step_has_firing
    {free : Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax.FreeSortContext}
    (namesOnly : ∀ name, free name ≠ some Mettapedia.OSLF.MeTTaIL.Syntax.rhoReflectivePresentation.processSort)
    {source target : RhoCalculus.ParameterizedRewriteSystem.Process free} {before : Store []}
    (represented : Represents before (RhoPayloadParameterizedRuntime.mapClass namesOnly source))
    (step : (RhoCalculus.ParameterizedRewriteSystem.theory free).Step source target) :
    ∃ after, InterpretedStep before after ∧
      Represents after (RhoPayloadParameterizedRuntime.mapClass namesOnly target) :=
  source_step_has_firing represented (RhoPayloadParameterizedRuntime.forward_step namesOnly step)

theorem target_step_reads_back_authored
    {free : Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax.FreeSortContext}
    (namesOnly : ∀ name, free name ≠ some Mettapedia.OSLF.MeTTaIL.Syntax.rhoReflectivePresentation.processSort)
    {source : RhoCalculus.ParameterizedRewriteSystem.Process free} {before after : Store []}
    (represented : Represents before (RhoPayloadParameterizedRuntime.mapClass namesOnly source))
    (step : InterpretedStep before after) :
    ∃ target, (RhoCalculus.ParameterizedRewriteSystem.theory free).Step source target ∧
      Represents after (RhoPayloadParameterizedRuntime.mapClass namesOnly target) := by
  obtain ⟨outcome, reaction, read⟩ := target_step_reads_back represented step
  obtain ⟨target, sourceStep, equal⟩ := RhoPayloadParameterizedRuntime.lift_step namesOnly reaction
  exact ⟨target, sourceStep, equal ▸ read⟩

theorem authored_bisimulation
    {free : Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax.FreeSortContext}
    (namesOnly : ∀ name, free name ≠ some Mettapedia.OSLF.MeTTaIL.Syntax.rhoReflectivePresentation.processSort) :
    IsBisimulation InterpretedStep (RhoCalculus.ParameterizedRewriteSystem.theory free).Step
      (fun state process => Represents state (RhoPayloadParameterizedRuntime.mapClass namesOnly process)) :=
  ⟨target_step_reads_back_authored namesOnly, authored_step_has_firing namesOnly⟩

/-- The reflected authored commit is a real semantic reduction, not just a
conversion between equal syntax presentations. -/
theorem target_step_has_paper_reduction
    {free : Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax.FreeSortContext}
    (namesOnly : ∀ name, free name ≠ some Mettapedia.OSLF.MeTTaIL.Syntax.rhoReflectivePresentation.processSort)
    {source : RhoCalculus.ParameterizedRewriteSystem.Process free} {before after : Store []}
    (represented : Represents before (RhoPayloadParameterizedRuntime.mapClass namesOnly source))
    (step : InterpretedStep before after) :
    ∃ target : RhoCalculus.ParameterizedRewriteSystem.Process free,
      Nonempty (RhoCalculus.Reduction.Reduces source.1 target.1) ∧
        Represents after (RhoPayloadParameterizedRuntime.mapClass namesOnly target) := by
  obtain ⟨target, authored, readback⟩ := target_step_reads_back_authored namesOnly represented step
  obtain ⟨redex, contractum, entry, actual, exit⟩ :=
    RhoCalculus.ParameterizedRewriteSystem.step_iff.mp authored
  have typed := ((RhoCalculus.ParameterizedRewriteSystem.process_iff free redex.1).mp redex.2).1
  obtain ⟨reaction⟩ := RhoCalculus.DerivedContextualStep.rhoStep_sound typed actual
  exact ⟨target, ⟨.equiv
    ((RhoCalculus.ParameterizedRewriteSystem.equations_iff_structuralCongruence source redex).mp entry)
    reaction
    ((RhoCalculus.ParameterizedRewriteSystem.equations_iff_structuralCongruence contractum target).mp exit)⟩,
    readback⟩

section CanonicalSurface

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern rhoReflectivePresentation)
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax (FreeSortContext ProcWellSorted)
open Mettapedia.OSLF.Binding.RhoPayloadPresentation (canonicalProcess canonicalWholeNameSafe)
open RhoCalculus.Canonical (canonicalize canonicalize_idempotent)
open RhoCalculus.DerivedContextualStep (RhoStepAt)

/-- Fixing the target equation class determines the exact canonical COMM
question for a well-sorted surface source. Its unnormalized spelling
need not satisfy the literal quotation checker. -/
theorem canonical_surface_step_iff_firing {free : FreeSortContext}
    (namesOnly : ∀ name, free name ≠ some rhoReflectivePresentation.processSort)
    {source : Pattern} (typed : ProcWellSorted rhoReflectivePresentation free [] source)
    (admitted : canonicalWholeNameSafe source = true)
    {target : RhoCalculus.ParameterizedRewriteSystem.Process free} {before : Store []}
    (represented : Represents before
      (RhoPayloadParameterizedRuntime.mapClass namesOnly (canonicalProcess source typed admitted))) :
    (∃ residual, RhoStepAt 1 (canonicalize source) residual ∧
      canonicalize residual = canonicalize target.1) ↔
    ∃ after, InterpretedStep before after ∧
      Represents after (RhoPayloadParameterizedRuntime.mapClass namesOnly target) := by
  have sourceCriterion :=
    RhoCalculus.ParameterizedRewriteSystem.step_iff_canonical_communication
      (source := canonicalProcess source typed admitted) (target := target)
  have equivalent :
      (RhoCalculus.ParameterizedRewriteSystem.theory free).Step (canonicalProcess source typed admitted) target ↔
      ∃ residual, RhoStepAt 1 (canonicalize source) residual ∧
        canonicalize residual = canonicalize target.1 := by
    simpa only [canonicalProcess,canonicalize_idempotent] using sourceCriterion
  rw [← equivalent]
  constructor
  · exact authored_step_has_firing namesOnly represented
  · rintro ⟨after,fired,final⟩
    obtain ⟨other,run,read⟩ := target_step_reads_back_authored namesOnly represented fired
    have classEq := read.readback.symm.trans final.readback
    have endpoint := (RhoPayloadParameterizedRuntime.mapClass_eq_iff namesOnly other target).mp classEq
    obtain ⟨redex,contractum,opening,reacted,closing⟩ :=
      RhoCalculus.ParameterizedRewriteSystem.step_iff.mp run
    exact RhoCalculus.ParameterizedRewriteSystem.step_iff.mpr
      ⟨redex,contractum,opening,reacted,Eq.trans closing endpoint⟩

/-- The canonical reaction read back from an admitted target edge is
also a paper reduction of the original surface spelling. Its actual
contractum inhabits the declared source scope. -/
theorem canonical_surface_firing_reflects_paper {free : FreeSortContext}
    (namesOnly : ∀ name, free name ≠ some rhoReflectivePresentation.processSort)
    {source : Pattern} (typed : ProcWellSorted rhoReflectivePresentation free [] source)
    (admitted : canonicalWholeNameSafe source = true) {before after : Store []}
    (represented : Represents before
      (RhoPayloadParameterizedRuntime.mapClass namesOnly (canonicalProcess source typed admitted)))
    (fired : InterpretedStep before after) :
    ∃ residual : RhoCalculus.ParameterizedRewriteSystem.Process free,
      RhoStepAt 1 (canonicalize source) residual.1 ∧
      Nonempty (RhoCalculus.Reduction.Reduces source residual.1) ∧
      Represents after (RhoPayloadParameterizedRuntime.mapClass namesOnly residual) := by
  obtain ⟨endpoint,authored,readback⟩ :=
    target_step_reads_back_authored namesOnly represented fired
  obtain ⟨raw,atRepresentative,closing⟩ :=
    RhoCalculus.ParameterizedRewriteSystem.step_iff_canonical_communication.mp authored
  have reacts : RhoStepAt 1 (canonicalize source) raw := by
    simpa only [canonicalProcess,canonicalize_idempotent] using atRepresentative
  let residual := RhoCalculus.ParameterizedRewriteSystem.stepTarget
    (canonicalProcess source typed admitted) ⟨1,reacts⟩
  have same : RhoPayloadParameterizedRuntime.mapClass namesOnly residual =
      RhoPayloadParameterizedRuntime.mapClass namesOnly endpoint :=
    (RhoPayloadParameterizedRuntime.mapClass_eq_iff namesOnly residual endpoint).mpr closing
  obtain ⟨paper⟩ := RhoCalculus.DerivedContextualStep.rhoStepAt_sound
    (RhoCalculus.CanonicalTyping.canonicalize_procWellSorted [] typed) reacts
  refine ⟨residual,reacts,⟨.equiv (RhoCalculus.Canonical.canonicalize_sound source) paper (.refl _)⟩,?_⟩
  rwa [same]

/-- Read an arbitrary admitted target path back from the compiled surface
term. Every recorded edge is an actual depth-one authored reaction on
the corresponding canonical representative; equations alone do not
count as an edge, including at the empty path. -/
theorem canonical_surface_path_reads_back {free : FreeSortContext}
    (namesOnly : ∀ name, free name ≠ some rhoReflectivePresentation.processSort)
    {source : Pattern} (typed : ProcWellSorted rhoReflectivePresentation free [] source)
    (admitted : canonicalWholeNameSafe source = true) {before after : Store []}
    (represented : Represents before
      (RhoPayloadParameterizedRuntime.mapClass namesOnly (canonicalProcess source typed admitted)))
    (path : Relation.ReflTransGen InterpretedStep before after) :
    ∃ target : RhoCalculus.ParameterizedRewriteSystem.Process free,
      Relation.ReflTransGen (fun first last : RhoCalculus.ParameterizedRewriteSystem.Process free =>
        ∃ residue, RhoStepAt 1 (canonicalize first.1) residue ∧
          canonicalize residue = canonicalize last.1)
        (canonicalProcess source typed admitted) target ∧
      Represents after (RhoPayloadParameterizedRuntime.mapClass namesOnly target) := by
  induction path with
  | refl => exact ⟨_, .refl, represented⟩
  | tail _ fired ih =>
    obtain ⟨middle,earlier,representedMiddle⟩ := ih
    obtain ⟨target,authored,representedTarget⟩ :=
      target_step_reads_back_authored namesOnly representedMiddle fired
    exact ⟨target,earlier.tail
      (RhoCalculus.ParameterizedRewriteSystem.step_iff_canonical_communication.mp authored),
      representedTarget⟩

end CanonicalSurface

end Payload

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunicationAdequacy
