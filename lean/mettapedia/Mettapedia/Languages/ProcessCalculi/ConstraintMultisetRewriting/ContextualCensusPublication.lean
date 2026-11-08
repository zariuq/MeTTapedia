import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualAnswerFamilies
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualQueryAnswers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchemaBatch

/-!
# Contextual census answers become separately scoped publication templates

The request is indexed by the actual source endpoint. Its complete table
is the existing bounded contextual driver on that endpoint's equations and
rows. Returned updates are extracted from those actual results. Each tuple
gets its own helper family, and the packed result preserves its exact
original solution instances. No alternative equations are conjoined.

The publication profile copies answers as schematic data. It does not bind
the caller to all alternatives. Explicit shared captures are the distinct
constructed-template production mode. Candidate order is not specified by
the finite answer set; ordered collection retains its separate scanner
contract.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCensusPublication

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching
open ContextualConjunctiveQueries

variable {S : Signature} {V : Type} {source : V → MetaArity S}

def returnedUpdate {problem : ContextualResidual.Problem source}
    (result : ContextualFrameWorklist.Result problem) (success : ContextualQueryAnswers.successful result = true) :
    ContextualFrameUpdate.Update problem :=
  match result with
  | .residual update => update
  | .refuted _ => False.elim (Bool.false_ne_true success)

theorem returnedUpdate_computed {problem : ContextualResidual.Problem source}
    (result : ContextualFrameWorklist.Result problem) (success : ContextualQueryAnswers.successful result = true) :
    result = .residual (returnedUpdate result success) := by
  cases result with
  | residual update => rfl
  | refuted _ => cases success

theorem returnedUpdate_finished {problem : ContextualResidual.Problem source}
    (result : ContextualFrameWorklist.Result problem) (success : ContextualQueryAnswers.successful result = true) :
    (returnedUpdate result success).remaining = [] := by
  cases result with
  | residual update => exact List.isEmpty_iff.mp success
  | refuted _ => cases success

variable {Query Local O : Type} (queries : Query → MetaArity S) (locals : Local → MetaArity S)
    [DecidableEq Query] [DecidableEq Local] [DecidableEq O]
    [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]
    {Γ : Ctx S} {sort : S.Srt}

structure Request (before : ContextualExecution.Endpoint locals O Γ sort) where
  patterns : List (Term (signature S (queryFamily queries before.declarations)) Γ sort)
  template : Term (signature S (queryFamily queries before.declarations)) Γ sort
  budget : (Fin patterns.length → O) → Nat
  complete : letI := before.equality
    ContextualQueryAnswers.certifies queries locals before.declarations before.inventory.configuration.equations
      patterns before.inventory.rows before.inventory.configuration.present budget = true

namespace Request

variable {queries locals} {before : ContextualExecution.Endpoint locals O Γ sort}

def entries (request : Request queries locals before) : Finset (Fin request.patterns.length → O) := by
  letI := before.equality
  exact ContextualQueryAnswers.answers queries locals before.declarations before.inventory.configuration.equations
    request.patterns before.inventory.rows before.inventory.configuration.present request.budget

abbrev Index (request : Request queries locals before) := { chosen // chosen ∈ request.entries }

def update (request : Request queries locals before) (index : request.Index) :
    ContextualFrameUpdate.Update (ContextualQueryAnswers.problemAt queries locals before.declarations
      before.inventory.configuration.equations request.patterns before.inventory.rows index.val) := by
  letI := before.equality
  exact returnedUpdate (ContextualQueryAnswers.scan queries locals before.declarations
    before.inventory.configuration.equations request.patterns before.inventory.rows request.budget index.val)
    (Finset.mem_filter.mp index.property).2

theorem update_computed (request : Request queries locals before) (index : request.Index) :
    letI := before.equality
    ContextualQueryAnswers.scan queries locals before.declarations before.inventory.configuration.equations
      request.patterns before.inventory.rows request.budget index.val = .residual (request.update index) := by
  let _ := before.equality
  exact returnedUpdate_computed _ (Finset.mem_filter.mp index.property).2

theorem update_finished (request : Request queries locals before) (index : request.Index) :
    (request.update index).remaining = [] := by
  let _ := before.equality
  exact returnedUpdate_finished _ (Finset.mem_filter.mp index.property).2

abbrev Variables (request : Request queries locals before) (index : request.Index) := (request.update index).Variables
abbrev declarations (request : Request queries locals before) (index : request.Index) := (request.update index).declaration
abbrev family (request : Request queries locals before) :=
  ContextualAnswerFamilies.family request.Variables request.declarations

def value (request : Request queries locals before) (index : request.Index) :
    Term (signature S (request.declarations index)) Γ sort :=
  instantiate (request.update index).answer
    (queryView queries locals before.declarations request.template)

def packedValue (request : Request queries locals before) (index : request.Index) :=
  ContextualAnswerFamilies.pack request.Variables request.declarations index (request.value index)

def blueprint (request : Request queries locals before) (index : request.Index) :
    Term (signature S (ContextualTemplateSource.Blueprint locals request.family before.declarations)) Γ sort :=
  instantiate (ContextualStoredRows.privateSource request.family
    (ContextualTemplateSource.Actor locals before.declarations)) (request.packedValue index)

def sourceRule (request : Request queries locals before) (order : List request.Index) :
    ContextualTemplateSource.Rule locals request.family before.declarations Γ sort :=
  ContextualSchemaBatch.rule locals request.family before.declarations (order.map request.packedValue)

instance indexEquality (request : Request queries locals before) : DecidableEq request.Index := inferInstance

instance variableEquality (request : Request queries locals before) :
    DecidableEq (ContextualAnswerFamilies.Names request.Variables) := by
  letI : ∀ index : request.Index, DecidableEq (request.Variables index) := fun index => (request.update index).equality
  infer_instance

/-- The packed value has exactly the instances of this tuple's original
joint problem and source template, independent of its chosen helper family. -/
theorem packed_instances_iff (request : Request queries locals before) (index : request.Index)
    {Next : Type} (next : Next → MetaArity S) (pattern : Term (signature S next) Γ sort) :
    ContextualPublication.Instances request.family (request.packedValue index) next pattern ↔
      ContextualPublication.SourceInstances
        (ContextualQueryAnswers.problemAt queries locals before.declarations before.inventory.configuration.equations
          request.patterns before.inventory.rows index.val)
        (queryView queries locals before.declarations request.template) next pattern :=
  (ContextualAnswerFamilies.instances_pack_iff request.Variables request.declarations next index
    (request.value index) pattern).trans
      (ContextualPublication.completed_instances_iff (request.update index) (request.update_finished index) _ next pattern)

/-- Every possible original matching tuple is published once in the finite
index family. Counts here are physical source tuples, not ground instances. -/
theorem entry_iff_source_match (request : Request queries locals before) (chosen : Fin request.patterns.length → O) :
    chosen ∈ request.entries ↔
      (∀ port, chosen port ∈ before.inventory.configuration.present) ∧
        ∃ (Next : Type) (next : Next → MetaArity S) (candidate : Assignment before.declarations next),
          ContextualFrameUnifier.Models candidate before.inventory.configuration.equations ∧
            ContextualConjunctiveQueries.Matches queries locals before.declarations candidate request.patterns
              before.inventory.rows chosen := by
  let _ := before.equality
  exact ContextualQueryAnswers.actual_answer_iff queries locals before.declarations before.inventory.configuration.equations
    request.patterns before.inventory.rows before.inventory.configuration.present request.budget request.complete chosen

/-- Coverage of the physical answer tuples at a cut. This alone is not a
replay certificate for their saved answer families: changed equations or row
meanings can narrow instances while leaving the tuple set unchanged. Actual
publication remains indexed by the request's original complete endpoint. -/
def CompleteAt (request : Request queries locals before)
    (equations : EquationStore (Term (signature S before.declarations) Γ sort))
    (rows : O → ContextualStoredRows.Row locals before.declarations Γ sort) (world : Finset O) : Prop :=
  ∀ chosen, chosen ∈ request.entries ↔
    (∀ port, chosen port ∈ world) ∧
      ∃ (Next : Type) (next : Next → MetaArity S) (candidate : Assignment before.declarations next),
        ContextualFrameUnifier.Models candidate equations ∧
          ContextualConjunctiveQueries.Matches queries locals before.declarations candidate request.patterns rows chosen

theorem complete_at_source (request : Request queries locals before) :
    request.CompleteAt before.inventory.configuration.equations before.inventory.rows before.inventory.configuration.present :=
  request.entry_iff_source_match

/-- An extra matching tuple containing a newly present occurrence makes a
previous table incomplete. No equality of emitted values can hide it. -/
theorem arrival_invalidates (request : Request queries locals before)
    (equations : EquationStore (Term (signature S before.declarations) Γ sort))
    (rows : O → ContextualStoredRows.Row locals before.declarations Γ sort) (world : Finset O)
    (chosen : Fin request.patterns.length → O) (port : Fin request.patterns.length)
    (new : chosen port ∉ before.inventory.configuration.present)
    (present : ∀ position, chosen position ∈ world)
    (matched : ∃ (Next : Type) (next : Next → MetaArity S) (candidate : Assignment before.declarations next),
      ContextualFrameUnifier.Models candidate equations ∧
        ContextualConjunctiveQueries.Matches queries locals before.declarations candidate request.patterns rows chosen) :
    ¬ request.CompleteAt equations rows world := by
  intro complete
  have member := (complete chosen).mpr ⟨present, matched⟩
  exact new (((request.entry_iff_source_match chosen).mp member).1 port)

structure Publication (request : Request queries locals before) (order : List request.Index) where
  enumerates : order.Perm request.entries.attach.toList
  firing : ContextualTemplatePublication.Firing locals request.family
    (ContextualSchemaBatch.prepared locals request.family before)
  authored : firing.sourceRule = request.sourceRule order

namespace Publication

variable {request : Request queries locals before} {order : List request.Index}

def indexAt (publication : Publication request order) (port : Fin publication.firing.selection.made.length) : request.Index :=
  order.get ⟨port.val, by
    have bound := ContextualSchemaBatch.value_bound locals request.family (order.map request.packedValue)
      publication.firing publication.authored port
    simpa only [List.length_map] using bound⟩

theorem output_length (publication : Publication request order) :
    publication.firing.selection.made.length = order.length := by
  have authoredLength := congrArg (fun source => source.produce.length) publication.authored
  have listed : (request.sourceRule order).produce.length = order.length := by
    change ((order.map request.packedValue).map
      (fun value => ContextualTemplateSource.Production.schema
        (ContextualSchemaBatch.blueprint locals request.family before.declarations value))).length = order.length
    rw [List.length_map, List.length_map]
  exact publication.firing.output_length.trans (authoredLength.trans listed)

theorem output_count (publication : Publication request order) :
    publication.firing.selection.made.length = request.entries.card := by
  have tableLength := publication.enumerates.length_eq
  rw [Finset.length_toList, Finset.card_attach] at tableLength
  exact publication.output_length.trans tableLength

/-- No source tuple can disappear when equal projected values coincide. -/
theorem every_tuple_has_an_output (publication : Publication request order)
    (chosen : Fin request.patterns.length → O) (member : chosen ∈ request.entries) :
    ∃ port : Fin publication.firing.selection.made.length, (publication.indexAt port).val = chosen := by
  let index : request.Index := ⟨chosen, member⟩
  have listed : index ∈ order := publication.enumerates.mem_iff.mpr (by simp)
  obtain ⟨position, atIndex⟩ := List.mem_iff_get.mp listed
  let port : Fin publication.firing.selection.made.length :=
    ⟨position.val, publication.output_length.symm ▸ position.isLt⟩
  exact ⟨port, congrArg Subtype.val atIndex⟩

/-- The actual row published at each output has precisely the original
matching tuple's source instances. Publication does not conjoin alternatives. -/
theorem row_instances (publication : Publication request order) (port : Fin publication.firing.selection.made.length)
    {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment publication.firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    ContextualGuardMatching.Matches
      (ContextualPublication.privateFamily (ContextualTemplateSource.Expanded locals request.family)
        publication.firing.update.declaration)
      candidate pattern (publication.firing.target.inventory.rows (publication.firing.selection.made.get port)) ↔
    ContextualPublication.SourceInstances
      (ContextualQueryAnswers.problemAt queries locals before.declarations before.inventory.configuration.equations
        request.patterns before.inventory.rows (publication.indexAt port).val)
      (queryView queries locals before.declarations request.template) next pattern := by
  have published := ContextualSchemaBatch.published_instances locals request.family (order.map request.packedValue)
    publication.firing publication.authored port next candidate pattern
  have packed : ContextualPublication.Instances request.family
      ((order.map request.packedValue).get
        ⟨port.val, ContextualSchemaBatch.value_bound locals request.family (order.map request.packedValue)
          publication.firing publication.authored port⟩) next pattern ↔
      ContextualPublication.Instances request.family (request.packedValue (publication.indexAt port)) next pattern := by
    change ContextualPublication.Instances request.family
      ((order.map request.packedValue)[port.val]'(ContextualSchemaBatch.value_bound locals request.family
        (order.map request.packedValue) publication.firing publication.authored port)) next pattern ↔ _
    rw [List.getElem_map]
    rfl
  exact published.trans (packed.trans (request.packed_instances_iff (publication.indexAt port) next pattern))

end Publication

/-- A complete actual answer table is published by one actual checked firing.
Its order only enumerates identities; it makes no ordered-collection claim. -/
theorem realize_publication (request : Request queries locals before) (order : List request.Index)
    (enumerates : order.Perm request.entries.attach.toList) (made : List O)
    (distinct : made.Nodup) (fresh : Disjoint made.toFinset before.inventory.configuration.present)
    (lengths : made.length = order.length)
    (consistent : ContextualFrameUnifier.Solvable before.inventory.configuration.equations)
    (patterned : ContextualPatternFragment.ProblemPattern
      (ContextualResidual.observeProblem before.inventory.configuration.equations)) :
    ∃ publication : Publication request order, publication.firing.selection = ContextualSchemaBatch.selection made := by
  let _ := before.equality
  obtain ⟨firing, authored, selected, _⟩ := ContextualSchemaBatch.realize locals request.family before
    (order.map request.packedValue) made distinct fresh
    (by simpa only [List.length_map] using lengths) consistent patterned
  exact ⟨⟨enumerates, firing, authored⟩, selected⟩

end Request

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCensusPublication
