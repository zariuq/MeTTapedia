import Mettapedia.Languages.MeTTa.SpaceTheory.HETypeQueries
import Mettapedia.Languages.MeTTa.SpaceTheory.HEAtomEntry
import Mettapedia.Languages.MeTTa.SpaceTheory.HEBodyEntry

/-!
# Replacing the type reads of one HE entry

An entry that delivers data asks no type question. Casting, interpreting
an application, and checking a completed grounded return have different
read supports. The original frames, diagnostics and continuation are
kept when those reads are preserved.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HETypedReplacement

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeLookupRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed
  (ArgumentService CastLookup InvocationSelection Policy Result WorldEnvironment rawLookup scopedLookup kindArgumentService)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Task Continuation)
open HEAtomEntry (Request Reply Licensed)
open HEFocused (Focus Leaf Parent)
open HETypeQueries (SameQuery SameOperands assignments)

def queryAt (lookup : CastLookup) (policy : Policy) (request : Request) (space : Space) : TypeLookupRel :=
  lookup (invocationTypeScope request.scope request.live (request.read policy).erase
    request.expected request.frame.bindings) space

structure EntryAgreement (service : ArgumentService) (before after : Space) (lookup : CastLookup)
    (p : Policy) (request : Request) : Prop where
  cast : request.action p .cast →
    SameQuery (queryAt lookup p request before) (queryAt lookup p request after) (request.read p).erase
  application : request.action p .interpret →
    ∀ head operands, request.expression p head operands →
      assignments before head.erase = assignments after head.erase ∧
      SameQuery (queryAt lookup p request before) (queryAt lookup p request after) head.erase ∧
      SameOperands service before after (queryAt lookup p request before) (queryAt lookup p request after)
        p (request.read p).erase

private theorem fields_erase {p : Policy} {request : Request} {operator : Entry.Value}
    {operands : List Entry.Value} (application : request.expression p operator operands) :
    (request.read p).erase = .expression (operator.erase :: operands.map Entry.Value.erase) := by
  obtain ⟨status, read⟩ := application
  simp only [read, Entry.Value.erase, List.map_cons]

private theorem query_of_assignments {before after : Space} {lookup : CastLookup} {subject : Atom}
    (chosen : lookup = rawLookup ∨ lookup = scopedLookup) (names : List String)
    (same : assignments before subject = assignments after subject) :
    SameQuery (lookup names before) (lookup names after) subject := by
  rcases chosen with rfl | rfl
  · exact HETypeQueries.raw_query same
  · exact HETypeQueries.scoped_query same names

/-- A concrete sufficient test for the two authored applicability
services. Compare the ordered assignments of the cast subject, or of
the operator and the actual operand atoms. No assignment for any
other subject is required. -/
theorem entry_of_assignments {service : ArgumentService} {before after : Space} {lookup : CastLookup}
    {p : Policy} {request : Request}
    (chosen : lookup = rawLookup ∨ lookup = scopedLookup)
    (role : service = .historical ∨ service = kindArgumentService)
    (cast : request.action p .cast → assignments before (request.read p).erase = assignments after (request.read p).erase)
    (application : request.action p .interpret → ∀ head operands, request.expression p head operands →
      ∀ subject ∈ head.erase :: operands.map Entry.Value.erase, assignments before subject = assignments after subject) :
    EntryAgreement service before after lookup p request := by
  have query {subject : Atom} (same : assignments before subject = assignments after subject) :
      SameQuery (queryAt lookup p request before) (queryAt lookup p request after) subject :=
    query_of_assignments chosen _ same
  constructor
  · exact fun admitted => query (cast admitted)
  · intro admitted head operands shaped
    have agrees (subject : Atom) (member : subject ∈ head.erase :: operands.map Entry.Value.erase) :
        SameQuery (queryAt lookup p request before) (queryAt lookup p request after) subject :=
      query (application admitted head operands shaped subject member)
    have forOperands (operator : Atom) (args : List Atom)
        (form : (request.read p).erase = .expression (operator :: args)) (subject : Atom) (member : subject ∈ args) :
        SameQuery (queryAt lookup p request before) (queryAt lookup p request after) subject := by
      have sameCons := Atom.expression.inj (form.symm.trans (fields_erase shaped))
      exact agrees subject (sameCons ▸ List.mem_cons_of_mem operator member)
    refine ⟨application admitted head operands shaped _ List.mem_cons_self,
      agrees _ List.mem_cons_self, ?_⟩
    rcases role with rfl | rfl
    · exact HETypeQueries.historical_operands forOperands
    · exact HETypeQueries.kind_operands forOperands

theorem entry_license_iff {service : ArgumentService} {before after : Space} {lookup : CastLookup}
    {p : Policy} {request : Request} (same : EntryAgreement service before after lookup p request)
    (reply : Reply) :
    Licensed service before lookup p request reply ↔ Licensed service after lookup p request reply := by
  have selected {head operands} (action : request.action p .interpret) (shaped : request.expression p head operands)
      (outcome : InvocationSelection) :
      service.selection before lookup p request.live request.scope (request.read p).erase
        head.erase request.expected request.frame outcome ↔
      service.selection after lookup p request.live request.scope (request.read p).erase
        head.erase request.expected request.frame outcome := by
    obtain ⟨_, operators, arguments⟩ := same.application action head operands shaped
    exact HETypeQueries.selection_iff operators arguments
  cases reply with
  | deliver => rfl
  | cast results =>
    constructor
    · rintro ⟨action, raw, batch, renewed⟩
      exact ⟨action, raw, (HETypeQueries.castBatch_iff (same.cast action)).mp batch,
        (HETypeQueries.castResults_iff (same.cast action)).mp renewed⟩
    · rintro ⟨action, raw, batch, renewed⟩
      exact ⟨action, raw, (HETypeQueries.castBatch_iff (same.cast action)).mpr batch,
        (HETypeQueries.castResults_iff (same.cast action)).mpr renewed⟩
  | tuple head operands =>
    exact and_congr_right fun action => and_congr_right fun shaped =>
      HETypeQueries.occurrences_iff (same.application action head operands shaped).1 _
  | selected head operands signature frames =>
    exact and_congr_right fun action => and_congr_right fun shaped =>
      selected action shaped (.selected signature frames)
  | fallback head operands errors =>
    exact and_congr_right fun action => and_congr_right fun shaped =>
      selected action shaped (.exhausted errors true)
  | failed head operands errors =>
    exact and_congr_right fun action => and_congr_right fun shaped =>
      selected action shaped (.exhausted errors false)

variable {Context World : Type}

theorem entry_step_iff (env : WorldEnvironment Context World) (other : World → Context → Space)
    (p : Policy) (request : Request) (world : World) (scope : Context)
    (same : EntryAgreement env.arguments (env.view world scope) (other world scope) env.lookup p request)
    (stack : List Continuation) (parents : List (Parent Context)) (published : List Result) (target : Focus Context World) :
    let source : Focus Context World := ⟨world, scope, .work request.task, stack, parents, published⟩
    HEFocused.Move env.arguments env.view env.services env.dispatch env.lookup p source target ↔
      HEFocused.Move env.arguments other env.services env.dispatch env.lookup p source target := by
  let alternative : WorldEnvironment Context World := {env with view := other}
  change HEFocused.Move env.arguments env.view env.services env.dispatch env.lookup p
    ⟨world, scope, .work request.task, stack, parents, published⟩ target ↔
    HEFocused.Move alternative.arguments alternative.view alternative.services alternative.dispatch alternative.lookup p
    ⟨world, scope, .work request.task, stack, parents, published⟩ target
  rw [HEAtomEntry.step_iff env, HEAtomEntry.step_iff alternative]
  constructor
  · rintro ⟨reply, licensed, reached⟩
    exact ⟨reply, (entry_license_iff same reply).mp licensed, reached⟩
  · rintro ⟨reply, licensed, reached⟩
    exact ⟨reply, (entry_license_iff same reply).mpr licensed, reached⟩

def BodyAgreement (before after : Space) (lookup : CastLookup) (task : Task) : Prop :=
  ∀ live scope caller original expected value activation,
    task = .boundary live scope caller (.native original (some expected) .completed) value activation →
    ¬CompletedNativeKeepRel value.erase expected →
    SameQuery (lookup (invocationTypeScope scope live original.erase expected activation.bindings) before)
      (lookup (invocationTypeScope scope live original.erase expected activation.bindings) after) value.erase

theorem BodyAgreement.symm {before after : Space} {lookup : CastLookup} {task : Task}
    (same : BodyAgreement before after lookup task) : BodyAgreement after before lookup task :=
  fun l s c a e v f shape notKept => (same l s c a e v f shape notKept).symm

private theorem body_move {before after : Space} {lookup : CastLookup} {p : Policy} {task : Task}
    {body : Leaf} {frames : List Continuation} (same : BodyAgreement before after lookup task)
    (planned : HEBodyEntry.Plan before lookup p task body frames) : HEBodyEntry.Plan after lookup p task body frames := by
  cases planned with
  | beginBody => exact .beginBody
  | chain => exact .chain
  | bodyTerminal terminal => exact .bodyTerminal terminal
  | bodyResume resume => exact .bodyResume resume
  | functionReturn => exact .functionReturn
  | functionNoReturn absent => exact .functionNoReturn absent
  | producerRaw raw => exact .producerRaw raw
  | producerFunction runs => exact .producerFunction runs
  | acceptReturn => exact .acceptReturn
  | batchNil => exact .batchNil
  | batchCons => exact .batchCons
  | nativeEmittedRaw => exact .nativeEmittedRaw
  | nativeEmittedTyped => exact .nativeEmittedTyped
  | nativeCompletedRaw => exact .nativeCompletedRaw
  | nativeCompletedTyped returned =>
    apply HEBodyEntry.Plan.nativeCompletedTyped
    cases returned with
    | keep kept => exact .keep kept
    | cast notKept batch results =>
      have agreed := same _ _ _ _ _ _ _ rfl notKept
      exact .cast notKept (HETypeQueries.castBatch_iff agreed |>.mp batch)
        (HETypeQueries.castResults_iff agreed |>.mp results)
  | refused refused => exact .refused refused
  | stopped stopped => exact .stopped stopped
  | evaluate computes success => exact .evaluate computes success

theorem body_step_iff (env : WorldEnvironment Context World) (other : World → Context → Space)
    (p : Policy) (task : Task) (covered : HEBodyEntry.covered task = true) (world : World) (scope : Context)
    (same : BodyAgreement (env.view world scope) (other world scope) env.lookup task)
    (stack : List Continuation) (parents : List (Parent Context)) (published : List Result) (target : Focus Context World) :
    let source : Focus Context World := ⟨world, scope, .work task, stack, parents, published⟩
    HEFocused.Move env.arguments env.view env.services env.dispatch env.lookup p source target ↔
      HEFocused.Move env.arguments other env.services env.dispatch env.lookup p source target := by
  let alternative : WorldEnvironment Context World := {env with view := other}
  change HEFocused.Move env.arguments env.view env.services env.dispatch env.lookup p
    ⟨world, scope, .work task, stack, parents, published⟩ target ↔
    HEFocused.Move alternative.arguments alternative.view alternative.services alternative.dispatch alternative.lookup p
    ⟨world, scope, .work task, stack, parents, published⟩ target
  rw [HEBodyEntry.step_iff env p task covered, HEBodyEntry.step_iff alternative p task covered]
  constructor
  · rintro ⟨body, frames, planned, reached⟩
    exact ⟨body, frames, body_move same planned, reached⟩
  · rintro ⟨body, frames, planned, reached⟩
    exact ⟨body, frames, body_move same.symm planned, reached⟩

end Mettapedia.Languages.MeTTa.SpaceTheory.HETypedReplacement
