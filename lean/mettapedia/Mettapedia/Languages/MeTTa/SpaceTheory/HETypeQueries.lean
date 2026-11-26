import Mettapedia.Languages.MeTTa.HE.ArgumentAdmission

/-!
# Which type questions HE can reuse

The historical and scoped type queries read the ordered assignments of
one exact subject. The subject may be an expression, not only a head
symbol. An application reads its operator and the type questions of its
operand policy. A cast reads its one subject, including when it renews
the caller's bindings. None of these facts equates two entire spaces.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HETypeQueries

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings ResultPair ResultSet)
open Mettapedia.Languages.MeTTa.HE.Spec.Type
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed

def assignments (space : Space) (subject : Atom) : List Atom :=
  space.atoms.filterMap (annotationType? subject)

private theorem annotations_iff {before after : Space} {subject : Atom}
    (same : assignments before subject = assignments after subject) (types : List Atom) :
    AnnotationTypesRel subject before.atoms types ↔ AnnotationTypesRel subject after.atoms types := by
  constructor
  · intro fromBefore
    have identifies : assignments before subject = types := (AnnotationTypesRel.complete _ _).unique fromBefore
    rw [same] at identifies
    exact identifies ▸ AnnotationTypesRel.complete _ _
  · intro fromAfter
    have identifies : assignments after subject = types := (AnnotationTypesRel.complete _ _).unique fromAfter
    rw [← same] at identifies
    exact identifies ▸ AnnotationTypesRel.complete _ _

private theorem storage_move {before after : Space} {subject : Atom} {types : List Atom}
    (same : assignments before subject = assignments after subject)
    (seen : StorageTypesRel before subject types) : StorageTypesRel after subject types := by
  cases seen with
  | «variable» => exact .variable _ _
  | groundedKnown known defined => exact .groundedKnown known defined
  | groundedUndefined known => exact .groundedUndefined known
  | symbolKnown supplied nonempty => exact .symbolKnown ((annotations_iff same _).mp supplied) nonempty
  | symbolUndefined missing => exact .symbolUndefined ((annotations_iff same _).mp missing)
  | unit => exact .unit _
  | expressionKnown supplied nonempty => exact .expressionKnown ((annotations_iff same _).mp supplied) nonempty
  | expressionUndefined missing => exact .expressionUndefined ((annotations_iff same _).mp missing)

theorem storage_iff {before after : Space} {subject : Atom}
    (same : assignments before subject = assignments after subject) (types : List Atom) :
    StorageTypesRel before subject types ↔ StorageTypesRel after subject types :=
  ⟨storage_move same, storage_move same.symm⟩

private theorem occurrences_move {before after : Space} {subject : Atom} {types : Multiset Atom}
    (same : assignments before subject = assignments after subject)
    (seen : TypeOccurrencesRel (before.atoms : Multiset Atom) subject types) :
    TypeOccurrencesRel (after.atoms : Multiset Atom) subject types := by
  obtain ⟨ordered, queried⟩ := StorageTypesRel.total before subject
  have result := TypeOccurrencesRel.unique queried.occurrences seen
  exact result ▸ (storage_move same queried).occurrences

theorem occurrences_iff {before after : Space} {subject : Atom}
    (same : assignments before subject = assignments after subject) (types : Multiset Atom) :
    TypeOccurrencesRel (before.atoms : Multiset Atom) subject types ↔
      TypeOccurrencesRel (after.atoms : Multiset Atom) subject types :=
  ⟨occurrences_move same, occurrences_move same.symm⟩

/-- Exact agreement of the complete type lists, retaining their order.
Bindings and demand may vary as other operands are checked. -/
def SameQuery (before after : TypeLookupRel) (subject : Atom) : Prop :=
  ∀ bindings demand types, before bindings subject demand types ↔ after bindings subject demand types

theorem SameQuery.symm {before after : TypeLookupRel} {subject : Atom}
    (same : SameQuery before after subject) : SameQuery after before subject :=
  fun b d t => (same b d t).symm

theorem raw_query {before after : Space} {subject : Atom}
    (same : assignments before subject = assignments after subject) :
    SameQuery (rawTypeLookupRel before) (rawTypeLookupRel after) subject :=
  fun _ _ types => storage_iff same types

theorem scoped_query {before after : Space} {subject : Atom}
    (same : assignments before subject = assignments after subject) (scope : List String) :
    SameQuery (scopedTypeLookup scope before) (scopedTypeLookup scope after) subject := by
  intro bindings expected candidates
  constructor
  · rintro ⟨types, queried, fresh⟩
    exact ⟨types, (storage_iff same types).mp queried, fresh⟩
  · rintro ⟨types, queried, fresh⟩
    exact ⟨types, (storage_iff same types).mpr queried, fresh⟩

private theorem castBatch_move {before after : Space} {first second : TypeLookupRel}
    {subject expected : Atom} {bindings : Bindings} {raw : ResultSet}
    {matching : Atom → Atom → Bindings → Bindings → Prop}
    (same : SameQuery first second subject)
    (cast : TypeCastBatchRel before subject expected bindings raw (lookup := first) (matching := matching)) :
    TypeCastBatchRel after subject expected bindings raw (lookup := second) (matching := matching) := by
  cases cast with
  | success queried chosen earlier matched => exact .success ((same _ _ _).mp queried) chosen earlier matched
  | failure queried rejected => exact .failure ((same _ _ _).mp queried) rejected

theorem castBatch_iff {before after : Space} {first second : TypeLookupRel}
    {subject expected : Atom} {bindings : Bindings} {raw : ResultSet}
    {matching : Atom → Atom → Bindings → Bindings → Prop}
    (same : SameQuery first second subject) :
    TypeCastBatchRel before subject expected bindings raw (lookup := first) (matching := matching) ↔
      TypeCastBatchRel after subject expected bindings raw (lookup := second) (matching := matching) :=
  ⟨castBatch_move same, castBatch_move same.symm⟩

private theorem castResult_move {first second : TypeLookupRel} {subject : Entry.Value}
    {expected : Atom} {policy : Policy} {caller : Frame} {raw : ResultPair} {result : Result}
    (same : SameQuery first second subject.erase)
    (checked : CastResultRel policy first caller subject expected raw result) :
    CastResultRel policy second caller subject expected raw result := by
  obtain ⟨readout, renew, payload⟩ := checked
  refine ⟨readout, ?_, payload⟩
  cases renew with
  | same => exact .same _
  | matched queried selected rejected matched unified =>
    exact .matched ((same _ _ _).mp queried) selected rejected matched unified

theorem castResults_iff {first second : TypeLookupRel} {subject : Entry.Value}
    {expected : Atom} {policy : Policy} {caller : Frame} {raw : List ResultPair} {results : List Result}
    (same : SameQuery first second subject.erase) :
    List.Forall₂ (CastResultRel policy first caller subject expected) raw results ↔
      List.Forall₂ (CastResultRel policy second caller subject expected) raw results :=
  ⟨List.Forall₂.imp (fun _ _ h => castResult_move same h),
    List.Forall₂.imp (fun _ _ h => castResult_move same.symm h)⟩

private theorem nativeReturn_move {before after : Space} {first second : TypeLookupRel}
    {policy : Policy} {value : Entry.Value} {expected : Atom} {caller : Frame} {results : List Result}
    (same : SameQuery first second value.erase)
    (returned : NativeCompletedReturnRel before first policy value expected caller results) :
    NativeCompletedReturnRel after second policy value expected caller results := by
  cases returned with
  | keep kept => exact .keep kept
  | cast notKept cast results => exact .cast notKept (castBatch_move same cast) ((castResults_iff same).mp results)

theorem nativeReturn_iff {before after : Space} {first second : TypeLookupRel}
    {policy : Policy} {value : Entry.Value} {expected : Atom} {caller : Frame} {results : List Result}
    (same : SameQuery first second value.erase) :
    NativeCompletedReturnRel before first policy value expected caller results ↔
      NativeCompletedReturnRel after second policy value expected caller results :=
  ⟨nativeReturn_move same, nativeReturn_move same.symm⟩

private theorem arguments_move {before after : Space} {first second : TypeLookupRel}
    {policy : Policy} {expression argument expected : Atom} {position : Nat}
    {frames outputs : List Frame} {errors : List Atom}
    (same : SameQuery first second argument)
    (checked : ArgumentChecksRel before first policy expression argument expected position frames outputs errors) :
    ArgumentChecksRel after second policy expression argument expected position frames outputs errors := by
  induction checked with
  | nil => exact .nil
  | cons queried checked _ ih => exact .cons ((same _ _ _).mp queried) checked ih

theorem kind_operand_iff {before after : Space} {first second : TypeLookupRel}
    {policy : Policy} {expression operand formal : Atom} {position : Nat} {caller : Frame}
    {frames : List Frame} {errors : List Atom}
    (queries : SameQuery first second operand) :
    KindArgumentAdmissionRel before first policy expression operand formal position caller frames errors ↔
      KindArgumentAdmissionRel after second policy expression operand formal position caller frames errors := by
  constructor
  · intro step
    cases step with
    | kind shape permitted => exact .kind shape permitted
    | inferred absent checked => exact .inferred absent (arguments_move queries checked)
  · intro step
    cases step with
    | kind shape permitted => exact .kind shape permitted
    | inferred absent checked => exact .inferred absent (arguments_move queries.symm checked)

/-- If a formal holds its operand, even a change of the inferred type
answers does not affect admission. This is a judgment about the authored
formal and operand kind, not a guess based on the observed result. -/
theorem held_operand_iff {before after : Space} {first second : TypeLookupRel}
    {policy : Policy} {expression operand formal kind : Atom} {position : Nat} {caller : Frame}
    {frames : List Frame} {errors : List Atom}
    (shape : MetaTypeRel operand kind) (holds : ArgumentKindCut formal kind) :
    KindArgumentAdmissionRel before first policy expression operand formal position caller frames errors ↔
      KindArgumentAdmissionRel after second policy expression operand formal position caller frames errors := by
  constructor
  · intro admitted
    obtain ⟨rfl, rfl⟩ := admitted.kind_exact shape holds
    exact .kind shape holds
  · intro admitted
    obtain ⟨rfl, rfl⟩ := admitted.kind_exact shape holds
    exact .kind shape holds

def operandPolicy : ArgumentService → ArgumentAdmission
  | .historical => queriedArgument
  | .role admit => admit

def SameOperand (admit : ArgumentAdmission) (before after : Space) (first second : TypeLookupRel)
    (policy : Policy) (expression operand : Atom) : Prop :=
  ∀ formal position frame frames errors,
    admit before first policy expression operand formal position frame frames errors ↔
      admit after second policy expression operand formal position frame frames errors

def SameOperands (service : ArgumentService) (before after : Space) (first second : TypeLookupRel)
    (policy : Policy) (expression : Atom) : Prop :=
  ∀ operator operands, expression = .expression (operator :: operands) →
    ∀ operand ∈ operands, SameOperand (operandPolicy service) before after first second policy expression operand

theorem SameOperands.symm {service : ArgumentService} {before after : Space} {first second : TypeLookupRel}
    {policy : Policy} {expression : Atom} (same : SameOperands service before after first second policy expression) :
    SameOperands service after before second first policy expression :=
  fun op args shape arg member f i b bs e => (same op args shape arg member f i b bs e).symm

theorem historical_operands {before after : Space} {first second : TypeLookupRel}
    {policy : Policy} {expression : Atom}
    (same : ∀ operator operands, expression = .expression (operator :: operands) →
      ∀ operand ∈ operands, SameQuery first second operand) :
    SameOperands .historical before after first second policy expression := by
  intro operator operands shape operand member formal position frame frames errors
  have agreed := same operator operands shape operand member
  exact ⟨arguments_move agreed, arguments_move agreed.symm⟩

theorem kind_operands {before after : Space} {first second : TypeLookupRel}
    {policy : Policy} {expression : Atom}
    (same : ∀ operator operands, expression = .expression (operator :: operands) →
      ∀ operand ∈ operands, SameQuery first second operand) :
    SameOperands kindArgumentService before after first second policy expression :=
  fun operator operands shape operand member _ _ _ _ _ =>
    kind_operand_iff (same operator operands shape operand member)

private theorem frames_move {admit : ArgumentAdmission} {before after : Space} {first second : TypeLookupRel}
    {policy : Policy} {expression operand formal : Atom} {position : Nat} {input output : List Frame}
    {errors : List Atom}
    (same : SameOperand admit before after first second policy expression operand)
    (frames : AdmissionFramesRel admit before first policy expression operand formal position input output errors) :
    AdmissionFramesRel admit after second policy expression operand formal position input output errors := by
  induction frames with
  | nil => exact .nil
  | cons accepted _ ih => exact .cons ((same _ _ _ _ _).mp accepted) ih

private theorem operands_move {admit : ArgumentAdmission} {before after : Space} {first second : TypeLookupRel}
    {policy : Policy} {expression : Atom} {position : Nat} {operands formals : List Atom} {input output : List Frame}
    {errors : List Atom}
    (same : ∀ operand ∈ operands, SameOperand admit before after first second policy expression operand)
    (used : AdmissionArgumentsRel admit before first policy expression position operands formals input output errors) :
    AdmissionArgumentsRel admit after second policy expression position operands formals input output errors := by
  induction used with
  | nil => exact .nil
  | cons checked _ ih =>
    exact .cons (frames_move (same _ List.mem_cons_self) checked)
      (ih fun operand member => same operand (List.mem_cons_of_mem _ member))

private theorem application_move {service : ArgumentService} {before after : Space} {first second : TypeLookupRel}
    {policy : Policy} {expression expected : Atom} {signature : SelectedTypePolicy} {caller : Frame}
    {frames : List Frame} {errors : List Atom}
    (same : SameOperands service before after first second policy expression)
    (accepted : AdmissionApplicationRel (operandPolicy service) before first policy expression expected
      signature caller frames errors) :
    AdmissionApplicationRel (operandPolicy service) after second policy expression expected signature caller frames errors := by
  cases accepted with
  | wrongArity shape incorrect => exact .wrongArity shape incorrect
  | checked shape operands results => exact .checked shape (operands_move (same _ _ shape) operands) results

private theorem scan_move {service : ArgumentService} {before after : Space} {first second : TypeLookupRel}
    {policy : Policy} {expression expected : Atom} {caller : Frame} {candidates : List Atom} {outcome : InvocationSelection}
    (same : SameOperands service before after first second policy expression)
    (scanned : AdmissionScanRel (operandPolicy service) before first policy expression expected caller candidates outcome) :
    AdmissionScanRel (operandPolicy service) after second policy expression expected caller candidates outcome := by
  induction scanned with
  | nil => exact .nil
  | nonFunction absent _ ih => exact .nonFunction absent ih
  | selected checked nonempty => exact .selected (application_move same checked) nonempty
  | rejected checked _ ih => exact .rejected (application_move same checked) ih

private theorem selection_role_iff (service : ArgumentService) {space : Space} {lookup : CastLookup}
    {policy : Policy} {live : List Atom} {scope : List String} {expression operator expected : Atom}
    {caller : Frame} {outcome : InvocationSelection} :
    service.selection space lookup policy live scope expression operator expected caller outcome ↔
      (ArgumentService.role (operandPolicy service)).selection space lookup policy live scope
        expression operator expected caller outcome := by
  cases service with
  | historical => exact queried_role_selection_iff.symm
  | role _ => rfl

theorem selection_iff {service : ArgumentService} {before after : Space} {lookup : CastLookup}
    {policy : Policy} {live : List Atom} {scope : List String} {expression operator expected : Atom}
    {caller : Frame} {outcome : InvocationSelection}
    (operators : SameQuery
      (lookup (invocationTypeScope scope live expression expected caller.bindings) before)
      (lookup (invocationTypeScope scope live expression expected caller.bindings) after) operator)
    (operands : SameOperands service before after
      (lookup (invocationTypeScope scope live expression expected caller.bindings) before)
      (lookup (invocationTypeScope scope live expression expected caller.bindings) after) policy expression) :
    service.selection before lookup policy live scope expression operator expected caller outcome ↔
      service.selection after lookup policy live scope expression operator expected caller outcome := by
  refine (selection_role_iff service).trans (Iff.trans ?_ (selection_role_iff service).symm)
  constructor
  · rintro ⟨candidates, queried, checked⟩
    exact ⟨candidates, (operators _ _ _).mp queried, scan_move operands checked⟩
  · rintro ⟨candidates, queried, checked⟩
    exact ⟨candidates, (operators _ _ _).mpr queried, scan_move operands.symm checked⟩

section Controls

private def head : Atom := .symbol "measure"
private def value : Atom := .symbol "sensor"
private def expression : Atom := .expression [head, value]
private def typeOf (subject type : Atom) : Atom := .expression [.symbol ":", subject, type]
private def returnType : Atom := .symbol "Reading"

theorem unrelated_assignment_keeps_exact_query :
    SameQuery (rawTypeLookupRel (Space.ofList [typeOf expression returnType]))
      (rawTypeLookupRel (Space.ofList [typeOf value (.symbol "Device"), typeOf expression returnType]))
      expression := raw_query (by decide +kernel)

theorem equal_head_assignments_do_not_protect_expression_cast :
    assignments Space.empty head = assignments (Space.ofList [typeOf expression returnType]) head ∧
      ¬SameQuery (rawTypeLookupRel Space.empty)
        (rawTypeLookupRel (Space.ofList [typeOf expression returnType])) expression := by
  refine ⟨by decide +kernel, ?_⟩
  intro same
  have typed : StorageTypesRel (Space.ofList [typeOf expression returnType]) expression [returnType] :=
    .expressionKnown (.hit .nil) (by simp)
  have old : StorageTypesRel Space.empty expression [returnType] :=
    (same Bindings.empty Atom.undefinedType _).mpr typed
  have unspecified : StorageTypesRel Space.empty expression [Atom.undefinedType] :=
    .expressionUndefined .nil
  have impossible := old.unique unspecified
  exact (by decide : [returnType] ≠ [Atom.undefinedType]) impossible

end Controls

end Mettapedia.Languages.MeTTa.SpaceTheory.HETypeQueries
