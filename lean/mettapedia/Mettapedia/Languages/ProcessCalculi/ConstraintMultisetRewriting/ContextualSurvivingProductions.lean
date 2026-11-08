import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUniformBirthProblem
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleOrigins

/-!
# Surviving source rows refer to their actual creation descriptors

Compilation tracks the latest production of each logical occurrence by an
index into the saved birth list. The lookup reads the authored selections,
not the final row store. Retained input rows keep their original capture
transport. The resulting descriptor connects final row origins to the
existing uniform solver's per-birth publication theorem.
-/

set_option autoImplicit false

universe u v

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows

variable {S : Signature} {V W O : Type} {declaration : V → MetaArity S} {later : W → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt}

def Birth.origin (birth : Birth declaration O Γ sort) : Origin declaration Γ sort :=
  if birth.reusable then .schema birth.saved birth.problem birth.value
  else .shared (instantiate birth.transport birth.value)

theorem Birth.origin_map (birth : Birth declaration O Γ sort) (change : Assignment declaration later) :
    (birth.map change).origin = birth.origin.map change := by
  unfold Birth.origin Birth.map
  split <;> simp only [Origin.map, Assignment.instantiate_compose]

theorem assign_none_iff {A : Type u} [DecidableEq O] (keys : List O) (values : List A)
    (unique : keys.Nodup) (lengths : keys.length = values.length) (key : O) :
    ContextualTemplateSource.assign keys values key = none ↔ key ∉ keys := by
  constructor
  · intro missing member
    obtain ⟨port, rfl⟩ := List.mem_iff_get.mp member
    have found := ContextualTemplateSource.assign_get keys values unique lengths port
    rw [missing] at found
    cases found
  · intro outside
    cases found : ContextualTemplateSource.assign keys values key with
    | none => rfl
    | some value => exact False.elim (outside (ContextualTemplateSource.assign_mem keys values key value found))

namespace Schedule

variable [DecidableEq O] {First Last : Type} {first : First → MetaArity S} {last : Last → MetaArity S}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

section Snoc

variable {Middle Query : Type} {middle : Middle → MetaArity S}
    [DecidableEq Middle] [DecidableEq Query]
    {mid : ContextualClauseSourceState.World middle O Γ sort}
    (past : Schedule S O Γ sort before mid) (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries mid.declarations)) Γ sort))
    (picked : Selection O)

def previousBirthIndex (index : past.BirthIndex) : (Schedule.snoc past queries plan picked).BirthIndex :=
  ⟨index.val, by simpa only [BirthIndex, births, List.length_append, List.length_map] using
    Nat.lt_add_right (originalBirths mid queries plan picked).length index.isLt⟩

def createdBirthIndex (port : Fin plan.rule.produce.length) : (Schedule.snoc past queries plan picked).BirthIndex :=
  ⟨past.births.length + port.val, by
    change _ < (past.births.map _ ++ originalBirths mid queries plan picked).length
    simp only [List.length_append, List.length_map, originalBirths, List.length_ofFn]
    omega⟩

theorem previous_birth (index : past.BirthIndex) :
    (Schedule.snoc past queries plan picked).births.get (previousBirthIndex past queries plan picked index) =
      (past.births.get index).map (captureFrame queries middle mid.declarations).assignment := by
  change (past.births.map (Birth.map (captureFrame queries middle mid.declarations).assignment) ++
    originalBirths mid queries plan picked)[index.val] = _
  rw [List.getElem_append_left (by simpa only [List.length_map] using index.isLt), List.getElem_map]
  rfl

theorem created_birth (port : Fin plan.rule.produce.length) :
    (Schedule.snoc past queries plan picked).births.get (createdBirthIndex past queries plan picked port) =
      (originalBirths mid queries plan picked).get ⟨port.val, by simp [originalBirths, port.isLt]⟩ := by
  change (past.births.map (Birth.map (captureFrame queries middle mid.declarations).assignment) ++
    originalBirths mid queries plan picked)[past.births.length + port.val]'(by
      simp only [List.length_append, List.length_map, originalBirths, List.length_ofFn]
      omega) = _
  rw [List.getElem_append_right (by simp only [List.length_map]; omega)]
  simp only [List.length_map, Nat.add_sub_cancel_left, List.get_eq_getElem]

theorem created_birth_origin (port : Fin plan.rule.produce.length) :
    ((Schedule.snoc past queries plan picked).births.get (createdBirthIndex past queries plan picked port)).origin =
      producedOrigin middle mid queries plan picked port := by
  rw [created_birth]
  unfold originalBirths
  rw [List.get_ofFn]
  change (if plan.reusable.get ⟨port.val, _⟩ then
    Origin.schema _ _ _ else Origin.shared (instantiate (generator _) _)) = _
  rw [instantiate_identity]
  rfl

end Snoc

def productionIndex : {First : Type} → {first : First → MetaArity S} →
    {before : ContextualClauseSourceState.World first O Γ sort} →
    {Last : Type} → {last : Last → MetaArity S} →
    {after : ContextualClauseSourceState.World last O Γ sort} →
    (schedule : Schedule S O Γ sort before after) → O → Option schedule.BirthIndex
  | _, _, _, _, _, _, .nil _, _ => none
  | _, _, _, _, _, _, @Schedule.snoc _ _ _ _ _ _ _ _ _ _ _ _ start _ past queries plan picked, occurrence =>
      (ContextualTemplateSource.assign picked.made
        (List.ofFn (createdBirthIndex past queries plan picked)) occurrence).or
        ((productionIndex (before := start) past occurrence).map (previousBirthIndex past queries plan picked))

def productionOrigin (schedule : Schedule S O Γ sort before after) (occurrence : O) : Origin after.declarations Γ sort :=
  ((schedule.productionIndex occurrence).map fun index => (schedule.births.get index).origin).getD
    (.retained first before.declarations (before.rows occurrence) schedule.frame.assignment)

/-- The saved production index selects exactly the independently compiled origin. -/
theorem production_origin (schedule : Schedule S O Γ sort before after) (occurrence : O) :
    schedule.productionOrigin occurrence = schedule.origins occurrence := by
  induction schedule with
  | nil start =>
      simp only [productionOrigin, productionIndex, origins, Option.map_none, Option.getD_none]
      congr 1
  | @snoc Middle Query _ middle _ _ start mid past queries plan picked prior =>
      let birthOrigin := fun index : (Schedule.snoc past queries plan picked).BirthIndex =>
        ((Schedule.snoc past queries plan picked).births.get index).origin
      have current :
          (ContextualTemplateSource.assign picked.made
            (List.ofFn (createdBirthIndex past queries plan picked)) occurrence).map birthOrigin =
            ContextualTemplateSource.assign picked.made
              (List.ofFn (producedOrigin middle mid queries plan picked)) occurrence := by
        rw [ContextualTemplateSource.assign_values_map, List.map_ofFn]
        congr 2
        funext port
        exact created_birth_origin past queries plan picked port
      have previous :
          ((past.productionIndex occurrence).map (previousBirthIndex past queries plan picked)).map birthOrigin =
            ((past.productionIndex occurrence).map fun index => (past.births.get index).origin).map
              (Origin.map (captureFrame queries middle mid.declarations).assignment) := by
        simp only [Option.map_map]
        apply congrArg (fun f => Option.map f (past.productionIndex occurrence))
        funext index
        exact (congrArg Birth.origin (previous_birth past queries plan picked index)).trans
          ((past.births.get index).origin_map _)
      simp only [productionOrigin, productionIndex, Option.map_or]
      rw [current, previous, Option.getD_or]
      have inherited :
          Origin.retained _ start.declarations (start.rows occurrence)
            (Schedule.snoc past queries plan picked).frame.assignment =
          (Origin.retained _ start.declarations (start.rows occurrence) past.frame.assignment).map
            (captureFrame queries middle mid.declarations).assignment := by
        rw [frame_snoc_assignment]
        rfl
      rw [inherited, Option.getD_map]
      change (ContextualTemplateSource.assign picked.made
        (List.ofFn (producedOrigin middle mid queries plan picked)) occurrence).getD
        ((past.productionOrigin occurrence).map (captureFrame queries middle mid.declarations).assignment) = _
      rw [prior]
      simp only [origins]

/-- A selected creation is the origin of this final row, before any native publication. -/
theorem selected_production_origin (schedule : Schedule S O Γ sort before after) (occurrence : O)
    (index : schedule.BirthIndex) (selected : schedule.productionIndex occurrence = some index) :
    (schedule.births.get index).origin = schedule.origins occurrence := by
  have compiled := schedule.production_origin occurrence
  simpa only [productionOrigin, selected, Option.map_some, Option.getD_some] using compiled

/-- A retained-input lookup is chosen exactly when no clause produced this occurrence. -/
theorem productionIndex_none_iff_shapes (schedule : Schedule S O Γ sort before after) (shapes : schedule.ShapesHold)
    (occurrence : O) :
    schedule.productionIndex occurrence = none ↔ ∀ picked ∈ schedule.selections, occurrence ∉ picked.made := by
  induction schedule with
  | nil _ => simp only [productionIndex, selections, List.not_mem_nil, false_implies, implies_true]
  | @snoc Middle Query _ middle _ _ start mid past queries plan picked prior =>
      have steps := (shapes_snoc past queries plan picked).mp shapes
      have distinct : picked.made.Nodup := steps.2.2.1
      have outputs : picked.made.length = plan.rule.produce.length := steps.2.2.2.2.2
      simp only [productionIndex, Option.or_eq_none_iff, Option.map_eq_none_iff]
      rw [assign_none_iff _ _ distinct
        (by simpa only [List.length_ofFn] using outputs), prior steps.1]
      change (occurrence ∉ picked.made ∧ ∀ selection ∈ past.selections, occurrence ∉ selection.made) ↔
        ∀ selection ∈ past.selections ++ [picked], occurrence ∉ selection.made
      rw [List.forall_mem_append, List.forall_mem_singleton]
      exact and_comm

theorem productionIndex_none_iff (schedule : Schedule S O Γ sort before after) (admitted : schedule.Admitted)
    (occurrence : O) :
    schedule.productionIndex occurrence = none ↔ ∀ picked ∈ schedule.selections, occurrence ∉ picked.made :=
  schedule.productionIndex_none_iff_shapes (schedule.admitted_characterization.mp admitted).1 occurrence

def outputValue (schedule : Schedule S O Γ sort before after) (index : schedule.BirthIndex) :
    Term (signature S schedule.uniformFamily) Γ sort :=
  let birth := schedule.births.get index
  if birth.reusable then
    instantiate (ContextualIndependentProblems.inclusion schedule.blockVariables schedule.blockDeclarations (some index)) birth.value
  else
    instantiate (ContextualIndependentProblems.inclusion schedule.blockVariables schedule.blockDeclarations none)
      (instantiate birth.transport birth.value)

end Schedule

namespace UniformComputed

variable [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    {First Last : Type} {first : First → MetaArity S} {last : Last → MetaArity S}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}
    {schedule : Schedule S O Γ sort before after} {fuel : Nat}
    (result : UniformComputed schedule fuel)

def currentEmbedding : Assignment after.declarations result.family :=
  Assignment.compose (ContextualComputedFreshFrame.includeSource result.update)
    (ContextualIndependentProblems.inclusion schedule.blockVariables schedule.blockDeclarations none)

/-- Exactly the ordinary/shared output forms already used by native firings. -/
def outputRow {Local : Type} (locals : Local → MetaArity S) (index : schedule.BirthIndex) :
    Row (ContextualPublication.privateFamily locals result.update.declaration) result.family Γ sort :=
  if (schedule.births.get index).reusable then
    ContextualConditionalPublication.ordinary locals result.update.declaration _
      (ContextualConditionalAnswers.ofUpdate result.update (schedule.outputValue index))
  else
    ofStored _ _ (.shared (instantiate (ContextualComputedFreshFrame.includeSource result.update) (schedule.outputValue index)))

theorem output_origin_instances {Local Next : Type} (locals : Local → MetaArity S)
    (index : schedule.BirthIndex) (next : Next → MetaArity S)
    (candidate : Assignment result.family next) (pattern : Term (signature S next) Γ sort) :
    Matches (ContextualPublication.privateFamily locals result.update.declaration) result.family candidate pattern
      (result.outputRow locals index) ↔
      (schedule.births.get index).origin.Instances (Assignment.compose candidate result.currentEmbedding) pattern := by
  by_cases ordinary : (schedule.births.get index).reusable = true
  · simp only [outputRow, ordinary, ite_true, Schedule.outputValue, Birth.origin]
    change Matches _ _ candidate pattern (result.birthRow locals index) ↔
      ContextualPublication.SourceInstances _ _ next pattern
    exact result.birth_row_instances locals index next candidate pattern
  · have shared : (schedule.births.get index).reusable = false := Bool.eq_false_iff.mpr ordinary
    simp only [outputRow, Schedule.outputValue, Birth.origin, shared, Bool.false_eq_true, if_false,
      ofStored_matches_iff, ContextualGuardMatching.shared_matches_iff, Origin.Instances,
      currentEmbedding, Assignment.instantiate_compose]
    exact Iff.of_eq (congrArg (fun value => pattern = instantiate candidate value)
      (Assignment.instantiate_compose (ContextualComputedFreshFrame.includeSource result.update)
        (ContextualIndependentProblems.inclusion schedule.blockVariables schedule.blockDeclarations none)
        (instantiate (schedule.births.get index).transport (schedule.births.get index).value)).symm)

/-- Every surviving output has its exact source row meaning under the returned caller environment. -/
theorem surviving_output_instances {Local Next : Type} (locals : Local → MetaArity S)
    (occurrence : O) (index : schedule.BirthIndex) (selected : schedule.productionIndex occurrence = some index)
    (next : Next → MetaArity S) (candidate : Assignment result.family next)
    (pattern : Term (signature S next) Γ sort) :
    Matches (ContextualPublication.privateFamily locals result.update.declaration) result.family candidate pattern
      (result.outputRow locals index) ↔
      Matches last after.declarations (Assignment.compose candidate result.currentEmbedding) pattern (after.rows occurrence) := by
  rw [result.output_origin_instances locals index next candidate pattern,
    schedule.selected_production_origin occurrence index selected]
  exact schedule.origins_instances result.admitted next (Assignment.compose candidate result.currentEmbedding) pattern occurrence

/-- Retained input rows and compiled productions share the native output private bank. -/
def compiledRow (occurrence : O) :
    Row (ContextualPublication.privateFamily first result.update.declaration) result.family Γ sort :=
  match schedule.productionIndex occurrence with
  | some index => result.outputRow first index
  | none =>
      ContextualConditionalPublication.extendPrivate first result.update.declaration result.family
        ((before.rows occurrence).map first before.declarations
          (Assignment.compose result.currentEmbedding schedule.frame.assignment))

/-- The complete compiled row store preserves every source observation under the same caller environment. -/
theorem compiled_row_instances {Next : Type} (occurrence : O) (next : Next → MetaArity S)
    (candidate : Assignment result.family next) (pattern : Term (signature S next) Γ sort) :
    Matches (ContextualPublication.privateFamily first result.update.declaration) result.family candidate pattern
      (result.compiledRow occurrence) ↔
      Matches last after.declarations (Assignment.compose candidate result.currentEmbedding) pattern (after.rows occurrence) := by
  cases selected : schedule.productionIndex occurrence with
  | some index =>
      simp only [compiledRow, selected]
      exact result.surviving_output_instances first occurrence index selected next candidate pattern
  | none =>
      simp only [compiledRow, selected, ContextualConditionalPublication.extendPrivate_matches_iff, matches_map_iff]
      have origin := schedule.production_origin occurrence
      simp only [Schedule.productionOrigin, selected, Option.map_none, Option.getD_none] at origin
      have source := schedule.origins_instances result.admitted next
        (Assignment.compose candidate result.currentEmbedding) pattern occurrence
      rw [← origin] at source
      change Matches first before.declarations
        (Assignment.compose (Assignment.compose candidate result.currentEmbedding) schedule.frame.assignment) pattern
          (before.rows occurrence) ↔ _ at source
      rw [← Assignment.compose_associative] at source
      exact source

end UniformComputed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules
