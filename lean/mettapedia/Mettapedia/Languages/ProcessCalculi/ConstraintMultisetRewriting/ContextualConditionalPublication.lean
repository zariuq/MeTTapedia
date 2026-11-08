import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalRows
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublicationInventory

/-!
# Conditional answers become independently reusable stored rows

The actual returned value and its residual equations use the same private
names in the stored row. Opening a row can therefore neither forget a
condition nor constrain another use's private variables. Extending the
private bank retains all previous row matching, including latent equations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalPublication

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching ContextualConditionalRows

variable {S : Signature} {Local Added Shared Next Future : Type}
    (locals : Local → MetaArity S) (added : Added → MetaArity S) (captures : Shared → MetaArity S)
    {next : Next → MetaArity S} {future : Future → MetaArity S}

/-- Publication data fixed before execution. Roles rename active declarations
to private row names or captured declarations; they cannot replace the emitted
body with an unrelated term. Conditions remain local to the produced row. -/
structure Recipe where
  role : Shared → Local ⊕ Shared
  preserves : ∀ name, ContextualSelectionViews.source locals captures (role name) = captures name
  conditions : ContextualResidual.Problem captures
  isSchema : Bool := true

/-- A private declaration reindexing fixes every captured declaration. -/
def privateReindex (names : Local → Added) (preserves : ∀ name, added (names name) = locals name) :
    Assignment (ContextualSelectionViews.source locals captures)
      (ContextualSelectionViews.source added captures) :=
  reindex (Sum.map names id) (fun name => by cases name with
    | inl name => exact preserves name
    | inr _ => rfl)

/-- Private names move in the value and its conditions together. Live values
retain their captured references and their storage constructor. -/
def reindexPrivate (names : Local → Added) (preserves : ∀ name, added (names name) = locals name)
    {Γ : Ctx S} {sort : S.Srt} (row : Row locals captures Γ sort) : Row added captures Γ sort :=
  ⟨match row.value with
    | .schema body => .schema (instantiate (privateReindex locals added captures names preserves) body)
    | .shared value => .shared value,
    ContextualResidual.mapProblem (privateReindex locals added captures names preserves) row.obligations⟩

theorem privateReindex_captures (names : Local → Added)
    (preserves : ∀ name, added (names name) = locals name) :
    Assignment.compose (privateReindex locals added captures names preserves)
        (ContextualSelectionViews.capturedSource locals captures) =
      ContextualSelectionViews.capturedSource added captures := by
  funext name
  exact instantiate_generator _ _

theorem reindexed_template (names : Local → Added)
    (preserves : ∀ name, added (names name) = locals name)
    {Γ : Ctx S} {sort : S.Srt} (row : Row locals captures Γ sort) :
    ContextualStoredRows.asTemplate added captures (reindexPrivate locals added captures names preserves row).value =
      instantiate (privateReindex locals added captures names preserves)
        (ContextualStoredRows.asTemplate locals captures row.value) := by
  rcases row with ⟨value, obligations⟩
  cases value with
  | schema body => rfl
  | shared value =>
      change instantiate (ContextualSelectionViews.capturedSource added captures) value =
        instantiate (privateReindex locals added captures names preserves)
          (instantiate (ContextualSelectionViews.capturedSource locals captures) value)
      rw [← Assignment.instantiate_compose, privateReindex_captures]

theorem privateReindex_capture_square (names : Local → Added)
    (preserves : ∀ name, added (names name) = locals name) (change : Assignment captures next) :
    Assignment.compose (ContextualStoredRows.liftCaptures added change)
        (privateReindex locals added captures names preserves) =
      Assignment.compose (privateReindex locals added next names preserves)
        (ContextualStoredRows.liftCaptures locals change) := by
  funext name
  cases name with
  | inl name =>
      change instantiate (ContextualStoredRows.liftCaptures added change)
          (privateReindex locals added captures names preserves (.inl name)) =
        instantiate (privateReindex locals added next names preserves) (generator _ (.inl name))
      simp only [privateReindex, instantiate_reindex, instantiate_generator]
      rfl
  | inr name =>
      change instantiate (ContextualStoredRows.liftCaptures added change)
          (generator _ (.inr name)) =
        instantiate (privateReindex locals added next names preserves)
          (instantiate (ContextualSelectionViews.capturedSource locals next) (change name))
      rw [instantiate_generator, ← Assignment.instantiate_compose, privateReindex_captures]
      rfl

theorem reindexPrivate_map (names : Local → Added)
    (preserves : ∀ name, added (names name) = locals name) (change : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt} (row : Row locals captures Γ sort) :
    (reindexPrivate locals added captures names preserves row).map added captures change =
      reindexPrivate locals added next names preserves (row.map locals captures change) := by
  have square := privateReindex_capture_square locals added captures names preserves change
  cases row with
  | mk value obligations =>
      apply congrArg₂ Row.mk
      · cases value with
        | schema body =>
            dsimp only [reindexPrivate, Row.map, ContextualStoredRows.Row.map]
            rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose, square]
        | shared value => rfl
      · change ContextualResidual.mapProblem _ (ContextualResidual.mapProblem _ obligations) =
          ContextualResidual.mapProblem _ (ContextualResidual.mapProblem _ obligations)
        simp only [ContextualResidual.mapProblem, List.map_map]
        congr 1
        funext equation
        simp only [Function.comp_def, instantiateObservation_comp]
        exact congrArg (fun assignment =>
          (instantiateObservation assignment equation.1, instantiateObservation assignment equation.2)) square

theorem privateReindex_inverse (forward : Local → Added) (backward : Added → Local)
    (forwardPreserves : ∀ name, added (forward name) = locals name)
    (backwardPreserves : ∀ name, locals (backward name) = added name)
    (inverse : Function.LeftInverse backward forward) :
    Assignment.compose (privateReindex added locals captures backward backwardPreserves)
        (privateReindex locals added captures forward forwardPreserves) =
      generator (ContextualSelectionViews.source locals captures) := by
  apply reindex_left_inverse
  intro name
  cases name with
  | inl name => exact congrArg Sum.inl (inverse name)
  | inr _ => rfl

theorem reindexPrivate_inverse (forward : Local → Added) (backward : Added → Local)
    (forwardPreserves : ∀ name, added (forward name) = locals name)
    (backwardPreserves : ∀ name, locals (backward name) = added name)
    (inverse : Function.LeftInverse backward forward)
    {Γ : Ctx S} {sort : S.Srt} (row : Row locals captures Γ sort) :
    reindexPrivate added locals captures backward backwardPreserves
        (reindexPrivate locals added captures forward forwardPreserves row) = row := by
  have square := privateReindex_inverse locals added captures forward backward
    forwardPreserves backwardPreserves inverse
  rcases row with ⟨value, obligations⟩
  apply congrArg₂ Row.mk
  · cases value with
    | schema body =>
        change ContextualStoredRows.Row.schema (instantiate _ (instantiate _ body)) = .schema body
        rw [← Assignment.instantiate_compose, square, instantiate_identity]
    | shared value => rfl
  · change ContextualResidual.mapProblem _ (ContextualResidual.mapProblem _ obligations) = obligations
    simp only [ContextualResidual.mapProblem, List.map_map]
    have point (equation : Observation S (ContextualSelectionViews.source locals captures) ×
        Observation S (ContextualSelectionViews.source locals captures)) :
        (instantiateObservation (privateReindex added locals captures backward backwardPreserves)
            (instantiateObservation (privateReindex locals added captures forward forwardPreserves) equation.1),
          instantiateObservation (privateReindex added locals captures backward backwardPreserves)
            (instantiateObservation (privateReindex locals added captures forward forwardPreserves) equation.2)) = equation := by
      simp only [instantiateObservation_comp, square, instantiateObservation_identity]
    simp only [Function.comp_def, point]
    exact List.map_id _

theorem instance_privateReindex (names : Local → Added)
    (preserves : ∀ name, added (names name) = locals name)
    (images : Assignment added future) (embedding : Assignment next future)
    (candidate : Assignment captures next) :
    Assignment.compose (instanceAssignment added images embedding candidate)
        (privateReindex locals added captures names preserves) =
      instanceAssignment locals (Assignment.compose images (reindex names preserves)) embedding candidate := by
  funext name
  cases name with
  | inl name =>
      simp only [Assignment.compose, privateReindex, instantiate_reindex, instanceAssignment, Sum.map_inl]
      rfl
  | inr name => exact instantiate_generator _ _

/-- Reindexing cannot invent a row instance. Identifying distinct private
names may remove instances, so the converse requires an inverse. -/
theorem matches_of_reindexPrivate (names : Local → Added)
    (preserves : ∀ name, added (names name) = locals name) (candidate : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt} (row : Row locals captures Γ sort) (pattern : Term (signature S next) Γ sort)
    (matched : Matches added captures candidate pattern (reindexPrivate locals added captures names preserves row)) :
    Matches locals captures candidate pattern row := by
  obtain ⟨extension, images, obligations, same⟩ := matched
  refine ⟨extension, Assignment.compose images (reindex names preserves), ?_, ?_⟩
  · have original := (ContextualResidual.models_mapProblem _ _ _).mp obligations
    rw [instance_privateReindex] at original
    exact original
  · rw [reindexed_template, ← Assignment.instantiate_compose, instance_privateReindex] at same
    exact same

theorem reindexPrivate_matches_iff (forward : Local → Added) (backward : Added → Local)
    (forwardPreserves : ∀ name, added (forward name) = locals name)
    (backwardPreserves : ∀ name, locals (backward name) = added name)
    (inverse : Function.LeftInverse backward forward) (candidate : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt} (row : Row locals captures Γ sort) (pattern : Term (signature S next) Γ sort) :
    Matches added captures candidate pattern (reindexPrivate locals added captures forward forwardPreserves row) ↔
      Matches locals captures candidate pattern row := by
  constructor
  · exact matches_of_reindexPrivate locals added captures forward forwardPreserves candidate row pattern
  · intro matched
    have projected := matches_of_reindexPrivate added locals captures backward backwardPreserves candidate
      (reindexPrivate locals added captures forward forwardPreserves row) pattern
    rw [reindexPrivate_inverse locals added captures forward backward forwardPreserves backwardPreserves inverse] at projected
    exact projected matched

namespace Recipe

variable {locals captures}

def assignment (recipe : Recipe locals captures) :
    Assignment captures (ContextualSelectionViews.source locals captures) :=
  reindex recipe.role recipe.preserves

/-- Embed recipe-private names into the result's shared private bank.
Captured identities, conditions and the row constructor remain unchanged. -/
def reindexPrivate (recipe : Recipe locals captures) (names : Local → Added)
    (preserves : ∀ name, added (names name) = locals name) : Recipe added captures where
  role name := Sum.map names id (recipe.role name)
  preserves := by
    intro name
    have original := recipe.preserves name
    cases selected : recipe.role name with
    | inl localName =>
        change added (names localName) = captures name
        rw [selected] at original
        change locals localName = captures name at original
        exact (preserves localName).trans original
    | inr captured =>
        change captures captured = captures name
        rw [selected] at original
        exact original
  conditions := recipe.conditions
  isSchema := recipe.isSchema

/-- The value is the actual emitted expression. The recipe only assigns its
name roles and attaches the authored local conditions. -/
def row (recipe : Recipe locals captures) {Γ : Ctx S} {sort : S.Srt}
    (emitted : Term (signature S captures) Γ sort) : Row locals captures Γ sort :=
  ⟨if recipe.isSchema then .schema (instantiate recipe.assignment emitted) else .shared emitted,
    ContextualResidual.mapProblem recipe.assignment recipe.conditions⟩

/-- Publication transports captures through the execution's returned frame;
private names and row-local conditions are transported together. -/
def publish (recipe : Recipe locals captures) (returned : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt} (emitted : Term (signature S captures) Γ sort) :
    Row locals next Γ sort :=
  (recipe.row emitted).map locals captures returned

theorem reindexPrivate_assignment (recipe : Recipe locals captures) (names : Local → Added)
    (preserves : ∀ name, added (names name) = locals name) :
    (recipe.reindexPrivate added names preserves).assignment =
      Assignment.compose (privateReindex locals added captures names preserves) recipe.assignment := by
  rw [assignment, assignment, privateReindex, reindex_compose]
  rfl

theorem row_reindexPrivate (recipe : Recipe locals captures) (names : Local → Added)
    (preserves : ∀ name, added (names name) = locals name)
    {Γ : Ctx S} {sort : S.Srt} (emitted : Term (signature S captures) Γ sort) :
    (recipe.reindexPrivate added names preserves).row emitted =
      ContextualConditionalPublication.reindexPrivate locals added captures names preserves (recipe.row emitted) := by
  apply congrArg₂ Row.mk
  · cases choice : recipe.isSchema <;>
      simp only [row, reindexPrivate, choice, Bool.false_eq_true, ↓reduceIte]
    rw [← Assignment.instantiate_compose, ← reindexPrivate_assignment]
    rfl
  · change ContextualResidual.mapProblem _ recipe.conditions =
      ContextualResidual.mapProblem _ (ContextualResidual.mapProblem _ recipe.conditions)
    rw [reindexPrivate_assignment]
    simp only [ContextualResidual.mapProblem, List.map_map]
    congr 1
    funext equation
    simp only [Function.comp_def, instantiateObservation_comp]

/-- Rendering before or after a private-name reindexing gives exactly the
same conditional row, including constructor and pending equations. -/
theorem publish_reindexPrivate (recipe : Recipe locals captures) (names : Local → Added)
    (preserves : ∀ name, added (names name) = locals name) (returned : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt} (emitted : Term (signature S captures) Γ sort) :
    (recipe.reindexPrivate added names preserves).publish returned emitted =
      ContextualConditionalPublication.reindexPrivate locals added next names preserves
        (recipe.publish returned emitted) := by
  rw [publish, row_reindexPrivate, reindexPrivate_map]
  rfl

theorem publish_matches (recipe : Recipe locals captures) (returned : Assignment captures next)
    (candidate : Assignment next future) {Γ : Ctx S} {sort : S.Srt}
    (emitted : Term (signature S captures) Γ sort) (pattern : Term (signature S future) Γ sort) :
    Matches locals next candidate pattern (recipe.publish returned emitted) ↔
      Matches locals captures (Assignment.compose candidate returned) pattern (recipe.row emitted) :=
  matches_map_iff locals captures returned candidate pattern (recipe.row emitted)

end Recipe

theorem private_square (images : Assignment locals future) (embedding : Assignment next future)
    (candidate : Assignment captures next) :
    Assignment.compose (instanceAssignment locals images embedding candidate)
      (ContextualStoredRows.privateSource locals captures) = images := by
  funext name
  exact instantiate_generator _ _

def store {Γ : Ctx S} {sort : S.Srt} (answer : ContextualConditionalAnswers.Answer locals Γ sort) : Row locals captures Γ sort :=
  ⟨ContextualStoredRows.store locals captures answer.value,
    ContextualResidual.mapProblem (ContextualStoredRows.privateSource locals captures) answer.obligations⟩

theorem store_matches_iff (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (answer : ContextualConditionalAnswers.Answer locals Γ sort) (pattern : Term (signature S next) Γ sort) :
    Matches locals captures candidate pattern (store locals captures answer) ↔ answer.Instances next pattern := by
  constructor
  · rintro ⟨extension, images, obligations, same⟩
    refine ⟨extension, images, ?_, ?_⟩
    · have original := (ContextualResidual.models_mapProblem _ _ _).mp obligations
      rw [private_square locals captures images extension.assignment candidate] at original
      exact original
    · exact (ContextualPublication.instantiate_store locals images extension.assignment candidate answer.value).symm.trans same
  · rintro ⟨extension, images, obligations, same⟩
    refine ⟨extension, images, ?_, ?_⟩
    · apply (ContextualResidual.models_mapProblem _ _ _).mpr
      rw [private_square]
      exact obligations
    · exact (ContextualPublication.instantiate_store locals images extension.assignment candidate answer.value).trans same

def extendPrivate {Γ : Ctx S} {sort : S.Srt} (row : Row locals captures Γ sort) :
    Row (ContextualPublication.privateFamily locals added) captures Γ sort :=
  ⟨ContextualPublication.extendPrivate locals added row.value,
    ContextualResidual.mapProblem (ContextualPublication.includePrivate locals added) row.obligations⟩

theorem extended_template {Γ : Ctx S} {sort : S.Srt} (row : Row locals captures Γ sort) :
    ContextualStoredRows.asTemplate (ContextualPublication.privateFamily locals added) captures
      (extendPrivate locals added captures row).value =
    instantiate (ContextualPublication.includePrivate locals added)
      (ContextualStoredRows.asTemplate locals captures row.value) := by
  change ContextualStoredRows.asTemplate (ContextualPublication.privateFamily locals added) captures
      (ContextualPublication.extendPrivate locals added row.value) = _
  cases row.value with
  | schema body => rfl
  | shared value =>
      change instantiate (ContextualSelectionViews.capturedSource (ContextualPublication.privateFamily locals added) captures) value =
        instantiate (ContextualPublication.includePrivate locals added)
          (instantiate (ContextualSelectionViews.capturedSource locals captures) value)
      rw [← Assignment.instantiate_compose]
      apply congrArg (fun assignment => instantiate assignment value)
      funext name
      change generator (ContextualSelectionViews.source (ContextualPublication.privateFamily locals added) captures)
        (.inr name) = instantiate (ContextualPublication.includePrivate locals added)
          (generator (ContextualSelectionViews.source locals captures) (.inr name))
      exact (instantiate_generator (ContextualPublication.includePrivate locals added) (Sum.inr name)).symm

theorem extendPrivate_matches_iff (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (row : Row locals captures Γ sort) (pattern : Term (signature S next) Γ sort) :
    Matches (ContextualPublication.privateFamily locals added) captures candidate pattern
      (extendPrivate locals added captures row) ↔ Matches locals captures candidate pattern row := by
  constructor
  · rintro ⟨extension, images, obligations, same⟩
    refine ⟨extension, (fun name => images (.inl name)), ?_, ?_⟩
    · have original := (ContextualResidual.models_mapProblem _ _ _).mp obligations
      rw [ContextualPublication.instance_includePrivate] at original
      exact original
    · rw [extended_template] at same
      rw [← Assignment.instantiate_compose, ContextualPublication.instance_includePrivate] at same
      exact same
  · rintro ⟨extension, images, obligations, same⟩
    let extra := Extension.withLocals added extension.declarations
    let images' : Assignment (ContextualPublication.privateFamily locals added) extra.declarations
      | .inl name => instantiate extra.assignment (images name)
      | .inr name => generator extra.declarations (.inl name)
    have square : Assignment.compose extra.assignment (instanceAssignment locals images extension.assignment candidate) =
        instanceAssignment locals (fun name => images' (.inl name)) (extension.trans extra).assignment candidate := by
      erw [Extension.trans_assignment]
      funext name
      cases name with
      | inl name => rfl
      | inr name => exact instantiate_comp extension.assignment extra.assignment (candidate name)
    refine ⟨extension.trans extra, images', ?_, ?_⟩
    · apply (ContextualResidual.models_mapProblem _ _ _).mpr
      erw [ContextualPublication.instance_includePrivate, ← square]
      exact ContextualResidual.models_compose obligations extra.assignment
    · rw [extended_template, ← Assignment.instantiate_compose]
      erw [ContextualPublication.instance_includePrivate, ← square]
      erw [Extension.trans_assignment]
      exact (Assignment.instantiate_compose extra.assignment _ _).trans
        ((congrArg (instantiate extra.assignment) same).trans
          (Assignment.instantiate_compose extra.assignment extension.assignment pattern).symm)

def ordinary {Γ : Ctx S} {sort : S.Srt} (answer : ContextualConditionalAnswers.Answer added Γ sort) :
    Row (ContextualPublication.privateFamily locals added) captures Γ sort :=
  ⟨ContextualPublication.ordinary locals added answer.value,
    ContextualResidual.mapProblem
      (Assignment.compose (ContextualStoredRows.privateSource (ContextualPublication.privateFamily locals added) captures)
        (ContextualPublication.newPrivate locals added)) answer.obligations⟩

theorem ordinary_matches_iff (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (answer : ContextualConditionalAnswers.Answer added Γ sort) (pattern : Term (signature S next) Γ sort) :
    Matches (ContextualPublication.privateFamily locals added) captures candidate pattern
      (ordinary locals added captures answer) ↔ answer.Instances next pattern := by
  constructor
  · rintro ⟨extension, images, obligations, same⟩
    refine ⟨extension, (fun name => images (.inr name)), ?_, ?_⟩
    · have original := (ContextualResidual.models_mapProblem _ _ _).mp obligations
      have square : Assignment.compose
          (instanceAssignment (ContextualPublication.privateFamily locals added) images extension.assignment candidate)
          (Assignment.compose (ContextualStoredRows.privateSource (ContextualPublication.privateFamily locals added) captures)
            (ContextualPublication.newPrivate locals added)) = (fun name => images (.inr name)) := by
        rw [Assignment.compose_associative, private_square]
        funext name
        exact instantiate_generator images (.inr name)
      exact square ▸ original
    · change instantiate (instanceAssignment (ContextualPublication.privateFamily locals added) images extension.assignment candidate)
        (instantiate (ContextualStoredRows.privateSource (ContextualPublication.privateFamily locals added) captures)
          (instantiate (ContextualPublication.newPrivate locals added) answer.value)) = _ at same
      rw [ContextualPublication.instantiate_store, ContextualPublication.instantiate_newPrivate] at same
      exact same
  · rintro ⟨extension, images, obligations, same⟩
    let extra := Extension.withLocals locals extension.declarations
    let images' : Assignment (ContextualPublication.privateFamily locals added) extra.declarations
      | .inl name => generator extra.declarations (.inl name)
      | .inr name => instantiate extra.assignment (images name)
    have square : Assignment.compose
        (instanceAssignment (ContextualPublication.privateFamily locals added) images' (extension.trans extra).assignment candidate)
        (Assignment.compose (ContextualStoredRows.privateSource (ContextualPublication.privateFamily locals added) captures)
          (ContextualPublication.newPrivate locals added)) = Assignment.compose extra.assignment images := by
      erw [Assignment.compose_associative, private_square]
      funext name
      exact instantiate_generator images' (.inr name)
    refine ⟨extension.trans extra, images', ?_, ?_⟩
    · apply (ContextualResidual.models_mapProblem _ _ _).mpr
      erw [square]
      exact ContextualResidual.models_compose obligations extra.assignment
    · change instantiate (instanceAssignment (ContextualPublication.privateFamily locals added) images'
        (extension.trans extra).assignment candidate)
        (instantiate (ContextualStoredRows.privateSource (ContextualPublication.privateFamily locals added) captures)
          (instantiate (ContextualPublication.newPrivate locals added) answer.value)) = _
      erw [ContextualPublication.instantiate_store, ContextualPublication.instantiate_newPrivate, Extension.trans_assignment]
      exact (Assignment.instantiate_compose extra.assignment images answer.value).trans
        ((congrArg (instantiate extra.assignment) same).trans
          (Assignment.instantiate_compose extra.assignment extension.assignment pattern).symm)

theorem update_matches_source {V : Type} {source : V → MetaArity S} {problem : ContextualResidual.Problem source}
    (update : ContextualFrameUpdate.Update problem) (candidate : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt} (value : Term (signature S source) Γ sort) (pattern : Term (signature S next) Γ sort) :
    Matches (ContextualPublication.privateFamily locals update.declaration) captures candidate pattern
      (ordinary locals update.declaration captures (ContextualConditionalAnswers.ofUpdate update value)) ↔
    ContextualPublication.SourceInstances problem value next pattern :=
  (ordinary_matches_iff locals update.declaration captures candidate _ pattern).trans
    (ContextualConditionalAnswers.ofUpdate_exact update value next pattern)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalPublication
