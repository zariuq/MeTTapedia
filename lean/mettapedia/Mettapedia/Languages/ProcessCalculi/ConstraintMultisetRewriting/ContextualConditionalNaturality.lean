import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalGuards
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalPublication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUnusedMatching
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualEventViewRelocation

/-!
# Conditional rows and heterogeneous problems reflect fresh extensions

Unused declaration arities are supplied by fresh generators, rather than
by assuming inhabitants at every sort. Both value equalities and latent
equations travel through the same extension square. All-future guard asks
therefore reflect source-frame embeddings without dropping conditions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalNaturality

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching ContextualPrefixModels ContextualConditionalRows

variable {S : Signature} {V W X Local Extra Shared Next O : Type}
    {source : V → MetaArity S} {middle : W → MetaArity S} {target : X → MetaArity S}
    (locals : Local → MetaArity S) (unused : Extra → MetaArity S)
    {captures : Shared → MetaArity S} {next : Next → MetaArity S}

theorem map_problem_compose (first : Assignment source middle) (second : Assignment middle target)
    (problem : ContextualResidual.Problem source) :
    ContextualResidual.mapProblem second (ContextualResidual.mapProblem first problem) =
      ContextualResidual.mapProblem (Assignment.compose second first) problem := by
  simp only [ContextualResidual.mapProblem, List.map_map]
  congr 1
  funext equation
  simp only [Function.comp_def, instantiateObservation_comp]

/-- The row's value and conditions open at the same relocated use scope. -/
theorem obligations_relocated (permutation : Equiv.Perm Nat) (scope : Nat)
    {Γ : Ctx S} {sort : S.Srt} (row : Row locals captures Γ sort) :
    ContextualResidual.mapProblem (ContextualEventViewRelocation.assignment locals captures permutation)
        (row.obligationsAt locals captures scope) =
      row.obligationsAt locals captures (permutation scope) := by
  rw [Row.obligationsAt, map_problem_compose, ContextualEventViewRelocation.freshening_composes]
  rfl

theorem row_map_compose (first : Assignment captures middle) (second : Assignment middle target)
    {Γ : Ctx S} {sort : S.Srt} (row : Row locals captures Γ sort) :
    (row.map locals captures first).map locals middle second =
      row.map locals captures (Assignment.compose second first) := by
  cases row
  simp only [Row.map, ContextualStoredRows.Row.map_compose, map_problem_compose, ContextualStoredRows.liftCaptures_compose]

theorem row_map_identity {Γ : Ctx S} {sort : S.Srt} (row : Row locals captures Γ sort) :
    row.map locals captures (generator captures) = row := by
  cases row
  simp only [Row.map, ContextualStoredRows.Row.map_identity, ContextualStoredRows.liftCaptures_identity,
    ContextualResidual.mapProblem, instantiateObservation_identity, List.map_id']

/-- Reindexing the entire conditional ask retains its row-local equations,
including for absence and count checks at the original physical world. -/
theorem ask_reindex_iff (forward : V → W) (backward : W → V)
    (forwardPreserves : ∀ name, middle (forward name) = source name)
    (backwardPreserves : ∀ name, source (backward name) = middle name)
    (leftInverse : Function.LeftInverse backward forward)
    {Γ : Ctx S} {sort : S.Srt} (problem : ContextualResidual.Problem source)
    (rows : O → Row locals source Γ sort) (world : Finset O)
    (check : Check (Term (signature S source) Γ sort)) :
    ContextualConditionalGuards.Ask locals (ContextualResidual.mapProblem (reindex forward forwardPreserves) problem)
        (fun occurrence => (rows occurrence).map locals source (reindex forward forwardPreserves)) world
        (check.map (instantiate (reindex forward forwardPreserves))) ↔
      ContextualConditionalGuards.Ask locals problem rows world check := by
  have inverse := reindex_left_inverse forward backward forwardPreserves backwardPreserves leftInverse
  constructor
  · intro transported
    have restored := ContextualConditionalGuards.ask_transport locals (reindex backward backwardPreserves) transported
    have problemRestored : ContextualResidual.mapProblem (reindex backward backwardPreserves)
        (ContextualResidual.mapProblem (reindex forward forwardPreserves) problem) = problem := by
      rw [map_problem_compose, inverse]
      simp only [ContextualResidual.mapProblem, instantiateObservation_identity, List.map_id']
    have rowsRestored : (fun occurrence =>
        ((rows occurrence).map locals source (reindex forward forwardPreserves)).map locals middle
          (reindex backward backwardPreserves)) = rows := by
      funext occurrence
      rw [row_map_compose, inverse, row_map_identity]
    have checkRestored : (check.map (instantiate (reindex forward forwardPreserves))).map
        (instantiate (reindex backward backwardPreserves)) = check := by
      cases check <;> simp only [Check.map,
        instantiate_reindex_inverse forward backward forwardPreserves backwardPreserves leftInverse]
    rw [problemRestored, rowsRestored, checkRestored] at restored
    exact restored
  · exact ContextualConditionalGuards.ask_transport locals (reindex forward forwardPreserves)

/-- Reindexing a source value together with its problem preserves its
instances. This compares solutions, not the identities of solver helpers. -/
theorem sourceInstances_reindex_iff (forward : V → W) (backward : W → V)
    (forwardPreserves : ∀ name, middle (forward name) = source name)
    (backwardPreserves : ∀ name, source (backward name) = middle name)
    (leftInverse : Function.LeftInverse backward forward) (problem : ContextualResidual.Problem source)
    {Γ : Ctx S} {sort : S.Srt} (value : Term (signature S source) Γ sort)
    (next : Next → MetaArity S) (pattern : Term (signature S next) Γ sort) :
    ContextualPublication.SourceInstances (ContextualResidual.mapProblem (reindex forward forwardPreserves) problem)
        (instantiate (reindex forward forwardPreserves) value) next pattern ↔
      ContextualPublication.SourceInstances problem value next pattern := by
  have inverse := reindex_left_inverse forward backward forwardPreserves backwardPreserves leftInverse
  constructor
  · rintro ⟨extension, images, model, same⟩
    refine ⟨extension, Assignment.compose images (reindex forward forwardPreserves),
      (ContextualResidual.models_mapProblem _ _ _).mp model, ?_⟩
    exact (Assignment.instantiate_compose images _ value).trans same
  · rintro ⟨extension, images, model, same⟩
    refine ⟨extension, Assignment.compose images (reindex backward backwardPreserves), ?_, ?_⟩
    · apply (ContextualResidual.models_mapProblem _ _ _).mpr
      rw [← Assignment.compose_associative, inverse, Assignment.compose_identity_right]
      exact model
    · rw [← Assignment.instantiate_compose, ← Assignment.compose_associative,
        inverse, Assignment.compose_identity_right]
      exact same

theorem holds_extendPrivate (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (rows : O → Row locals captures Γ sort) (world : Finset O) (check : Check (Term (signature S captures) Γ sort)) :
    ContextualConditionalGuards.Holds (ContextualPublication.privateFamily locals unused) candidate
        (fun occurrence => ContextualConditionalPublication.extendPrivate locals unused captures (rows occurrence)) world check ↔
      ContextualConditionalGuards.Holds locals candidate rows world check := by
  cases check with
  | equal first second => rfl
  | absent pattern =>
      simp only [ContextualConditionalGuards.Holds, ContextualConditionalPublication.extendPrivate_matches_iff]
  | count pattern cardinality =>
      have regions : ContextualConditionalGuards.region (ContextualPublication.privateFamily locals unused) candidate
          (fun occurrence => ContextualConditionalPublication.extendPrivate locals unused captures (rows occurrence)) world pattern =
        ContextualConditionalGuards.region locals candidate rows world pattern := by
        classical
        ext occurrence
        simp only [ContextualConditionalGuards.mem_region, ContextualConditionalPublication.extendPrivate_matches_iff]
      change (ContextualConditionalGuards.region _ candidate _ world pattern).card = cardinality ↔
        (ContextualConditionalGuards.region locals candidate rows world pattern).card = cardinality
      rw [regions]

theorem ask_extendPrivate {Γ : Ctx S} {sort : S.Srt} (problem : ContextualResidual.Problem captures)
    (rows : O → Row locals captures Γ sort) (world : Finset O) (check : Check (Term (signature S captures) Γ sort)) :
    ContextualConditionalGuards.Ask (ContextualPublication.privateFamily locals unused) problem
        (fun occurrence => ContextualConditionalPublication.extendPrivate locals unused captures (rows occurrence)) world check ↔
      ContextualConditionalGuards.Ask locals problem rows world check := by
  constructor <;> intro asked Future future candidate model
  · exact (holds_extendPrivate locals unused candidate rows world check).mp (asked Future future candidate model)
  · exact (holds_extendPrivate locals unused candidate rows world check).mpr (asked Future future candidate model)

theorem observation_extension_injective (extension : Extension source) :
    Function.Injective (instantiateObservation extension.assignment) := by
  rintro ⟨leftContext, leftSort, left⟩ ⟨rightContext, rightSort, right⟩ same
  obtain ⟨sameContext, inner⟩ := Sigma.mk.inj_iff.mp same
  subst rightContext
  have sameInner := eq_of_heq inner
  obtain ⟨sameSort, bodies⟩ := Sigma.mk.inj_iff.mp sameInner
  subst rightSort
  have sameBodies := extension.instantiate_injective (eq_of_heq bodies)
  subst right
  rfl

theorem models_inclusion_iff (candidate : Assignment captures next) (problem : ContextualResidual.Problem captures) :
    ContextualResidual.Models (Assignment.compose (inclusion unused next) candidate) problem ↔
      ContextualResidual.Models candidate problem := by
  constructor
  · intro solved equation member
    apply observation_extension_injective (Extension.withLocals unused next)
    have sameAssignment : (Extension.withLocals unused next).assignment = inclusion unused next := by
      funext name
      rfl
    rw [sameAssignment]
    exact (instantiateObservation_comp candidate (inclusion unused next) equation.1).trans
      ((solved equation member).trans (instantiateObservation_comp candidate (inclusion unused next) equation.2).symm)
  · intro solved
    exact ContextualResidual.models_compose solved (inclusion unused next)

theorem models_liftModel_iff (extension : Extension source) (candidate : Assignment source next)
    (problem : ContextualResidual.Problem source) :
    ContextualResidual.Models (extension.liftModel candidate) (ContextualResidual.mapProblem extension.assignment problem) ↔
      ContextualResidual.Models candidate problem := by
  rw [ContextualResidual.models_mapProblem, extension.liftModel_square]
  exact models_inclusion_iff extension.complementDeclarations candidate problem

theorem solvable_extension_iff (extension : Extension source) (problem : ContextualResidual.Problem source) :
    (∃ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment extension.declarations future),
      ContextualResidual.Models candidate (ContextualResidual.mapProblem extension.assignment problem)) ↔
    ∃ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment source future),
      ContextualResidual.Models candidate problem := by
  constructor
  · rintro ⟨Future, future, candidate, model⟩
    exact ⟨Future, future, Assignment.compose candidate extension.assignment,
      (ContextualResidual.models_mapProblem _ _ _).mp model⟩
  · rintro ⟨Future, future, candidate, model⟩
    exact ⟨Extension.Complement extension ⊕ Future, extended extension.complementDeclarations future,
      extension.liftModel candidate, (models_liftModel_iff extension candidate problem).mpr model⟩

theorem matches_inclusion_iff (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (pattern : Term (signature S next) Γ sort) (row : Row locals captures Γ sort) :
    Matches locals captures (Assignment.compose (inclusion unused next) candidate)
        (instantiate (inclusion unused next) pattern) row ↔ Matches locals captures candidate pattern row := by
  constructor
  · rintro ⟨extension, images, conditions, same⟩
    refine ⟨extension.restrictUnused unused, images, ?_, ?_⟩
    · rw [instance_restrict_unused] at conditions
      exact conditions
    · rw [instance_restrict_unused] at same
      exact same.trans (by rw [← Assignment.instantiate_compose, ← Extension.restrictUnused_assignment]; rfl)
  · rintro ⟨extension, images, conditions, same⟩
    refine ⟨extension.addUnused unused, Assignment.compose (inclusion unused extension.declarations) images, ?_, ?_⟩
    · have mapped := ContextualResidual.models_compose conditions (inclusion unused extension.declarations)
      rw [instance_add_unused] at mapped
      exact mapped
    · have left := congrArg
        (fun assignment : Assignment (ContextualSelectionViews.source locals captures)
          (extended unused extension.declarations) => instantiate assignment (ContextualStoredRows.asTemplate locals captures row.value))
        (instance_add_unused locals unused extension images candidate)
      simp only [Assignment.instantiate_compose] at left
      have mapped := congrArg (instantiate (inclusion unused extension.declarations)) same
      have right : instantiate (inclusion unused extension.declarations) (instantiate extension.assignment pattern) =
          instantiate (extension.addUnused unused).assignment (instantiate (inclusion unused next) pattern) := by
        rw [Extension.addUnused_assignment]
        exact (ContextualStoredRows.liftCaptures_on_shared_value unused extension.assignment pattern).symm
      exact left.symm.trans (mapped.trans right)

theorem region_inclusion (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (rows : O → Row locals captures Γ sort) (world : Finset O) (pattern : Term (signature S captures) Γ sort) :
    ContextualConditionalGuards.region locals (Assignment.compose (inclusion unused next) candidate) rows world pattern =
      ContextualConditionalGuards.region locals candidate rows world pattern := by
  classical
  ext occurrence
  rw [ContextualConditionalGuards.mem_region, ContextualConditionalGuards.mem_region, Assignment.instantiate_compose]
  exact and_congr_right fun _ => matches_inclusion_iff locals unused candidate (instantiate candidate pattern) (rows occurrence)

theorem holds_inclusion_iff (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (rows : O → Row locals captures Γ sort) (world : Finset O) (check : Check (Term (signature S captures) Γ sort)) :
    ContextualConditionalGuards.Holds locals (Assignment.compose (inclusion unused next) candidate) rows world check ↔
      ContextualConditionalGuards.Holds locals candidate rows world check := by
  cases check with
  | equal first second =>
      change instantiate (Assignment.compose (inclusion unused next) candidate) first =
        instantiate (Assignment.compose (inclusion unused next) candidate) second ↔ _
      rw [Assignment.instantiate_compose, Assignment.instantiate_compose]
      exact ⟨fun same => inclusion_injective unused next _ _ same, congrArg (instantiate (inclusion unused next))⟩
  | absent pattern =>
      simp only [ContextualConditionalGuards.Holds, Assignment.instantiate_compose, matches_inclusion_iff]
  | count pattern number =>
      change (ContextualConditionalGuards.region locals _ rows world pattern).card = number ↔
        (ContextualConditionalGuards.region locals candidate rows world pattern).card = number
      rw [region_inclusion]

theorem ask_extension_iff (extension : Extension source) {Γ : Ctx S} {sort : S.Srt}
    (problem : ContextualResidual.Problem source) (rows : O → Row locals source Γ sort) (world : Finset O)
    (check : Check (Term (signature S source) Γ sort)) :
    ContextualConditionalGuards.Ask locals (ContextualResidual.mapProblem extension.assignment problem)
        (fun occurrence => (rows occurrence).map locals source extension.assignment) world
        (check.map (instantiate extension.assignment)) ↔ ContextualConditionalGuards.Ask locals problem rows world check := by
  constructor
  · intro asked Future future candidate model
    have lifted := (models_liftModel_iff extension candidate problem).mpr model
    have held := asked (Extension.Complement extension ⊕ Future) (extended extension.complementDeclarations future)
      (extension.liftModel candidate) lifted
    have original := (ContextualConditionalGuards.holds_transport locals extension.assignment
      (extension.liftModel candidate) rows world check).mp held
    rw [extension.liftModel_square] at original
    exact (holds_inclusion_iff locals extension.complementDeclarations candidate rows world check).mp original
  · intro asked
    exact ContextualConditionalGuards.ask_transport locals extension.assignment asked

theorem source_instances_extension (extension : Extension source) {Γ : Ctx S} {sort : S.Srt}
    (problem : ContextualResidual.Problem source) (value : Term (signature S source) Γ sort)
    (next : Next → MetaArity S) (pattern : Term (signature S next) Γ sort) :
    ContextualPublication.SourceInstances (ContextualResidual.mapProblem extension.assignment problem)
        (instantiate extension.assignment value) next pattern ↔ ContextualPublication.SourceInstances problem value next pattern := by
  constructor
  · rintro ⟨later, candidate, model, same⟩
    exact ⟨later, Assignment.compose candidate extension.assignment,
      (ContextualResidual.models_mapProblem _ _ _).mp model,
      (Assignment.instantiate_compose candidate extension.assignment value).trans same⟩
  · rintro ⟨later, candidate, model, same⟩
    let added := Extension.withLocals extension.complementDeclarations later.declarations
    refine ⟨later.trans added, extension.liftModel candidate,
      (models_liftModel_iff extension candidate problem).mpr model, ?_⟩
    erw [Extension.trans_assignment, ← Assignment.instantiate_compose, extension.liftModel_square,
      Assignment.instantiate_compose]
    exact (congrArg (instantiate added.assignment) same).trans
      (Assignment.instantiate_compose added.assignment later.assignment pattern).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalNaturality
