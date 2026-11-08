import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReachTemplatePublication

/-!
# One publication of independently reusable schema values

The list supplies values, including any location constructors. Distinct
physical output identities retain equal values as distinct occurrences.
All private names in a value remain private to its later uses. This is
the publication stage; a caller collecting answers must retain its complete
query certificate at the same admission cut.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchemaBatch

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualTemplateSource ContextualScopeSupport ContextualWorldScopeLedger

variable {S : Signature} {Local Inner O : Type}
    (locals : Local → MetaArity S) (inners : Inner → MetaArity S)
    {Γ : Ctx S} {sort : S.Srt}

def blueprint {Shared : Type} (captures : Shared → MetaArity S)
    (value : Term (signature S inners) Γ sort) :
    Term (signature S (Blueprint locals inners captures)) Γ sort :=
  instantiate (ContextualStoredRows.privateSource inners (Actor locals captures)) value

def rule {Shared : Type} (captures : Shared → MetaArity S)
    (values : List (Term (signature S inners) Γ sort)) : Rule locals inners captures Γ sort :=
  ⟨[], [], [], [], values.map fun value => .schema (blueprint locals inners captures value)⟩

def selection (made : List O) : Selection O := ⟨[], [], made⟩

abbrev prepared (before : ContextualExecution.Endpoint locals O Γ sort) :=
  ContextualTemplatePublication.prepareEndpoint locals inners before

theorem rule_at_port {Shared : Type} (captures : Shared → MetaArity S)
    (values : List (Term (signature S inners) Γ sort)) (position : Fin values.length) :
    (rule locals inners captures values).produce.get
      ⟨position.val, by simpa only [rule, List.length_map] using position.isLt⟩ =
      .schema (blueprint locals inners captures (values.get position)) := by
  change (values.map (fun value => Production.schema (blueprint locals inners captures value)))[position.val] = _
  exact List.getElem_map ..

def outputs [DecidableEq O] (before : ContextualExecution.Endpoint locals O Γ sort)
    (values : List (Term (signature S inners) Γ sort)) (made : List O) :
    O → Term (signature S (Active locals inners before.declarations)) Γ sort :=
  let point := ContextualActivationScopes.scopeAt before.occupied
    (ContextualActivationScopes.rulePort (selection made))
  let terms := (ContextualActivatedStep.prepared (Expanded locals inners) before.declarations
    before.occupied (selection made) ((rule locals inners before.declarations values).lower locals inners before.declarations)
    (prepared locals inners before).inventory.rows).rule.produce
  fun occurrence => (assign made terms occurrence).getD
    (ContextualStoredRows.viewAt (Expanded locals inners) before.declarations point
      ((prepared locals inners before).inventory.rows occurrence))

theorem outputs_exact [DecidableEq O] (before : ContextualExecution.Endpoint locals O Γ sort)
    (values : List (Term (signature S inners) Γ sort)) (made : List O)
    (distinct : made.Nodup) (lengths : made.length = values.length) :
    made.map (outputs locals inners before values made) =
      (ContextualActivatedStep.prepared (Expanded locals inners) before.declarations before.occupied (selection made)
        ((rule locals inners before.declarations values).lower locals inners before.declarations)
        (prepared locals inners before).inventory.rows).rule.produce := by
  apply assign_map made _ _ distinct
  simpa only [ContextualActivatedStep.prepared, ContextualSelectionViews.prepare,
    ContextualFreshening.ruleAt, RuleInstance.map, Rule.lower, rule,
    List.length_map, List.length_mapIdx] using lengths

theorem rule_covered (before : ContextualExecution.Endpoint locals O Γ sort)
    (values : List (Term (signature S inners) Γ sort)) :
    RuleCovered (privateScopes before.scopes) before.occupied
      ((rule locals inners before.declarations values).lower locals inners before.declarations) := by
  intro value member
  change value ∈ ((rule locals inners before.declarations values).lower locals inners before.declarations).produce at member
  obtain ⟨position, same⟩ := List.mem_iff_get.mp member
  let position' : Fin (rule locals inners before.declarations values).produce.length :=
    ⟨position.val, by simpa only [Rule.lower, List.length_mapIdx] using position.isLt⟩
  have original := (rule locals inners before.declarations values).lower_at_port locals inners before.declarations position'
  change ((rule locals inners before.declarations values).lower locals inners before.declarations).produce.get position = _ at original
  rw [same] at original
  rw [original]
  have bound : position'.val < values.length := by simpa only [rule, List.length_map] using position'.isLt
  rw [rule_at_port locals inners before.declarations values ⟨position'.val, bound⟩]
  change Covered (privateScopes before.scopes) before.occupied
    (instantiate (templateInclusion locals inners before.declarations position'.val)
      (blueprint locals inners before.declarations (values.get ⟨position'.val, bound⟩)))
  unfold blueprint
  rw [← Assignment.instantiate_compose]
  apply covered_instantiate _ _ _ _
  intro identity _
  change term (privateScopes before.scopes)
    (instantiate (templateInclusion locals inners before.declarations position.val)
      (generator (Blueprint locals inners before.declarations) (.inl identity))) ⊆ before.occupied
  rw [instantiate_generator, templateInclusion]
  erw [term_generator (S := S)]
  exact Finset.empty_subset _

theorem problem_eq (before : ContextualExecution.Endpoint locals O Γ sort)
    (values : List (Term (signature S inners) Γ sort)) (made : List O) :
    ContextualActivatedStep.problem (Expanded locals inners) before.declarations before.occupied (selection made)
      ((rule locals inners before.declarations values).lower locals inners before.declarations)
      (prepared locals inners before).inventory.rows before.inventory.configuration =
    ContextualFrameUnifier.mapProblem (ContextualSelectionViews.capturedTarget (Expanded locals inners) before.declarations)
      before.inventory.configuration.equations := by
  simp [ContextualActivatedStep.problem, ContextualActivatedStep.frame,
    ContextualActivatedStep.prepared, ContextualSelectionViews.prepare, ContextualFreshening.ruleAt,
    RuleInstance.map, Rule.lower, rule, ContextualActivatedStep.useEquations, Selection.equations]

theorem solvable (before : ContextualExecution.Endpoint locals O Γ sort)
    (values : List (Term (signature S inners) Γ sort)) (made : List O)
    (consistent : ContextualFrameUnifier.Solvable before.inventory.configuration.equations) :
    ContextualFrameUnifier.Solvable (ContextualActivatedStep.problem (Expanded locals inners) before.declarations
      before.occupied (selection made) ((rule locals inners before.declarations values).lower locals inners before.declarations)
      (prepared locals inners before).inventory.rows before.inventory.configuration) := by
  rw [problem_eq]
  obtain ⟨Next, next, candidate, model⟩ := consistent
  let added := ContextualGuardMatching.Extension.withLocals
    (fun name : Mettapedia.Logic.LP.ScopedVar (Local ⊕ (Nat × Inner)) => (Expanded locals inners) name.name) next
  let images : Assignment (Active locals inners before.declarations) added.declarations
    | .inl name => generator added.declarations (.inl name)
    | .inr name => instantiate added.assignment (candidate name)
  refine ⟨_, added.declarations, images, ?_⟩
  apply (ContextualFrameUnifier.models_mapProblem _ _ _).mpr
  have same : Assignment.compose images
      (ContextualSelectionViews.capturedTarget (Expanded locals inners) before.declarations) =
      Assignment.compose added.assignment candidate := by
    funext name
    exact instantiate_generator images (.inr name)
  rw [same]
  exact ContextualFrameUnifier.models_compose model added.assignment

theorem admitted [DecidableEq O] (before : ContextualExecution.Endpoint locals O Γ sort)
    (values : List (Term (signature S inners) Γ sort)) (made : List O)
    (distinct : made.Nodup) (fresh : Disjoint made.toFinset before.inventory.configuration.present)
    (lengths : made.length = values.length)
    (consistent : ContextualFrameUnifier.Solvable before.inventory.configuration.equations) :
    ContextualGuardedStep.Valid (Expanded locals inners) before.declarations before.occupied
      (selection made) ((rule locals inners before.declarations values).lower locals inners before.declarations)
      (prepared locals inners before).inventory.rows before.inventory.configuration
      (outputs locals inners before values made) := by
  refine ⟨⟨by simp [selection], distinct, rfl, rfl, outputs_exact locals inners before values made distinct lengths,
    ?_, ?_⟩, solvable locals inners before values made consistent⟩
  · refine ⟨by simp [selection, Selection.commit], by simp [selection, Selection.commit],
      by simp [selection, Selection.commit], ?_, ?_⟩
    · exact fresh
    · intro query member
      cases member
  · intro check member
    cases member

theorem blueprint_instances_iff {Shared Next : Type}
    (captures : Shared → MetaArity S) (next : Next → MetaArity S)
    (candidate : Assignment (Actor locals captures) next)
    (value : Term (signature S inners) Γ sort) (pattern : Term (signature S next) Γ sort) :
    ContextualGuardMatching.Matches inners candidate pattern
      (.schema (blueprint locals inners captures value)) ↔
    ContextualPublication.Instances inners value next pattern := by
  constructor
  · rintro ⟨extension, images, same⟩
    refine ⟨extension, images, ?_⟩
    exact (ContextualPublication.instantiate_store inners images extension.assignment candidate value).symm.trans same
  · rintro ⟨extension, images, same⟩
    exact ⟨extension, images,
      (ContextualPublication.instantiate_store inners images extension.assignment candidate value).trans same⟩

/-- A consistent structural-pattern source world constructs a real completed
publication. No solver answer or run is supplied by the caller. -/
theorem realize [DecidableEq Local] [DecidableEq Inner] [DecidableEq O]
    [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]
    (before : ContextualExecution.Endpoint locals O Γ sort)
    (values : List (Term (signature S inners) Γ sort)) (made : List O)
    (distinct : made.Nodup) (fresh : Disjoint made.toFinset before.inventory.configuration.present)
    (lengths : made.length = values.length)
    (consistent : ContextualFrameUnifier.Solvable before.inventory.configuration.equations)
    (patterned : ContextualPatternFragment.ProblemPattern
      (ContextualResidual.observeProblem before.inventory.configuration.equations)) :
    ∃ firing : ContextualTemplatePublication.Firing locals inners (prepared locals inners before),
      firing.sourceRule = rule locals inners before.declarations values ∧
      firing.selection = selection made ∧ firing.execution.outputs = outputs locals inners before values made := by
  let _ := before.equality
  apply ContextualTemplatePublication.realize_source_publication locals inners (prepared locals inners before)
    (rule locals inners before.declarations values) (selection made) (outputs locals inners before values made)
    (rule_covered locals inners before values) (admitted locals inners before values made distinct fresh lengths consistent)
  change ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
    (ContextualActivatedStep.problem (Expanded locals inners) before.declarations before.occupied (selection made)
      ((rule locals inners before.declarations values).lower locals inners before.declarations)
      (prepared locals inners before).inventory.rows before.inventory.configuration))
  rw [problem_eq, ContextualResidual.observeProblem_mapProblem]
  apply ContextualPatternFragment.map_patterns _ _ _ patterned
  intro identity
  exact ContextualPatternFragment.generator_pattern (S := S)
    (declaration := Active locals inners before.declarations) (Sum.inr identity)

section Publication

variable [DecidableEq Local] [DecidableEq Inner] [DecidableEq O]
    [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]
    {before : ContextualExecution.Endpoint locals O Γ sort}
    (values : List (Term (signature S inners) Γ sort))
    (firing : ContextualTemplatePublication.Firing locals inners (prepared locals inners before))

theorem value_bound (authored : firing.sourceRule = rule locals inners before.declarations values)
    (position : Fin firing.selection.made.length) : position.val < values.length := by
  have lengths := firing.output_length
  rw [authored] at lengths
  change firing.selection.made.length =
    (values.map fun value => Production.schema (blueprint locals inners before.declarations value)).length at lengths
  rw [List.length_map] at lengths
  omega

theorem descriptor_at (authored : firing.sourceRule = rule locals inners before.declarations values)
    (position : Fin firing.selection.made.length) :
    firing.descriptor (firing.selection.made.get position) =
      some (position.val, Production.schema
        (blueprint locals inners before.declarations (values.get
          ⟨position.val, value_bound locals inners values firing authored position⟩))) := by
  have atPort := firing.sourceRule.output_at_port locals inners before.declarations
    firing.selection.made firing.execution.admitted.output_distinct firing.output_length position
  change firing.descriptor (firing.selection.made.get position) = _ at atPort
  have lengths := firing.output_length
  have production : firing.sourceRule.produce.get
      ⟨position.val, by omega⟩ =
      Production.schema (blueprint locals inners before.declarations
        (values.get ⟨position.val, value_bound locals inners values firing authored position⟩)) := by
    exact (List.getElem_of_eq (congrArg (fun source => source.produce) authored)
      (i := position.val) (lengths ▸ position.isLt)).trans (rule_at_port locals inners before.declarations values
        ⟨position.val, value_bound locals inners values firing authored position⟩)
  exact atPort.trans (congrArg (fun output => some (position.val, output)) production)

/-- A later reader sees exactly an instance of the selected original value.
The firing's helper choice and the later reader's caller do not change it. -/
theorem published_instances (authored : firing.sourceRule = rule locals inners before.declarations values)
    (position : Fin firing.selection.made.length)
    {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    ContextualGuardMatching.Matches
      (ContextualPublication.privateFamily (Expanded locals inners) firing.update.declaration)
      candidate pattern (firing.target.inventory.rows (firing.selection.made.get position)) ↔
    ContextualPublication.Instances inners
      (values.get ⟨position.val, value_bound locals inners values firing authored position⟩) next pattern := by
  exact (firing.schema_matches_source _ _ _ (descriptor_at locals inners values firing authored position)
    next candidate pattern).trans (blueprint_instances_iff locals inners before.declarations next _ _ pattern)

end Publication

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchemaBatch
