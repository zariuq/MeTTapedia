import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedRenaming

/-!
# Actual selected reads and takes commute under exact resource independence

The two source paths are built from their shared-input evidence and the actual
one-fuel solver returns. Different port counts use different scope maps.
The endpoint relation keeps all rows and roots, and the full joint equation
list up to permutation, including every duplicate equation from aliased reads.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedExecution

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualScopeSupport ContextualWorldScopeLedger
open ContextualSelectedNormalization ContextualExecutionCommutationNames
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {Local O : Type} {locals : Local → MetaArity S}
  [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  {Γ : Ctx S} {sort : S.Srt}

structure EndpointPermutation (first second : Endpoint locals O Γ sort) : Type 1 where
  names : first.Names ≃ second.Names
  declarations : ∀ name, second.declarations (names name) = first.declarations name
  scope_coverage : ∀ name, second.scopes (names name) ⊆ second.occupied ↔ first.scopes name ⊆ first.occupied
  occupied : first.occupied = second.occupied
  world : first.inventory.configuration.present = second.inventory.configuration.present
  equations : (ContextualFrameUnifier.mapProblem (reindex names declarations)
    first.inventory.configuration.equations).Perm second.inventory.configuration.equations
  rows : ∀ occurrence, (first.inventory.rows occurrence).map locals (reindex names declarations) =
    second.inventory.rows occurrence
  retained : (first.inventory.retained.map (instantiateObservation (reindex names declarations))).Perm
    second.inventory.retained
  templates : first.inventory.templates.map
    (instantiateObservation (ContextualStoredRows.liftCaptures locals (reindex names declarations))) = second.inventory.templates

omit [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem EndpointPermutation.joint_models_iff {first second : Endpoint locals O Γ sort}
    (equivalence : EndpointPermutation first second) {Future : Type} (future : Future → MetaArity S)
    (candidate : Assignment second.declarations future) :
    ContextualFrameUnifier.Models candidate second.inventory.configuration.equations ↔
      ContextualFrameUnifier.Models (Assignment.compose candidate (reindex equivalence.names equivalence.declarations))
        first.inventory.configuration.equations := by
  have permuted : ContextualFrameUnifier.Models candidate
      (ContextualFrameUnifier.mapProblem (reindex equivalence.names equivalence.declarations) first.inventory.configuration.equations) ↔
        ContextualFrameUnifier.Models candidate second.inventory.configuration.equations := by
    constructor
    · intro solved equation member
      exact solved equation (equivalence.equations.symm.subset member)
    · intro solved equation member
      exact solved equation (equivalence.equations.subset member)
  exact permuted.symm.trans (ContextualFrameUnifier.models_mapProblem _ _ _)

variable {before : Endpoint locals O Γ sort}

def swapAssignment (first second : Interaction before) : Assignment (twiceDeclarations locals before.declarations)
    (twiceDeclarations locals before.declarations) :=
  ContextualSelectedNames.assignment locals before.declarations
    (ContextualSelectedRenaming.earlierScopes before.occupied first.count second.count)
    (ContextualSelectedRenaming.laterScopes before.occupied first.count second.count)

omit [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem earlier_becomes_later (first second : Interaction before) (occurrence : O) :
    instantiate (swapAssignment first second) (first.earlierValue occurrence) = second.laterValue first occurrence := by
  rw [Interaction.earlierValue, ← Assignment.instantiate_compose]
  change instantiate (Assignment.compose (ContextualSelectedNames.assignment locals before.declarations _ _)
    (intoEarlier locals before.declarations _)) _ = _
  rw [ContextualSelectedNames.earlier_into_later]
  simp only [ContextualSelectedRenaming.earlierScopes, Equiv.swap_apply_left]
  rfl

omit [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem later_becomes_earlier (first second : Interaction before) (occurrence : O) :
    instantiate (swapAssignment first second) (first.laterValue second occurrence) = second.earlierValue occurrence := by
  rw [Interaction.laterValue, ← Assignment.instantiate_compose]
  change instantiate (Assignment.compose (ContextualSelectedNames.assignment locals before.declarations _ _)
    (intoLater locals before.declarations _)) _ = _
  rw [ContextualSelectedNames.later_into_earlier]
  simp only [ContextualSelectedRenaming.laterScopes, Equiv.swap_apply_left]
  rfl

theorem swapped_rows (first second : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior)
    (apart : first.Independent second) (occurrence : O) :
    ((first.twoTarget second prior incoming apart.orders.1).inventory.rows occurrence).map locals (swapAssignment first second) =
      (second.twoTarget first prior incoming apart.orders.2).inventory.rows occurrence := by
  rw [Interaction.two_target_rows, Interaction.two_target_rows]
  have madeApart := ((Interaction.independent_iff_disjoint first second).mp apart).2.1
  by_cases inFirst : occurrence ∈ first.made
  · have notSecond : occurrence ∉ second.made := by
      intro member
      exact Finset.disjoint_left.mp madeApart (by simpa using inFirst) (by simpa using member)
    simp only [if_pos inFirst, if_neg notSecond, ContextualStoredRows.Row.map, earlier_becomes_later]
  · by_cases inSecond : occurrence ∈ second.made
    · simp only [if_neg inFirst, if_pos inSecond, ContextualStoredRows.Row.map, later_becomes_earlier]
    · simp only [if_neg inFirst, if_neg inSecond]
      rw [ContextualStoredRows.Row.map_compose]
      exact congrArg (fun change => (before.inventory.rows occurrence).map locals change)
        (ContextualSelectedNames.captures_fixed locals before.declarations _ _)

theorem swapped_equations (first second : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior)
    (apart : first.Independent second) :
    (ContextualFrameUnifier.mapProblem (swapAssignment first second)
      (first.twoTarget second prior incoming apart.orders.1).inventory.configuration.equations).Perm
        (second.twoTarget first prior incoming apart.orders.2).inventory.configuration.equations := by
  rw [Interaction.two_target_equations, Interaction.two_target_equations, map_diagonals]
  apply List.Perm.map
  have permuted : (prior ++ first.inputTerms ++ second.inputTerms).Perm (prior ++ second.inputTerms ++ first.inputTerms) := by
    simpa only [List.append_assoc] using (List.perm_append_comm (l₁ := first.inputTerms) (l₂ := second.inputTerms)).append_left prior
  simpa only [Interaction.terms, Interaction.inputTerms, List.append_assoc] using permuted

theorem swapped_roots (first second : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior)
    (apart : first.Independent second) :
    ((first.twoTarget second prior incoming apart.orders.1).inventory.retained.map
      (instantiateObservation (swapAssignment first second))).Perm
        (second.twoTarget first prior incoming apart.orders.2).inventory.retained := by
  rw [Interaction.two_target_retained, Interaction.two_target_retained, List.map_append, List.map_append]
  have initial : (before.inventory.retained.map (instantiateObservation (intoOldCaptures locals before.declarations))).map
      (instantiateObservation (swapAssignment first second)) =
        before.inventory.retained.map (instantiateObservation (intoOldCaptures locals before.declarations)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro value _member
    rw [Function.comp_apply, instantiateObservation_comp]
    exact congrArg (fun change => instantiateObservation change value)
      (ContextualSelectedNames.captures_fixed locals before.declarations _ _)
  rw [initial]
  have earlier := Interaction.rootValues_map _ _ (swapAssignment first second)
    (intoEarlier locals before.declarations (ContextualActivationScopes.start before.occupied)) first
  have later := Interaction.rootValues_map _ _ (swapAssignment first second)
    (intoLater locals before.declarations
      (ContextualActivationScopes.start (ContextualSelectedScopes.advance before.occupied first.count))) second
  rw [show Assignment.compose (swapAssignment first second) (intoEarlier locals before.declarations
      (ContextualActivationScopes.start before.occupied)) =
        intoLater locals before.declarations (ContextualActivationScopes.start (ContextualSelectedScopes.advance before.occupied second.count))
      from by simpa [swapAssignment, ContextualSelectedRenaming.earlierScopes] using
        (ContextualSelectedNames.earlier_into_later locals before.declarations
          (ContextualSelectedRenaming.earlierScopes before.occupied first.count second.count)
          (ContextualSelectedRenaming.laterScopes before.occupied first.count second.count)
          (ContextualActivationScopes.start before.occupied))] at earlier
  rw [show Assignment.compose (swapAssignment first second) (intoLater locals before.declarations
      (ContextualActivationScopes.start (ContextualSelectedScopes.advance before.occupied first.count))) =
        intoEarlier locals before.declarations (ContextualActivationScopes.start before.occupied)
      from by simpa [swapAssignment, ContextualSelectedRenaming.laterScopes] using
        (ContextualSelectedNames.later_into_earlier locals before.declarations
          (ContextualSelectedRenaming.earlierScopes before.occupied first.count second.count)
          (ContextualSelectedRenaming.laterScopes before.occupied first.count second.count)
          (ContextualActivationScopes.start (ContextualSelectedScopes.advance before.occupied first.count)))] at later
  rw [earlier, later]
  simpa only [List.append_assoc] using List.perm_append_comm.append_left
    (before.inventory.retained.map (instantiateObservation (intoOldCaptures locals before.declarations)))

theorem swapped_templates (first second : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior)
    (apart : first.Independent second) :
    (first.twoTarget second prior incoming apart.orders.1).inventory.templates.map
      (instantiateObservation (ContextualStoredRows.liftCaptures locals (swapAssignment first second))) =
        (second.twoTarget first prior incoming apart.orders.2).inventory.templates := by
  rw [Interaction.two_target_templates, Interaction.two_target_templates, List.map_map]
  apply List.map_congr_left
  intro value _member
  rw [Function.comp_apply, instantiateObservation_comp, ContextualStoredRows.liftCaptures_compose]
  exact congrArg (fun change => instantiateObservation (ContextualStoredRows.liftCaptures locals change) value)
    (ContextualSelectedNames.captures_fixed locals before.declarations _ _)

def endpointPermutation (first second : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior)
    (apart : first.Independent second) :
    EndpointPermutation (first.twoTarget second prior incoming apart.orders.1)
      (second.twoTarget first prior incoming apart.orders.2) where
  names := ContextualSelectedNames.namesEquiv
    (ContextualSelectedRenaming.earlierScopes before.occupied first.count second.count)
    (ContextualSelectedRenaming.laterScopes before.occupied first.count second.count)
  declarations := ContextualSelectedNames.preserves locals before.declarations _ _
  scope_coverage := ContextualSelectedRenaming.scope_coverage before.scopes before.occupied
    first.count second.count first.count_positive second.count_positive
  occupied := ContextualSelectedScopes.advance_comm before.occupied first.count second.count first.count_positive second.count_positive
  world := fire_comm first.physical second.physical
  equations := swapped_equations first second prior incoming apart
  rows := swapped_rows first second prior incoming apart
  retained := swapped_roots first second prior incoming apart
  templates := swapped_templates first second prior incoming apart

theorem actual_independent_selected_firings_commute (first second : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior)
    (apart : first.Independent second) :
    ∃ left right : Endpoint locals O Γ sort,
      ∃ forward : Quiver.Path before left, ∃ backward : Quiver.Path before right,
        Nonempty (EndpointPermutation left right) ∧
        ContextualExecution.selections forward = [first.selection, second.selection] ∧
        ContextualExecution.selections backward = [second.selection, first.selection] ∧
        ContextualExecution.fuels forward = [1, 1] ∧ ContextualExecution.fuels backward = [1, 1] :=
  ⟨first.twoTarget second prior incoming apart.orders.1, second.twoTarget first prior incoming apart.orders.2,
    first.twoPath second prior incoming apart.orders.1, second.twoPath first prior incoming apart.orders.2,
    ⟨endpointPermutation first second prior incoming apart⟩, rfl, rfl, rfl, rfl⟩

theorem actual_original_captures_fixed (first second : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior)
    (apart : first.Independent second) (name : before.Names) :
    (endpointPermutation first second prior incoming apart).names
      (namesAlong (first.twoPath second prior incoming apart.orders.1) name) =
        namesAlong (second.twoPath first prior incoming apart.orders.2) name := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedExecution
