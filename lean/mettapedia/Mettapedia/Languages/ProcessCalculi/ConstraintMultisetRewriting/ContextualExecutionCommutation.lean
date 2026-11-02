import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutationScopes

/-!
# Actual adjacent symbolic producers commute by an explicit endpoint renaming

Both orders below are constructed as paths of the original contextual
Firing relation. Their complete inventories correspond under a nonidentity
declaration isomorphism: original captures are fixed, the two live local
blocks are exchanged, every helper copy remains present, and retained root
lists differ only by permutation. Scope ownership and occupied ledgers are
also transported. The profile is check-free with an empty incoming equation
store; arbitrary solver-helper changes and guarded swaps are separate work.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualSchedulePromotion ContextualWorldScopeLedger
open ContextualExecutionCommutationNames

variable {S : Signature} {Local O : Type} {locals : Local → MetaArity S}
  [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  {Γ : Ctx S} {sort : S.Srt}

/-- Inventory equivalence preserves all occurrence rows and root
multiplicities. Retained roots are permitted to exchange positions. -/
structure EndpointRenaming (first second : Endpoint locals O Γ sort) : Type 1 where
  names : first.Names ≃ second.Names
  declarations : ∀ name, second.declarations (names name) = first.declarations name
  scopes : Equiv.Perm Nat
  scope_images : ∀ name, second.scopes (names name) = (first.scopes name).image scopes
  occupied : first.occupied.image scopes = second.occupied
  world : first.inventory.configuration.present = second.inventory.configuration.present
  equations : ContextualFrameUnifier.mapProblem (reindex names declarations)
    first.inventory.configuration.equations = second.inventory.configuration.equations
  rows : ∀ occurrence, (first.inventory.rows occurrence).map locals (reindex names declarations) =
    second.inventory.rows occurrence
  retained : (first.inventory.retained.map (instantiateObservation (reindex names declarations))).Perm
    second.inventory.retained
  templates : first.inventory.templates.map
    (instantiateObservation (ContextualStoredRows.liftCaptures locals (reindex names declarations))) =
      second.inventory.templates

variable {before : Endpoint locals O Γ sort}

def swapAssignment : Assignment (twiceDeclarations locals before.declarations)
    (twiceDeclarations locals before.declarations) := assignment locals before.declarations (swapScopes before.occupied)

omit [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem swap_earlier_term (producer : Producer before) (occurrence : O) :
    instantiate (swapAssignment (before := before)) (producer.earlierTerm occurrence) =
      producer.laterTerm occurrence := by
  rw [Producer.earlierTerm, ← Assignment.instantiate_compose]
  change instantiate (Assignment.compose (assignment locals before.declarations (swapScopes before.occupied))
    (intoEarlier locals before.declarations (firstScope before.occupied))) _ = _
  rw [earlier_into_later]
  simp only [swapScopes, Equiv.swap_apply_left]
  rfl

omit [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem swap_later_term (producer : Producer before) (occurrence : O) :
    instantiate (swapAssignment (before := before)) (producer.laterTerm occurrence) =
      producer.earlierTerm occurrence := by
  rw [Producer.laterTerm, ← Assignment.instantiate_compose]
  change instantiate (Assignment.compose (assignment locals before.declarations (swapScopes before.occupied))
    (intoLater locals before.declarations (secondScope before.occupied))) _ = _
  rw [later_into_earlier]
  simp only [swapScopes, Equiv.symm_swap, Equiv.swap_apply_right]
  rfl

theorem swapped_rows (first second : Producer before) (empty : before.inventory.configuration.equations = [])
    (separate : Disjoint second.made.toFinset first.made.toFinset) (occurrence : O) :
    ((first.twoTarget second empty separate).inventory.rows occurrence).map locals
      (swapAssignment (before := before)) =
        (second.twoTarget first empty separate.symm).inventory.rows occurrence := by
  rw [Producer.two_target_rows, Producer.two_target_rows]
  by_cases inFirst : occurrence ∈ first.made
  · have notSecond : occurrence ∉ second.made := by
      intro member
      exact Finset.disjoint_left.mp separate (by simpa using member) (by simpa using inFirst)
    simp only [if_pos inFirst, if_neg notSecond, ContextualStoredRows.Row.map, swap_earlier_term]
  · by_cases inSecond : occurrence ∈ second.made
    · simp only [if_neg inFirst, if_pos inSecond, ContextualStoredRows.Row.map, swap_later_term]
    · simp only [if_neg inFirst, if_neg inSecond]
      rw [ContextualStoredRows.Row.map_compose]
      exact congrArg (fun change => (before.inventory.rows occurrence).map locals change)
        (captures_fixed locals before.declarations (swapScopes before.occupied))

theorem swapped_retained_roots (first second : Producer before) (empty : before.inventory.configuration.equations = [])
    (separate : Disjoint second.made.toFinset first.made.toFinset) :
    ((first.twoTarget second empty separate).inventory.retained.map
      (instantiateObservation (swapAssignment (before := before)))).Perm
      (second.twoTarget first empty separate.symm).inventory.retained := by
  rw [Producer.two_target_retained, Producer.two_target_retained, List.map_append, List.map_append]
  have initial : (before.inventory.retained.map (instantiateObservation (intoOldCaptures locals before.declarations))).map
      (instantiateObservation (swapAssignment (before := before))) =
        before.inventory.retained.map (instantiateObservation (intoOldCaptures locals before.declarations)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro value _member
    rw [Function.comp_apply, instantiateObservation_comp]
    exact congrArg (fun change => instantiateObservation change value)
      (captures_fixed locals before.declarations (swapScopes before.occupied))
  rw [initial]
  have earlier : (first.made.map (fun occurrence => observe (first.earlierTerm occurrence))).map
      (instantiateObservation (swapAssignment (before := before))) =
        first.made.map (fun occurrence => observe (first.laterTerm occurrence)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro occurrence _member
    exact congrArg observe (swap_earlier_term first occurrence)
  have later : (second.made.map (fun occurrence => observe (second.laterTerm occurrence))).map
      (instantiateObservation (swapAssignment (before := before))) =
        second.made.map (fun occurrence => observe (second.earlierTerm occurrence)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro occurrence _member
    exact congrArg observe (swap_later_term second occurrence)
  rw [earlier, later]
  simpa only [List.append_assoc] using (List.perm_append_comm
    (l₁ := first.made.map (fun occurrence => observe (first.laterTerm occurrence)))
    (l₂ := second.made.map (fun occurrence => observe (second.earlierTerm occurrence)))).append_left
      (before.inventory.retained.map (instantiateObservation (intoOldCaptures locals before.declarations)))

theorem swapped_templates (first second : Producer before) (empty : before.inventory.configuration.equations = [])
    (separate : Disjoint second.made.toFinset first.made.toFinset) :
    (first.twoTarget second empty separate).inventory.templates.map
      (instantiateObservation (ContextualStoredRows.liftCaptures locals (swapAssignment (before := before)))) =
        (second.twoTarget first empty separate.symm).inventory.templates := by
  rw [Producer.two_target_templates, Producer.two_target_templates, List.map_map]
  apply List.map_congr_left
  intro value _member
  rw [Function.comp_apply, instantiateObservation_comp, ContextualStoredRows.liftCaptures_compose]
  exact congrArg (fun change => instantiateObservation (ContextualStoredRows.liftCaptures locals change) value)
    (captures_fixed locals before.declarations (swapScopes before.occupied))

def producerEndpointRenaming (first second : Producer before)
    (empty : before.inventory.configuration.equations = [])
    (separate : Disjoint second.made.toFinset first.made.toFinset)
    (scopeBound : ∀ name, before.scopes name ⊆ before.occupied) :
    EndpointRenaming (first.twoTarget second empty separate) (second.twoTarget first empty separate.symm) where
  names := namesEquiv (swapScopes before.occupied)
  declarations := exchange_preserves locals before.declarations (swapScopes before.occupied)
  scopes := swapScopes before.occupied
  scope_images name := scope_exchange before.scopes before.occupied scopeBound name
  occupied := swap_preserves_final_ledger before.occupied
  world := by rw [Producer.two_target_world, Producer.two_target_world]; exact Finset.union_right_comm _ _ _
  equations := by rw [Producer.two_target_equations, Producer.two_target_equations]; rfl
  rows := swapped_rows first second empty separate
  retained := swapped_retained_roots first second empty separate
  templates := swapped_templates first second empty separate

theorem actual_path_captures_are_fixed (first second : Producer before)
    (empty : before.inventory.configuration.equations = [])
    (separate : Disjoint second.made.toFinset first.made.toFinset)
    (scopeBound : ∀ name, before.scopes name ⊆ before.occupied) (name : before.Names) :
    (producerEndpointRenaming first second empty separate scopeBound).names
      (ContextualExecution.namesAlong (first.twoPath second empty separate) name) =
        ContextualExecution.namesAlong (second.twoPath first empty separate.symm) name := rfl

/-- These are paths of the source relation, not permutations of a checking
catalogue. The complete endpoint inventories are linked by the constructed
declaration isomorphism and its explicit scope permutation. -/
theorem actual_adjacent_producers_commute (first second : Producer before)
    (empty : before.inventory.configuration.equations = [])
    (separate : Disjoint second.made.toFinset first.made.toFinset)
    (scopeBound : ∀ name, before.scopes name ⊆ before.occupied) :
    ∃ left right : Endpoint locals O Γ sort,
      ∃ forward : Quiver.Path before left, ∃ backward : Quiver.Path before right,
        Nonempty (EndpointRenaming left right) ∧
        ContextualExecution.selections forward = [first.selection, second.selection] ∧
        ContextualExecution.selections backward = [second.selection, first.selection] ∧
        ContextualExecution.fuels forward = [0, 0] ∧ ContextualExecution.fuels backward = [0, 0] := by
  exact ⟨first.twoTarget second empty separate, second.twoTarget first empty separate.symm,
    first.twoPath second empty separate, second.twoPath first empty separate.symm,
    ⟨producerEndpointRenaming first second empty separate scopeBound⟩, rfl, rfl, rfl, rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutation
