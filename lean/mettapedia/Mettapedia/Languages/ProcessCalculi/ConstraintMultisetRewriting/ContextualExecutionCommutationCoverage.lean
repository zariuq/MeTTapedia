import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutation

/-!
# Producer commutation preserves formation without bounding unused names

An endpoint may declare infinitely many unused scoped names. CoveredWorld
bounds the actual roots, not every name in that carrier. The source formation
observation is whether a name's scopes are covered by the current ledger.
The explicit block exchange preserves that observation for every name,
without requiring every unused input name to be covered initially.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualScopeSupport ContextualFreshFrameScopeLedger
open ContextualExecutionCommutationNames

theorem swap_member_final_iff (occupied : Finset Nat) (scope : Nat) :
    swapScopes occupied scope ∈ Producer.nextLedger (Producer.nextLedger occupied) ↔
      scope ∈ Producer.nextLedger (Producer.nextLedger occupied) := by
  constructor
  · intro member
    have image : scope ∈ (Producer.nextLedger (Producer.nextLedger occupied)).image (swapScopes occupied) :=
      Finset.mem_image.mpr ⟨swapScopes occupied scope, member, by simp [swapScopes]⟩
    rw [swap_preserves_final_ledger] at image
    exact image
  · intro member
    have image : swapScopes occupied scope ∈
        (Producer.nextLedger (Producer.nextLedger occupied)).image (swapScopes occupied) :=
      Finset.mem_image.mpr ⟨scope, member, rfl⟩
    rw [swap_preserves_final_ledger] at image
    exact image

theorem covered_scope_exchange {Local V : Type} (scopes : V → Finset Nat) (occupied : Finset Nat)
    (name : Twice (Local := Local) (V := V)) :
    twiceScopes scopes occupied (exchange (swapScopes occupied) name) ⊆
        Producer.nextLedger (Producer.nextLedger occupied) ↔
      twiceScopes scopes occupied name ⊆ Producer.nextLedger (Producer.nextLedger occupied) := by
  cases name with
  | inr helper => rfl
  | inl active =>
      cases active with
      | inl name =>
          change ({((swapScopes occupied).symm name.scope)} : Finset Nat) ⊆
            Producer.nextLedger (Producer.nextLedger occupied) ↔
            ({name.scope} : Finset Nat) ⊆ Producer.nextLedger (Producer.nextLedger occupied)
          simp only [Finset.singleton_subset_iff, swapScopes, Equiv.symm_swap]
          exact swap_member_final_iff occupied name.scope
      | inr previous =>
          cases previous with
          | inr _ => rfl
          | inl active =>
              cases active with
              | inl name =>
                  change ({swapScopes occupied name.scope} : Finset Nat) ⊆
                    Producer.nextLedger (Producer.nextLedger occupied) ↔
                    ({name.scope} : Finset Nat) ⊆ Producer.nextLedger (Producer.nextLedger occupied)
                  simp only [Finset.singleton_subset_iff]
                  exact swap_member_final_iff occupied name.scope
              | inr _ => rfl

variable {S : Signature} {Local O : Type} {locals : Local → MetaArity S}
  [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  {Γ : Ctx S} {sort : S.Srt}

structure EndpointCoverageRenaming (first second : Endpoint locals O Γ sort) : Type 1 where
  names : first.Names ≃ second.Names
  declarations : ∀ name, second.declarations (names name) = first.declarations name
  scope_coverage : ∀ name, second.scopes (names name) ⊆ second.occupied ↔ first.scopes name ⊆ first.occupied
  occupied : first.occupied = second.occupied
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

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
private theorem covered_reindex_forward {V W : Type} {source : V → MetaArity S} {target : W → MetaArity S}
    (names : V → W) (preserves : ∀ name, target (names name) = source name)
    (oldScopes : V → Finset Nat) (newScopes : W → Finset Nat) (oldLedger newLedger : Finset Nat)
    (coverage : ∀ name, oldScopes name ⊆ oldLedger → newScopes (names name) ⊆ newLedger)
    {context : Ctx S} {result : S.Srt} (term : Term (signature S source) context result)
    (formed : Covered oldScopes oldLedger term) :
    Covered newScopes newLedger (instantiate (reindex names preserves) term) := by
  apply covered_instantiate newScopes newLedger _ term
  intro name present
  apply (covered_iff _ _ _).mpr
  intro image member
  rw [support_reindex] at member
  obtain rfl := List.mem_singleton.mp member
  exact coverage name ((covered_iff _ _ _).mp formed name present)

omit [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem EndpointCoverageRenaming.term_formation_iff {first second : Endpoint locals O Γ sort}
    (equivalence : EndpointCoverageRenaming first second) {context : Ctx S} {result : S.Srt}
    (term : Term (signature S first.declarations) context result) :
    Covered second.scopes second.occupied
        (instantiate (reindex equivalence.names equivalence.declarations) term) ↔
      Covered first.scopes first.occupied term := by
  constructor
  · intro formed
    let inversePreserves : ∀ name, first.declarations (equivalence.names.symm name) = second.declarations name :=
      fun name => (equivalence.declarations (equivalence.names.symm name)).symm.trans
        (congrArg second.declarations (equivalence.names.apply_symm_apply name))
    have transported := covered_reindex_forward equivalence.names.symm inversePreserves
      second.scopes first.scopes second.occupied first.occupied
      (fun name bounded => (equivalence.scope_coverage (equivalence.names.symm name)).mp
        (by simpa only [Equiv.apply_symm_apply] using bounded)) _ formed
    exact Eq.mp (congrArg (Covered first.scopes first.occupied)
      (instantiate_reindex_inverse equivalence.names equivalence.names.symm equivalence.declarations
        inversePreserves equivalence.names.symm_apply_apply term)) transported
  · exact covered_reindex_forward equivalence.names equivalence.declarations
      first.scopes second.scopes first.occupied second.occupied
      (fun name bounded => (equivalence.scope_coverage name).mpr bounded) term

variable {before : Endpoint locals O Γ sort}

def producerCoverageRenaming (first second : Producer before)
    (empty : before.inventory.configuration.equations = [])
    (separate : Disjoint second.made.toFinset first.made.toFinset) :
    EndpointCoverageRenaming (first.twoTarget second empty separate) (second.twoTarget first empty separate.symm) where
  names := namesEquiv (swapScopes before.occupied)
  declarations := exchange_preserves locals before.declarations (swapScopes before.occupied)
  scope_coverage := covered_scope_exchange before.scopes before.occupied
  occupied := rfl
  world := by rw [Producer.two_target_world, Producer.two_target_world]; exact Finset.union_right_comm _ _ _
  equations := by rw [Producer.two_target_equations, Producer.two_target_equations]; rfl
  rows := swapped_rows first second empty separate
  retained := swapped_retained_roots first second empty separate
  templates := swapped_templates first second empty separate

theorem actual_adjacent_producers_preserve_formation (first second : Producer before)
    (empty : before.inventory.configuration.equations = [])
    (separate : Disjoint second.made.toFinset first.made.toFinset) :
    ∃ left right : Endpoint locals O Γ sort,
      ∃ forward : Quiver.Path before left, ∃ backward : Quiver.Path before right,
        Nonempty (EndpointCoverageRenaming left right) ∧
        ContextualExecution.selections forward = [first.selection, second.selection] ∧
        ContextualExecution.selections backward = [second.selection, first.selection] :=
  ⟨first.twoTarget second empty separate, second.twoTarget first empty separate.symm,
    first.twoPath second empty separate, second.twoPath first empty separate.symm,
    ⟨producerCoverageRenaming first second empty separate⟩, rfl, rfl⟩

theorem actual_captures_preserved_without_unused_scope_bound (first second : Producer before)
    (empty : before.inventory.configuration.equations = [])
    (separate : Disjoint second.made.toFinset first.made.toFinset) (name : before.Names) :
    (producerCoverageRenaming first second empty separate).names
      (ContextualExecution.namesAlong (first.twoPath second empty separate) name) =
        ContextualExecution.namesAlong (second.twoPath first empty separate.symm) name := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutation
