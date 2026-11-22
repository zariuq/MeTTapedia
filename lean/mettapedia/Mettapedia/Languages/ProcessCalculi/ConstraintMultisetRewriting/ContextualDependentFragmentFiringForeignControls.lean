import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentFiringForeign
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentFiringIdentityControls

/-!
# A solvable pattern store of the fragment that no solver ever solves

Over `A T : U0, G : (x : A) → T`, the store `T ≐ A` is

* **in the dynamic pattern fragment**: a Miller pattern of `T` at arity zero against a metavariable;
* **solvable**: `T := A`, with `G` kept at the instantiated type `(x : A) → A`;
* **suspended at every budget** by the rigid, decomposition, permuting, fragment and identity rounds.
  The pattern and prune rules read only the newest metavariable `G`. Exchange needs `G` independent
  of `T`, and `G`'s type mentions `T`. Rotation needs a deep declaration that the later ones do not
  mention, and `G` mentions `A`. The conversion scan cannot identify two distinct metavariables,
  and the dispatcher cannot align the universe with `G`'s Π type.

So newest-first elimination misses a metavariable that a later declaration depends on: solving in
place, with the dependent declarations instantiated, is missing from the rules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFragment.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiSpine ContextualDependentScope ContextualDependentWorklist
open ContextualDependentGeneralPattern ContextualDependentGeneralPattern.Controls
open ContextualDependentPatternSolver ContextualDependentPatternSolver.Controls
open ContextualDependentDynamicFragment ContextualDependentDecisiveFragment

/-! ## The store -/

/-- `A T : U0`. -/
abbrev twoTypes := ContextualDependentInversion.Controls.withExtra

theorem family_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 twoTypes
    (.pi (.var 1) (.var 1))).isSome := by decide +kernel

/-- `(x : A) → T` over `A T : U0`. -/
def familyType : TypeOver twoTypes :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes (.pi (.var 1) (.var 1))).get family_formed).val

/-- `A T : U0, G : (x : A) → T`. -/
abbrev dependent := extend twoTypes familyType

/-- The metavariable `T`. -/
def typeT : Term dependent (universeAt dependent) := ⟨(.var 1 : Tower.Tm 3), .var (1 : Fin 3)⟩

/-- The metavariable `A`. -/
def typeA : Term dependent (universeAt dependent) := ⟨(.var 2 : Tower.Tm 3), .var (2 : Fin 3)⟩

/-- `T ≐ A`. -/
def blockedActive : Active dependent := ⟨universeAt dependent, typeT, typeA⟩

def blockedStore : EquationStore (TotalTerm dependent) := closeStore ((Spine.stop (universeAt dependent)).toScoped blockedActive)

theorem blockedStore_length : blockedStore.length = 1 := by decide +kernel

def blockedEquation : Equation (TotalTerm dependent) :=
  blockedStore.head (List.ne_nil_of_length_pos (by rw [blockedStore_length]; decide))

theorem blockedStore_eq : blockedStore = [blockedEquation] :=
  ContextualDependentDynamicFragment.Controls.singleton_of_length blockedStore blockedStore_length

theorem blocked_left : blockedEquation.1.2.code = .var 1 := by decide +kernel
theorem blocked_right : blockedEquation.2.2.code = .var 2 := by decide +kernel
theorem blocked_annotation : blockedEquation.1.1.code = .head (.sort Tower.zero) := by decide +kernel

/-- **`T ≐ A` is in the dynamic pattern fragment.** -/
theorem blocked_in_fragment : InFragmentStore blockedStore := by
  rw [blockedStore_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have same : blockedEquation.2.1.code = blockedEquation.1.1.code := by decide +kernel
    rw [same]
    exact IsType.refl blockedEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-! ## Solvable -/

theorem endo_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 types
    (.pi (.var 0) (.var 1))).isSome := by decide +kernel

/-- `(x : A) → A` over `A : U0`. -/
def endoType : TypeOver types :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 types (.pi (.var 0) (.var 1))).get endo_formed).val

/-- `A : U0, G' : (x : A) → A`. -/
abbrev solvedContext := extend types endoType

/-- `T := A`, `A := A`, `G := G'`. -/
def solving : solvedContext ⟶ dependent where
  substitution := Fin.cases (.var 0) fun _ => .var 1
  typed := by
    intro index
    refine Fin.cases ?_ (fun prior => Fin.cases ?_ (fun prior' => ?_) prior) index
    · exact .var 0
    · exact .var 1
    · have only : prior' = 0 := Fin.fin_one_eq_zero prior'
      subst only
      exact .var 1

theorem blocked_closes : ∃ active,
    ((Spine.stop (universeAt dependent)).toScoped blockedActive).closeWith setting.levels
      ExecutableTowerChoices.choices = some active :=
  Option.isSome_iff_exists.mp (by decide +kernel)

/-- **`T ≐ A` is solvable**, by `T := A`. -/
theorem blocked_solvable : (frames setting.levels).Solvable blockedStore := by
  refine ⟨solvedContext, solving, ?_⟩
  apply (closeStore_models _ solving blocked_closes).mpr
  refine (Spine.toScoped_holds_iff (Spine.stop (universeAt dependent)) blockedActive solving).mpr ?_
  change Equal setting.R solvedContext.raw (.var 1) (.var 1) (.head (.sort Tower.zero))
  exact .refl (.var 1)

/-! ## No rule reads it -/

theorem blocked_foreign : ForeignEquation (S := setting) (fun _ => none) blockedEquation := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · rw [blocked_left]
    exact .inr ⟨⟨1, by decide⟩, by decide, rfl⟩
  · rw [blocked_right]
    exact .inr ⟨⟨2, by decide⟩, by decide, rfl⟩

/-- `G`'s type mentions `T`, so the exchange rule never applies. -/
theorem blocked_dependent : ∀ (Γ₀ : Context setting.R) (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older)),
    dependent = extend (extend Γ₀ older) newer →
      ContextualDependentInversion.invert (ContextualDependentPatternSolver.withoutNewest Γ₀.arity) newer.code = none := by
  intro Γ₀ older newer same
  obtain ⟨arity, raw, formed⟩ := Γ₀
  obtain ⟨olderCode, olderLevel, olderUniverse, olderFormed⟩ := older
  obtain ⟨newerCode, newerLevel, newerUniverse, newerFormed⟩ := newer
  cases same
  exact (by decide +kernel :
    ContextualDependentInversion.invert (ContextualDependentPatternSolver.withoutNewest 1) familyType.code = none)

/-- `G` mentions `A`, so `A` cannot be rotated past it. -/
theorem blocked_fixed : ∀ depth ∈ List.range' 2 (dependent.arity - 2),
    ContextualDependentPermutation.rotateRaw dependent.raw depth = none := by
  intro depth member
  rw [show List.range' 2 (dependent.arity - 2) = [2] from rfl] at member
  rw [List.mem_singleton.mp member]
  decide +kernel

/-- `T` and `A` are distinct metavariables, so conversion does not identify them. -/
theorem blocked_unequal :
    ¬ Equal setting.R dependent.raw blockedEquation.1.2.code blockedEquation.2.2.code blockedEquation.1.1.code := by
  rw [blocked_left, blocked_right]
  intro same
  have supports := ContextualDependentNormalSupport.equal_support ContextualDependentPiSpine.Controls.rigid
    TowerModel.complete dependent.formed same (ContextualDependentNormalObservations.normal_var
      ContextualDependentPiSpine.Controls.rigid _)
    (ContextualDependentNormalObservations.normal_var ContextualDependentPiSpine.Controls.rigid _)
  exact absurd supports (by decide +kernel)

/-- The dispatcher cannot align the universe with `G`'s Π type. -/
theorem blocked_noSearch (fuel : Nat) :
    ∀ view : Newest dependent, ∀ moved : Equation (TotalTerm (extend view.base view.type)), HEq moved blockedEquation →
      ContextualDependentDispatch.search (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
        TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
        ContextualDependentInversion.Controls.reducer fuel view.type [moved] = none := by
  intro view moved same
  obtain ⟨⟨arity, raw, formed⟩, ⟨code, level, universeWitness, typeFormed⟩, contexts⟩ := view
  cases contexts
  cases same
  apply search_misaligned (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer fuel ⟨_, level, universeWitness, typeFormed⟩ blockedEquation
  apply ContextualDependentRigid.not_typeEq_of_shapeClashes ContextualDependentPiSpine.Controls.rigid TowerModel.facts
    TowerModel.complete dependent.formed
  have family : familyType.code = .pi (.var 1) (.var 1) :=
    ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
      TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer 16 twoTypes (.pi (.var 1) (.var 1))).get family_formed).property
  change ContextualDependentRigid.shapeClashes setting.R blockedEquation.1.1.code (subst _ familyType.code) = true
  rw [family, blocked_annotation]
  simp [ContextualDependentRigid.shapeClashes, ContextualDependentRigid.shape, ContextualDependentRigid.former,
    ContextualDependentRigid.clashes, ContextualDependentRigid.Shape.kind, subst]

/-! ## Suspended at every budget -/

/-- **The rigid round is stuck on it at every budget.** -/
theorem blocked_rigidRound_stuck (fuel : Nat) :
    ContextualDependentRigidDecomposition.rigidRound (S := setting) ContextualDependentPiSpine.Controls.rigid
      TowerModel.complete TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
      DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique fuel [blockedEquation] =
        .stuck := by
  unfold ContextualDependentRigidDecomposition.rigidRound
  rw [localsRule_foreign (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none) fuel blockedEquation
    blocked_foreign]
  dsimp only
  erw [fullRound_eq]
  have first : firstRule (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
      TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
      ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
      DispatchControls.tower_normalizes DispatchControls.certifyNormal
      ContextualDependentNormalCheckingTower.head_typing_unique fuel [blockedEquation] = none := by
    unfold firstRule
    rw [patternRule_foreign (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts
      TowerModel.complete TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
      DispatchControls.certifyNormal fuel blockedEquation blocked_foreign]
    dsimp only
    rw [pruneRule_foreign (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts
      TowerModel.complete TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
      DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique fuel blockedEquation
      blocked_foreign]
    exact exchangeRule_dependent (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts
      TowerModel.complete TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
      DispatchControls.certifyNormal fuel _ blocked_dependent
  rw [first]
  dsimp only
  exact worklistRound_stuck_of_scan (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts
    TowerModel.complete TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer fuel blockedEquation (by decide +kernel) blocked_unequal
    (blocked_noSearch fuel)

/-- **The decomposition round is stuck on it at every budget.** -/
theorem blocked_decomposeRound_stuck (fuel : Nat) :
    ContextualDependentRigidDecomposition.decomposeRound (S := setting) ContextualDependentPiSpine.Controls.rigid
      TowerModel.facts TowerModel.complete TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
      DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique fuel [blockedEquation] =
        .stuck := by
  unfold ContextualDependentRigidDecomposition.decomposeRound
  rw [decomposeSearch_foreign (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts
    TowerModel.complete TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
    DispatchControls.certifyNormal fuel blockedEquation blocked_foreign]
  exact blocked_rigidRound_stuck fuel

theorem blocked_rotation (fuel : Nat) (problem : EquationStore (TotalTerm dependent)) :
    ContextualDependentPermutation.rotateRule (S := setting) ContextualDependentPiSpine.Controls.rigid
      TowerModel.complete TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
      DispatchControls.certifyNormal fuel problem = none :=
  rotateRule_none (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    DispatchControls.tower_normalizes DispatchControls.certifyNormal fuel problem blocked_fixed

/-- **The permuting round is stuck on it at every budget.** -/
theorem blocked_permutingRound_stuck (fuel : Nat) :
    ContextualDependentPermutation.permutingRound (S := setting) ContextualDependentPiSpine.Controls.rigid
      TowerModel.complete TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
      DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique fuel [blockedEquation] =
        .stuck := by
  unfold ContextualDependentPermutation.permutingRound
  rw [blocked_rigidRound_stuck fuel]
  dsimp only
  erw [blocked_rotation fuel]

theorem blocked_context_stopped : StoppedContext (S := setting) (fun _ => none) dependent.raw := by
  refine ⟨⟨⟨trivial, rfl⟩, rfl⟩, ?_⟩
  decide +kernel

theorem blocked_codes_stopped : ∀ equation ∈ blockedStore,
    StoppedTerm (S := setting) (fun _ => none) equation.1 ∧ StoppedTerm (S := setting) (fun _ => none) equation.2 := by
  rw [blockedStore_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  exact ⟨⟨by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel⟩⟩

/-- **The fragment round is stuck on it at every budget.** -/
theorem blocked_fragmentRound_stuck (fuel : Nat) :
    fragmentRound (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
      TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
      ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
      (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) DispatchControls.tower_normalizes
      DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique fuel blockedStore =
        .stuck := by
  apply fragmentRound_stuck_of_stopped (S := setting) (fun _ => none)
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) TowerModel.facts TowerModel.roots
    TowerModel.heads ContextualDependentPiSpine.Controls.rigid TowerModel.complete TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique fuel blockedStore blocked_context_stopped
    blocked_codes_stopped
  · rw [blockedStore_eq]
    exact blocked_decomposeRound_stuck fuel
  · exact blocked_rotation fuel blockedStore

/-- **The identity round is stuck on it at every budget**: its left side is not an identity type. -/
theorem blocked_identityRound_stuck (fuel : Nat) :
    identityRound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal
      ContextualDependentNormalCheckingTower.head_typing_unique
      (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) fuel blockedStore = .stuck := by
  have searched : idDecomposeSearch (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal fuel
      (ContextualDependentNormalizing.prepare (S := setting) (fun _ => none)
        (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) TowerModel.facts TowerModel.roots
        TowerModel.heads fuel blockedStore).remaining = none := by
    rw [prepare_stopped (S := setting) (fun _ => none)
      (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) TowerModel.facts TowerModel.roots
      TowerModel.heads fuel blockedStore blocked_context_stopped blocked_codes_stopped]
    change idDecomposeSearch (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal fuel blockedStore = none
    rw [blockedStore_eq]
    exact idDecomposeSearch_foreign (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts
      TowerModel.complete TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
      DispatchControls.certifyNormal fuel blockedEquation
      blocked_foreign (fun A a b same => by rw [blocked_left] at same; cases same)
  unfold identityRound
  split
  · rename_i update smaller found
    rw [searched] at found
    cases found
  · rename_i absent found
    rw [searched] at found
    cases found
  · exact blocked_fragmentRound_stuck fuel

theorem blockedStore_nonempty : blockedStore ≠ [] := by
  rw [blockedStore_eq]
  exact List.cons_ne_nil _ _

/-- **No budget and no number of rounds decides it**, for any of the solvers: the rigid, the
decomposition, the permuting, the fragment and the identity solver. -/
theorem blocked_never_decided (fuel rounds : Nat) :
    ¬ (run (rigidTower.solver fuel) blockedStore rounds).Decided ∧
      ¬ (run (decomposeTower fuel) blockedStore rounds).Decided ∧
      ¬ (run (permutingTower fuel) blockedStore rounds).Decided ∧
      ¬ (run (fragmentTower.solver fuel) blockedStore rounds).Decided ∧
      ¬ (run (identityTower.solver fuel) blockedStore rounds).Decided := by
  refine ⟨never_decided_of_stuck _ blockedStore_nonempty ?_ rounds,
    never_decided_of_stuck _ blockedStore_nonempty ?_ rounds,
    never_decided_of_stuck _ blockedStore_nonempty ?_ rounds,
    never_decided_of_stuck _ blockedStore_nonempty (blocked_fragmentRound_stuck fuel) rounds,
    never_decided_of_stuck _ blockedStore_nonempty (blocked_identityRound_stuck fuel) rounds⟩
  · rw [blockedStore_eq]; exact blocked_rigidRound_stuck fuel
  · rw [blockedStore_eq]; exact blocked_decomposeRound_stuck fuel
  · rw [blockedStore_eq]; exact blocked_permutingRound_stuck fuel

/-- **A solvable Miller-pattern store of the fragment that no solver ever solves.** -/
theorem blocked_not_decisive :
    InFragmentStore blockedStore ∧ (frames setting.levels).Solvable blockedStore ∧
      ∀ budget, ¬ (run (identityTower.solver budget) blockedStore budget).Decided ∧
        ¬ (run (fragmentTower.solver budget) blockedStore budget).Decided :=
  ⟨blocked_in_fragment, blocked_solvable, fun budget =>
    ⟨(blocked_never_decided budget budget).2.2.2.2, (blocked_never_decided budget budget).2.2.2.1⟩⟩

end ContextualDependentFragment.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
