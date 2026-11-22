import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentFiring
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentStoresPrepared
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDynamicFragmentControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDecisiveFragmentSingle

/-!
# A one-equation store of the dynamic pattern fragment that no rule decides

Over `T : U0`, the store `λ a b. Id T a b ≐ λ a b. Id T b a` is

* **in the dynamic pattern fragment**: its annotation `(a b : T) → U0` is normal, its opened sides
  `Id T a b` and `Id T b a` are normal with Miller occurrences (`T` is a metavariable at arity
  zero);
* **unsolvable in every future context**: equal identity types have equal endpoints, and the
  endpoints are distinct rigid locals;
* **suspended at every budget** by the rigid round, the decomposition round, the permuting round
  and the fragment round: the opened sides are identity types, which no rule reads; there is no
  clash; the conversion scan cannot discharge an unsolvable equation; the annotation, a Π type,
  never aligns with the universe that types `T`; and preparation leaves the stopped store unchanged.

So at no joint budget does any of these families reach a principal answer or a refutation on it. The
one-equation reduction `single_decided` does not extend to every one-equation store of the
fragment: decomposition of rigid type formers is missing from the rules.

Every hypothesis of the general lemmas is discharged here; the runs at budget 16 are checked by the
kernel as well.
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

/-- `Id T a b ≐ Id T b a` under the telescope `a b : T`. -/
def idActive : Active spine.target := ⟨spine.result, orderedBody, swappedBody⟩

/-- `λ a b. Id T a b ≐ λ a b. Id T b a` over `T : U0`. -/
def idStore : EquationStore (TotalTerm types) := closeStore (spine.toScoped idActive)

theorem idStore_length : idStore.length = 1 := by decide +kernel

/-- The equation of the store. -/
def idEquation : Equation (TotalTerm types) :=
  idStore.head (List.ne_nil_of_length_pos (by rw [idStore_length]; decide))

theorem idStore_eq : idStore = [idEquation] :=
  ContextualDependentDynamicFragment.Controls.singleton_of_length idStore idStore_length

/-! ## In the dynamic pattern fragment -/

/-- **`λ a b. Id T a b ≐ λ a b. Id T b a` is in the dynamic pattern fragment.** -/
theorem id_in_fragment : InFragment idEquation := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have same : idEquation.2.1.code = idEquation.1.1.code := by decide +kernel
    rw [same]
    exact IsType.refl idEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

theorem idStore_in_fragment : InFragmentStore idStore := by
  rw [idStore_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  exact id_in_fragment

/-! ## Unsolvable in every future context -/

/-- The carrier `T` under the telescope `a b : T`. -/
def carrierAt : TypeOver spine.target := ⟨(.var 2 : Tower.Tm 3), .sort Tower.zero, .sort _, .var (2 : Fin 3)⟩

/-- `a ≐ b` at `T`. -/
def endpoints : Active spine.target :=
  ⟨carrierAt, ⟨(.var 1 : Tower.Tm 3), .var (1 : Fin 3)⟩, ⟨(.var 0 : Tower.Tm 3), .var (0 : Fin 3)⟩⟩

theorem idStore_closes : ∃ active, (spine.toScoped idActive).closeWith setting.levels ExecutableTowerChoices.choices =
    some active :=
  Option.isSome_iff_exists.mp (by decide +kernel)

/-- **No solution in any future context**: equal identity types have equal endpoints, and the
endpoints are distinct rigid locals. -/
theorem idStore_unsolvable : ¬ (frames setting.levels).Solvable idStore := by
  rintro ⟨Δ, solution, solved⟩
  have held := (closeStore_models (spine.toScoped idActive) solution idStore_closes).mp solved
  replace held := (Spine.toScoped_holds_iff spine idActive solution).mp held
  change Equal setting.R (spine.reindex solution).target.raw
      (.id ((spine.map solution).substitution (2 : Fin 3)) ((spine.map solution).substitution (1 : Fin 3))
        ((spine.map solution).substitution (0 : Fin 3)))
      (.id ((spine.map solution).substitution (2 : Fin 3)) ((spine.map solution).substitution (0 : Fin 3))
        ((spine.map solution).substitution (1 : Fin 3)))
      (.head (.sort Tower.zero)) at held
  have types : TypeEq setting.R (spine.reindex solution).target.raw
      (.id ((spine.map solution).substitution (2 : Fin 3)) ((spine.map solution).substitution (1 : Fin 3))
        ((spine.map solution).substitution (0 : Fin 3)))
      (.id ((spine.map solution).substitution (2 : Fin 3)) ((spine.map solution).substitution (0 : Fin 3))
        ((spine.map solution).substitution (1 : Fin 3))) := ⟨_, .sort _, held⟩
  obtain ⟨_, ends, _⟩ := (ContextualDependentRigid.typeEq_id_iff TowerModel.facts
    (spine.reindex solution).target.formed).mp types
  apply ContextualDependentRigidDecomposition.distinct_locals_refuted ContextualDependentPiSpine.Controls.rigid
    TowerModel.complete spine endpoints (.inl ()) (.inr (.inl ())) (by intro same; cases same)
    (by rfl') (by rfl') solution ((Spine.toScoped_holds_iff spine endpoints solution).mpr ends)

/-! ## No rule reads it -/

/-- **Both opened sides are silent at every budget**: they are identity types or the β-redexes of
the opened abstractions, and the normalizer only ever returns the identity types. -/
theorem id_silent : SilentEquation (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) idEquation := by
  intro fuel reading read
  obtain ⟨found, leftCode, right, rightSame, rightCode⟩ := viewEquation_codes (S := setting) TowerModel.facts
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none) fuel idEquation read
  have depth : lamDepth idEquation.1.2.code = 2 := by decide +kernel
  rw [depth] at found
  have opened : ∀ term : Term types idEquation.1.1,
      (Silent (Tm.app (Presentation.rename wk (Tm.app (Presentation.rename wk term.code) (.var 0))) (.var 0)) ∧
        ∀ fuel' result, ExecutableReduction.normalize setting.R (fun _ => none) fuel'
          (Tm.app (Presentation.rename wk (Tm.app (Presentation.rename wk term.code) (.var 0))) (.var 0)) =
            some result → Silent result.val) →
      Silent (normalizeAt (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads (fun _ => none) fuel
        (reading.1.openFunction term)).1.code := by
    intro term holds
    have both := discover_two_code (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer fuel _ reading.1 found term
      (fun code => Silent code ∧ ∀ fuel' result,
        ExecutableReduction.normalize setting.R (fun _ => none) fuel' code = some result → Silent result.val) holds
    exact normalizeAt_silent (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads (fun _ => none) fuel _
      both.1 (both.2 fuel)
  refine ⟨?_, ?_⟩
  · rw [leftCode]
    exact opened idEquation.1.2 ⟨silent_of_silentB (by decide +kernel),
      normalize_results_silent (S := setting) (fun _ => none) 8 _ (by decide +kernel) (by decide +kernel)⟩
  · rw [rightCode]
    apply opened
    rw [rightSame]
    exact ⟨silent_of_silentB (by decide +kernel),
      normalize_results_silent (S := setting) (fun _ => none) 8 _ (by decide +kernel) (by decide +kernel)⟩

theorem idEquation_unsolvable : ¬ (frames setting.levels).Solvable [idEquation] := by
  intro solvable
  apply idStore_unsolvable
  rw [idStore_eq]
  exact solvable

/-- **The rigid round is stuck on it at every budget.** -/
theorem id_rigidRound_stuck (fuel : Nat) :
    ContextualDependentRigidDecomposition.rigidRound (S := setting) ContextualDependentPiSpine.Controls.rigid
      TowerModel.complete TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
      DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique fuel [idEquation] =
        .stuck := by
  unfold ContextualDependentRigidDecomposition.rigidRound
  rw [localsRule_silent (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none) fuel idEquation id_silent]
  dsimp only
  erw [fullRound_eq]
  rw [firstRule_silent (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts
    TowerModel.complete TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
    DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique fuel rfl idEquation id_silent]
  dsimp only
  exact worklistRound_stuck (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete fuel
    idEquation (by decide +kernel) idEquation_unsolvable (exists_pi_of_isPiB (by decide +kernel))
    ⟨0, .nil, .sort Tower.zero, types.formed, rfl⟩

/-- **The decomposition round is stuck on it at every budget.** -/
theorem id_decomposeRound_stuck (fuel : Nat) :
    ContextualDependentRigidDecomposition.decomposeRound (S := setting) ContextualDependentPiSpine.Controls.rigid
      TowerModel.facts TowerModel.complete TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
      DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique fuel [idEquation] =
        .stuck := by
  unfold ContextualDependentRigidDecomposition.decomposeRound
  rw [decomposeSearch_silent (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts
    TowerModel.complete TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
    DispatchControls.certifyNormal fuel idEquation id_silent]
  exact id_rigidRound_stuck fuel

/-- **The permuting round is stuck on it at every budget.** -/
theorem id_permutingRound_stuck (fuel : Nat) :
    ContextualDependentPermutation.permutingRound (S := setting) ContextualDependentPiSpine.Controls.rigid
      TowerModel.complete TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
      DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique fuel [idEquation] =
        .stuck := by
  unfold ContextualDependentPermutation.permutingRound
  rw [id_rigidRound_stuck fuel]
  dsimp only
  rw [rotateRule_short (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    DispatchControls.tower_normalizes DispatchControls.certifyNormal fuel (by decide) [idEquation]]

/-! ## Never decided -/

/-- The rigid family in the tower. -/
abbrev rigidTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  rigidFamily (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    DispatchControls.tower_normalizes DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique

/-- The decomposition solver in the tower, at one budget. -/
abbrev decomposeTower (fuel : Nat) : Solver setting.levels :=
  ContextualDependentRigidDecomposition.decomposeSolver (S := setting) ContextualDependentPiSpine.Controls.rigid
    TowerModel.facts TowerModel.complete TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
    DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique fuel

/-- The permuting solver in the tower, at one budget. -/
abbrev permutingTower (fuel : Nat) : Solver setting.levels :=
  ContextualDependentPermutation.permutingSolver (S := setting) ContextualDependentPiSpine.Controls.rigid
    TowerModel.complete TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
    DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique fuel

theorem idStore_nonempty : idStore ≠ [] := by
  rw [idStore_eq]
  exact List.cons_ne_nil _ _

/-- **No budget and no number of rounds decides it**, for the rigid, decomposition and permuting
solvers: the runs end suspended or cut off, never with a principal answer or a refutation. -/
theorem id_never_decided (fuel rounds : Nat) :
    ¬ (run (rigidTower.solver fuel) idStore rounds).Decided ∧
      ¬ (run (decomposeTower fuel) idStore rounds).Decided ∧
      ¬ (run (permutingTower fuel) idStore rounds).Decided := by
  refine ⟨never_decided_of_stuck _ idStore_nonempty ?_ rounds, never_decided_of_stuck _ idStore_nonempty ?_ rounds,
    never_decided_of_stuck _ idStore_nonempty ?_ rounds⟩
  · rw [idStore_eq]; exact id_rigidRound_stuck fuel
  · rw [idStore_eq]; exact id_decomposeRound_stuck fuel
  · rw [idStore_eq]; exact id_permutingRound_stuck fuel

/-- **The one-equation reduction does not reach every one-equation store of the fragment**: this
one is in the dynamic pattern fragment and unsolvable, yet at no joint budget does the rigid family
reach a principal answer or a refutation. -/
theorem rigid_not_decisive_on_fragment :
    InFragmentStore idStore ∧ ¬ (frames setting.levels).Solvable idStore ∧
      ¬ ∃ budget, ∀ larger, budget ≤ larger →
        run (rigidTower.solver larger) idStore larger = run (rigidTower.solver budget) idStore budget ∧
        ((∃ state finished, run (rigidTower.solver larger) idStore larger = .solved state finished ∧
            (frames setting.levels).Principal idStore state.answer) ∨
          (∃ absent, run (rigidTower.solver larger) idStore larger = .refuted absent)) := by
  refine ⟨idStore_in_fragment, idStore_unsolvable, ?_⟩
  rintro ⟨budget, decided⟩
  have never := (id_never_decided budget budget).1
  rcases (decided budget le_rfl).2 with ⟨state, finished, solved, _⟩ | ⟨absent, refuted⟩
  · rw [solved] at never; exact never trivial
  · rw [refuted] at never; exact never trivial

/-! ## The fragment solver, checked by the kernel -/

/-- The fragment solver in the tower at budget 16. -/
def fragmentOnly : Solver setting.levels :=
  fragmentSolver (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) DispatchControls.tower_normalizes
    DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique 16

/-- **The fragment solver leaves it suspended**, at budget 16. -/
theorem id_fragment_suspended : (run fragmentOnly idStore 4).readout = .suspended := by decide +kernel

/-- **The fragment solver commits on R86's pruning store**, with a principal answer. -/
theorem flexFlex_fragment_solved :
    (run fragmentOnly ContextualDependentPatternSolver.Controls.flexFlexStore 2).readout = .commit := by
  decide +kernel

/-! ## The fragment solver at every budget -/

theorem types_stopped : StoppedContext (S := setting) (fun _ => none) types.raw := ⟨trivial, rfl⟩

theorem idStore_stopped : ∀ equation ∈ idStore,
    StoppedTerm (S := setting) (fun _ => none) equation.1 ∧ StoppedTerm (S := setting) (fun _ => none) equation.2 := by
  rw [idStore_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  exact ⟨⟨by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel⟩⟩

/-- **The fragment round is stuck on it at every budget**: preparation leaves the stopped store
unchanged, the decomposition round is stuck, and one declaration is too few to rotate. -/
theorem id_fragmentRound_stuck (fuel : Nat) :
    fragmentRound (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
      TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
      ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
      (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) DispatchControls.tower_normalizes
      DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique fuel idStore = .stuck := by
  apply fragmentRound_stuck_of_stopped (S := setting) (fun _ => none)
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) TowerModel.facts TowerModel.roots
    TowerModel.heads ContextualDependentPiSpine.Controls.rigid TowerModel.complete TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique fuel idStore types_stopped idStore_stopped
  · rw [idStore_eq]
    exact id_decomposeRound_stuck fuel
  · exact rotateRule_short (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
      TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
      ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
      DispatchControls.tower_normalizes DispatchControls.certifyNormal fuel (by decide) idStore

/-- The fragment family in the tower. -/
abbrev fragmentTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  fragmentFamily (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) DispatchControls.tower_normalizes
    DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique

/-- **The fragment family never decides it either**, at any budget and any number of rounds. -/
theorem id_fragment_never_decided (fuel rounds : Nat) : ¬ (run (fragmentTower.solver fuel) idStore rounds).Decided :=
  never_decided_of_stuck _ idStore_nonempty (id_fragmentRound_stuck fuel) rounds

/-- **Decisiveness fails on the dynamic pattern fragment for the strongest solver**: the store is
in the fragment and unsolvable, and the fragment family, which prepares, decomposes, runs every rigid
rule and rotates, reaches neither a principal answer nor a refutation at any joint budget. -/
theorem fragment_not_decisive :
    InFragmentStore idStore ∧ ¬ (frames setting.levels).Solvable idStore ∧
      ∀ budget, ¬ (run (fragmentTower.solver budget) idStore budget).Decided :=
  ⟨idStore_in_fragment, idStore_unsolvable, fun budget => id_fragment_never_decided budget budget⟩

end ContextualDependentFragment.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
