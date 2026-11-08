import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentInPlaceKept
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentFiringPiControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternSolverOccursControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDecisiveFragmentControls

/-!
# Solving in place on concrete stores

* **The solving-in-place witness is decided.** Over `A T : U0, G : (x : A) → T`, the store
  `T ≐ A` is in the dynamic pattern fragment and solvable, and every earlier solver leaves it
  suspended at every budget. The in-place solver strengthens the equation past `G`, solves
  `T := A` over `A T`, and carries the answer past `G`, whose type becomes `(x : A) → A`. From
  budget 16 on its round is the same; the in-place family **decides the store at one joint budget,
  with a principal answer** (`blocked_decided_principal`).
* **An occurs-check failure at depth is refused with a certificate.** Over
  `F : (A : U0) (c : A → A) (x : A) → A, P : Id _ F F`, where the later declaration `P` depends on
  `F`, the store `F A c x ≐ c (F A c x)` is refuted: strengthened past `P`, the occurs check refutes
  it over `F`. The refutation carries the absence of solutions. The Π solver leaves it suspended.
* **A solvable equation at the same depth commits**: `F A c x ≐ c x` over `F, P` is solved with a
  principal answer, `P`'s type instantiated.

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentInPlace.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiSpine ContextualDependentScope ContextualDependentWorklist
open ContextualDependentGeneralPattern ContextualDependentGeneralPattern.Controls
open ContextualDependentPatternSolver ContextualDependentPatternSolver.Controls
open ContextualDependentDynamicFragment ContextualDependentDecisiveFragment
open ContextualDependentFragment ContextualDependentFragment.Controls ContextualDependentUpdate

/-- The in-place solver of the tower controls, as a fuel-indexed family. -/
abbrev inPlaceTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  inPlaceFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The in-place solver at budget 16. -/
def inPlaceOnly : Solver setting.levels := inPlaceTower.solver 16

/-- The in-place round of the controls at one budget. -/
abbrev round (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :=
  inPlaceRound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) fuel problem

/-- The in-place rule of the controls at one budget and depth. -/
abbrev atDepth (fuel depth : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :=
  inPlaceAt (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique fuel depth problem

/-- The in-place rule of the controls at one budget. -/
abbrev rule (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :=
  inPlaceRule (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique fuel problem

/-- The newest declaration of the controls at one budget. -/
abbrev newest (fuel : Nat) (Θ : Context setting.R) :=
  ContextualDependentWorklist.newestOf (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer fuel Θ

/-- Separation of the controls at one budget. -/
abbrev separationAt (fuel : Nat) {Γ : Context setting.R} (type : TypeOver Γ)
    (problem : EquationStore (TotalTerm (extend Γ type))) :=
  separation (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer fuel type problem

/-- The pattern rule of the controls at one budget. -/
abbrev pattern (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :=
  patternRule (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    DispatchControls.tower_normalizes DispatchControls.certifyNormal fuel problem

/-! ## The solving-in-place witness -/

/-- **The in-place solver commits on `T ≐ A`.** -/
theorem blocked_inPlace_solved : (run inPlaceOnly blockedStore 2).readout = .commit := by decide +kernel

theorem blocked_inPlace_principal :
    ∃ state finished, run inPlaceOnly blockedStore 2 = .solved state finished ∧
      (frames setting.levels).Principal blockedStore state.answer := by
  obtain ⟨state, finished, solved⟩ := ContextualDependentWorklist.Controls.solved_of_commit blocked_inPlace_solved
  exact ⟨state, finished, solved, drive_solved_principal inPlaceOnly solved⟩

/-- **The answer instantiates `G`'s type**: the target context is `A : U0, G : (x : A) → A`. -/
theorem blocked_target :
    (match round 16 blockedStore with
      | .progress update _ =>
          match update.target with
          | ⟨_, .snoc (.snoc .nil first) second, _⟩ =>
              decide (first = .head (.sort Tower.zero)) && decide (second = .pi (.var 0) (.var 1))
          | _ => false
      | _ => false) = true := by decide +kernel

theorem blocked_newest_read : (newest 16 dependent).isSome := by decide +kernel

/-- The newest declaration `G`, read at budget 16. -/
def blockedView : Newest (S := setting) dependent := Option.get _ blocked_newest_read

theorem blocked_firm : strengthenFirm (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 blockedView.type (blockedView.same ▸ blockedStore) = true := by
  decide +kernel

/-- The store strengthened past `G`, over `A T`. -/
abbrev blockedStrong := (separationAt 16 blockedView.type (blockedView.same ▸ blockedStore)).val.1

theorem strong_newest_read : (newest 16 blockedView.base).isSome := by decide +kernel

/-- The newest declaration `T` of `A T`, read at budget 16. -/
def strongView : Newest (S := setting) blockedView.base := Option.get _ strong_newest_read

theorem strong_search_firm : searchFirm (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) 16 strongView.type
    (strongView.same ▸ blockedStrong) = true := by decide +kernel

theorem strong_pattern_kept : ∀ larger, 16 ≤ larger → pattern larger blockedStrong = pattern 16 blockedStrong :=
  patternRule_kept_of ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    DispatchControls.tower_normalizes DispatchControls.certifyNormal ContextualDependentDecisiveFragment.Controls.stable
    blockedStrong (Option.some_get strong_newest_read).symm
    (searchFirm_kept ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
      TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
      ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
      DispatchControls.tower_normalizes DispatchControls.certifyNormal
      ContextualDependentDecisiveFragment.Controls.stable _ _ strong_search_firm)

theorem strong_pattern_fires : (pattern 16 blockedStrong).isSome := by decide +kernel

theorem strong_zero_kept : ∀ larger, 16 ≤ larger →
    atDepth larger 0 blockedStrong = some ((pattern 16 blockedStrong).get strong_pattern_fires) :=
  inPlaceAt_zero_kept (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique blockedStrong strong_pattern_kept
    (Option.some_get strong_pattern_fires).symm

/-- **The in-place rule at depth 1 is kept from budget 16.** -/
theorem blocked_one_kept : ∀ larger, 16 ≤ larger → atDepth larger 1 blockedStore = atDepth 16 1 blockedStore :=
  inPlaceAt_succ_kept (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique ContextualDependentDecisiveFragment.Controls.stable
    blockedStore 0 (Option.some_get blocked_newest_read).symm
    (separation_kept (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer ContextualDependentDecisiveFragment.Controls.stable _ _ blocked_firm)
    (fun larger enough => (strong_zero_kept larger enough).trans (strong_zero_kept 16 le_rfl).symm)

theorem blocked_one_fires : (atDepth 16 1 blockedStore).isSome := by decide +kernel

/-- **The in-place rule is kept from budget 16.** -/
theorem blocked_rule_kept : ∀ larger, 16 ≤ larger → rule larger blockedStore = rule 16 blockedStore := by
  have key := inPlaceSearch_head_kept (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique blockedStore 1 [2]
    (found := (atDepth 16 1 blockedStore).get blocked_one_fires)
    (fun larger enough => (blocked_one_kept larger enough).trans (Option.some_get blocked_one_fires).symm)
  intro larger enough
  exact (key larger enough).trans (key 16 le_rfl).symm

theorem blocked_prepared (fuel : Nat) :
    ContextualDependentNormalizing.prepare (S := setting) (fun _ => none)
      (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) TowerModel.facts TowerModel.roots
      TowerModel.heads fuel blockedStore = Update.pending setting.levels blockedStore :=
  prepare_stopped (S := setting) (fun _ => none) (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))
    TowerModel.facts TowerModel.roots TowerModel.heads fuel blockedStore blocked_context_stopped blocked_codes_stopped

/-- **The in-place round on the witness is the same from budget 16 on.** -/
theorem blocked_round_kept : ∀ larger, 16 ≤ larger → round larger blockedStore = round 16 blockedStore :=
  inPlaceRound_kept (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) blockedStore
    (fun larger _ => blocked_piRound_stuck larger)
    (fun larger _ => (blocked_prepared larger).trans (blocked_prepared 16).symm)
    (by
      rw [blocked_prepared 16]
      exact blocked_rule_kept)

/-- At budget 16 the in-place round solves the witness and leaves nothing. -/
theorem blocked_round_finishes :
    (match round 16 blockedStore with
      | .progress update _ => update.remaining.isEmpty
      | _ => false) = true := by decide +kernel

/-- The witness, and every empty store. -/
def blockedClass {Γ : Context setting.R} (problem : EquationStore (TotalTerm Γ)) : Prop :=
  problem = [] ∨ (⟨Γ, problem⟩ : (Γ : Context setting.R) × EquationStore (TotalTerm Γ)) = ⟨dependent, blockedStore⟩

/-- **The in-place family settles on the witness.** -/
def blockedSettled : ContextualDependentDecisiveDriver.Settled inPlaceTower :=
  inPlaceSettledOfConst (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))
    ContextualDependentDecisiveFragment.Controls.stable (fun problem => blockedClass problem)
    (by
      intro Γ problem inside nonempty
      rcases inside with empty | same
      · exact absurd empty nonempty
      · cases same
        refine ⟨16, fun larger enough => ⟨?_, ?_⟩⟩
        · change round larger blockedStore ≠ .stuck
          rw [blocked_round_kept larger enough]
          intro stuck
          have finishes := blocked_round_finishes
          rw [stuck] at finishes
          cases finishes
        · intro update smaller fired
          change round larger blockedStore = _ at fired
          rw [blocked_round_kept larger enough] at fired
          have finishes := blocked_round_finishes
          rw [fired] at finishes
          exact .inl (List.isEmpty_iff.mp finishes))

/-- **The solving-in-place witness is decided at one joint budget**: from one budget on, used both
for the executables and for the rounds, the in-place solver reaches the same outcome, a principal
answer or a certified refutation. -/
theorem blocked_decided :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (inPlaceTower.solver larger) blockedStore larger = run (inPlaceTower.solver budget) blockedStore budget ∧
      ((∃ state finished, run (inPlaceTower.solver larger) blockedStore larger = .solved state finished ∧
          (frames setting.levels).Principal blockedStore state.answer) ∨
        (∃ absent, run (inPlaceTower.solver larger) blockedStore larger = .refuted absent)) :=
  blockedSettled.decided (Or.inr rfl)

/-- **The witness is decided with a principal answer**, since it is solvable. -/
theorem blocked_decided_principal :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (inPlaceTower.solver larger) blockedStore larger = run (inPlaceTower.solver budget) blockedStore budget ∧
      ∃ state finished, run (inPlaceTower.solver larger) blockedStore larger = .solved state finished ∧
        (frames setting.levels).Principal blockedStore state.answer := by
  obtain ⟨budget, decided⟩ := blocked_decided
  refine ⟨budget, fun larger enough => ⟨(decided larger enough).1, ?_⟩⟩
  rcases (decided larger enough).2 with principal | ⟨absent, _⟩
  · exact principal
  · exact absurd blocked_solvable absent

/-- **The witness of R90, now decided**: in the fragment, solvable, and decided at one joint budget with a
principal answer by the in-place family. -/
theorem blocked_now_decided :
    InFragmentStore blockedStore ∧ (frames setting.levels).Solvable blockedStore ∧
      ∃ budget, ∀ larger, budget ≤ larger →
        ∃ state finished, run (inPlaceTower.solver larger) blockedStore larger = .solved state finished ∧
          (frames setting.levels).Principal blockedStore state.answer := by
  obtain ⟨budget, decided⟩ := blocked_decided_principal
  exact ⟨blocked_in_fragment, blocked_solvable, budget, fun larger enough => (decided larger enough).2⟩

/-! ## An occurs-check failure at depth -/

theorem guard_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16
    (extend (empty Tower.rules) OccursControls.selfWhole)
    (.id (rename wk OccursControls.selfWhole.code) (.var 0) (.var 0))).isSome := by decide +kernel

/-- `P : Id _ F F`, a later declaration that depends on `F`. -/
def guardType : TypeOver (extend (empty Tower.rules) OccursControls.selfWhole) :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 (extend (empty Tower.rules) OccursControls.selfWhole)
    (.id (rename wk OccursControls.selfWhole.code) (.var 0) (.var 0))).get guard_formed).val

/-- `F : (A : U0) (c : A → A) (x : A) → A, P : Id _ F F`. -/
abbrev guarded := extend (extend (empty Tower.rules) OccursControls.selfWhole) guardType

/-- `F A c x ≐ c (F A c x)` over `F, P`. -/
def deepOccursStore : EquationStore (TotalTerm guarded) :=
  (frames setting.levels).applyStore (projectionHom _ guardType) OccursControls.occursStore

/-- `F A c x ≐ c x` over `F, P`. -/
def deepAppliedStore : EquationStore (TotalTerm guarded) :=
  (frames setting.levels).applyStore (projectionHom _ guardType) OccursControls.appliedStore

/-- **The in-place solver refutes the deep occurrence.** -/
theorem deep_occurs_refuted : (run inPlaceOnly deepOccursStore 2).readout = .refuted := by decide +kernel

/-- **The refutation is certified**: it carries the absence of solutions. -/
theorem deep_occurs_unsolvable : ¬ (frames setting.levels).Solvable deepOccursStore :=
  drive_refuted inPlaceOnly 2 _ deep_occurs_refuted

/-- The Π solver leaves it suspended: no rule of it reads `F` under the later `P`. -/
theorem deep_occurs_pi_suspended : (run piOnly deepOccursStore 4).readout = .suspended := by decide +kernel

/-- **A solvable equation at the same depth commits**, with `P`'s type instantiated. -/
theorem deep_applied_solved : (run inPlaceOnly deepAppliedStore 2).readout = .commit := by decide +kernel

theorem deep_applied_principal :
    ∃ state finished, run inPlaceOnly deepAppliedStore 2 = .solved state finished ∧
      (frames setting.levels).Principal deepAppliedStore state.answer := by
  obtain ⟨state, finished, solved⟩ := ContextualDependentWorklist.Controls.solved_of_commit deep_applied_solved
  exact ⟨state, finished, solved, drive_solved_principal inPlaceOnly solved⟩

theorem deep_applied_pi_suspended : (run piOnly deepAppliedStore 4).readout = .suspended := by decide +kernel

end ContextualDependentInPlace.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
