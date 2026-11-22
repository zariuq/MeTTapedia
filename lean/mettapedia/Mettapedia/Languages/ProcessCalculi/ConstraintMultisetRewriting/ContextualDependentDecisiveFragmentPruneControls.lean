import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDecisiveFragmentPruneKept
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDecisiveFragmentControls

/-!
# A store that needs pruning, in the fragment and decided at one joint budget

Over `T : U0, F G : (a b : T) → U0`, the store `λ x y z. G y z ≐ λ x y z. F x y` has three
metavariables, and solving it needs pruning: `G` keeps only its first argument, then `F` is solved.

* It belongs to the dynamic pattern fragment (`flexFlex_in_fragment`).
* At budget 16 neither the distinct-locals rule nor the pattern rule fires. The reading of the
  equation and both of its orientations need no more budget (`searchFirm`, checked by the kernel),
  so both rules stay silent at every larger budget.
* At budget 16 the prune rule fires and leaves nothing to solve. Along its path every executable
  keeps its result and the readers do not use the budget, and its final pattern search needs no more
  budget (`pruneFirm`, checked by the kernel), so it returns the same answer at every larger budget.
* The class `{this store, empty stores}` therefore satisfies the settling criterion, and the rigid
  solver decides the store at one joint budget, with the same outcome at every larger joint budget;
  the outcome is a principal answer.

Every fact at budget 16 is evaluated by the kernel; every larger budget is covered by the kept-result
lemmas.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentDecisiveFragment.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentPatternSolver ContextualDependentDecisiveDriver
open ContextualDependentGeneralPattern ContextualDependentGeneralPattern.Controls ContextualDependentPatternSolver.Controls
open ContextualDependentNormalizing.Controls ContextualDependentDynamicFragment ContextualDependentDynamicFragment.Controls

/-- The prune rule of the controls at one budget. -/
abbrev pruned (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :=
  pruneRule (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique fuel problem

/-- The first rule of the controls that fires, at one budget. -/
abbrev first (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :=
  firstRule (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique fuel problem

/-! ## The distinct-locals rule never fires -/

theorem flex_reading_kept : ∀ larger, 16 ≤ larger → reading larger flexEquation = reading 16 flexEquation :=
  reading_kept flexEquation (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem flex_locals_none : locals 16 flexFlexStore = none := by decide +kernel

theorem flex_locals_kept : ∀ larger, 16 ≤ larger → locals larger flexFlexStore = none := by
  intro larger enough
  have kept := localsRule_singleton_kept ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none) flexEquation
    flex_reading_kept larger enough
  have atBudget := flex_locals_none
  rw [flexFlex_store_eq] at atBudget ⊢
  exact kept.trans atBudget

/-! ## The pattern rule never fires -/

theorem flex_newest_read : (ContextualDependentWorklist.newestOf (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16
    ContextualDependentPrune.Controls.metas).isSome := by decide +kernel

/-- The newest declaration `G`, read at budget 16. -/
def flexNewest : Newest (S := setting) ContextualDependentPrune.Controls.metas := Option.get _ flex_newest_read

/-- Both readings of the pattern search need no more budget. -/
theorem flex_pattern_firm : searchFirm (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) 16 flexNewest.type
    (flexNewest.same ▸ flexFlexStore) = true := by decide +kernel

theorem flex_pattern_kept : ∀ larger, 16 ≤ larger → rule larger flexFlexStore = rule 16 flexFlexStore :=
  patternRule_kept_of ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    DispatchControls.tower_normalizes DispatchControls.certifyNormal stable flexFlexStore
    (Option.some_get flex_newest_read).symm
    (searchFirm_kept ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
      TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
      ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
      DispatchControls.tower_normalizes DispatchControls.certifyNormal stable _ _ flex_pattern_firm)

theorem flex_pattern_none : rule 16 flexFlexStore = none := by decide +kernel

/-! ## The prune rule fires, kept from budget 16 -/

theorem flex_inner_read : (ContextualDependentWorklist.newestOf (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 flexNewest.base).isSome := by
  decide +kernel

/-- The next older declaration `F`, read at budget 16. -/
def flexInner : Newest (S := setting) flexNewest.base := Option.get _ flex_inner_read

/-- The store read at the two newest declarations. -/
abbrev twoStore := twoNewestStore flexNewest flexInner flexFlexStore

theorem two_length : twoStore.2.2.2.length = 1 := by decide +kernel

/-- The store's one equation, read at the two newest declarations. -/
def twoEquation : Equation (TotalTerm (extend (extend twoStore.1 twoStore.2.1) twoStore.2.2.1)) :=
  twoStore.2.2.2.head (List.ne_nil_of_length_pos (by rw [two_length]; decide))

theorem two_eq : twoStore.2.2.2 = [twoEquation] := singleton_of_length _ two_length

theorem two_reading_kept : ∀ larger, 16 ≤ larger → reading larger twoEquation = reading 16 twoEquation :=
  reading_kept twoEquation (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem two_viewed : (reading 16 twoEquation).isSome := by decide +kernel

/-- The scoped reading of the equation at budget 16. -/
def twoReading := Option.get _ two_viewed

theorem two_read : (readApplication twoReading.2.1.left.code).isSome := by decide +kernel

/-- The head and arguments of the opened left side `G y z`. -/
def twoApplied := Option.get _ two_read

theorem two_spine : (ContextualDependentPiSpineDiscovery.discover (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 twoApplied.2.length
    twoStore.2.2.1).isSome := by decide +kernel

/-- The spine of `G`'s type. -/
def twoSpine := Option.get _ two_spine

theorem two_recognized : (recognize twoSpine twoReading.1 twoReading.2.1).isSome := by decide +kernel

/-- The recognized pattern `G y z`. -/
def twoRecognized := Option.get _ two_recognized

/-- The prune rule on the recognized pattern, at one budget. -/
abbrev pruneStep (fuel : Nat) :=
  tryPrune (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique fuel twoStore.2.1 twoStore.2.2.1 twoReading.1
    twoReading.2.1 twoEquation twoReading.2.2 [] twoSpine twoRecognized

theorem prune_step_fires : (pruneStep 16).isSome := by decide +kernel

/-- The prune step's check that its final pattern search needs no more budget, at one budget. -/
abbrev pruneCheck (fuel : Nat) :=
  pruneFirm (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    DispatchControls.tower_normalizes ContextualDependentNormalCheckingTower.head_typing_unique fuel twoStore.2.1
    twoStore.2.2.1 twoReading.1 twoReading.2.1 twoEquation twoReading.2.2 [] twoSpine twoRecognized

theorem prune_firm_checked : pruneCheck 16 = true := by decide +kernel

set_option maxHeartbeats 1000000 in
attribute [local irreducible] flexNewest flexInner twoEquation twoReading twoApplied twoSpine twoRecognized
  ContextualDependentPatternSolver.searchStore ContextualDependentPiSpineDiscovery.discover
  ContextualDependentPruning.formType ContextualDependentGeneralPattern.assign ContextualDependentPatternSolver.dropPis
  ContextualDependentGeneralPattern.readApplication ContextualDependentGeneralPattern.localOf in
/-- **The prune step is kept from budget 16**: along its path, spine discovery and type formation
keep their results, the readers do not use the budget, and the final pattern search needs no more
budget. -/
theorem prune_step_kept : ∀ larger, 16 ≤ larger → pruneStep larger = pruneStep 16 := by
  intro larger enough
  obtain ⟨found, fires⟩ := Option.isSome_iff_exists.mp prune_step_fires
  revert fires
  unfold pruneStep tryPrune
  try dsimp only
  -- the older metavariable's application
  split
  · intro fires; cases fires
  rename_i headIndex arguments read
  -- its spine
  split
  · intro fires; cases fires
  rename_i olderSpine discovered
  simp only [discover_mono TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer stable _ _ discovered enough]
  try dsimp only
  -- its arguments as locals, and their positions
  split
  · intro fires; cases fires
  rename_i values valued
  split
  · intro fires; cases fires
  rename_i olderArgs assigned
  -- distinct arguments, compatible binders, the same type, the same side
  split
  swap
  · intro fires; cases fires
  rename_i distinct
  split
  swap
  · intro fires; cases fires
  rename_i olderCompatible
  try dsimp only
  split
  swap
  · intro fires; cases fires
  rename_i sameType
  split
  swap
  · intro fires; cases fires
  rename_i rightSame
  try dsimp only
  -- the deleted binders
  split
  · intro fires; cases fires
  rename_i keptCode dropped
  -- the pruned type
  split
  · intro fires; cases fires
  rename_i next formed
  simp only [ContextualDependentRecoveryBudget.formType_mono TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer stable formed enough]
  try dsimp only
  -- its spine, and the kept positions
  split
  · intro fires; cases fires
  rename_i kept discoveredKept
  simp only [discover_mono TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer stable _ _ discoveredKept enough]
  try dsimp only
  split
  · intro fires; cases fires
  rename_i keep keptAssigned
  -- distinct kept positions, compatible binders, the same result, covering
  split
  swap
  · intro fires; cases fires
  rename_i keptDistinct
  split
  swap
  · intro fires; cases fires
  rename_i keptCompatible
  split
  swap
  · intro fires; cases fires
  rename_i keptResult
  try dsimp only
  split
  swap
  · intro fires; cases fires
  rename_i covering
  try dsimp only
  -- the final pattern search needs no more budget
  intro _
  split <;>
  · rename_i searched
    have key := (searchFirm_pruned_kept (S := setting) _ _ _ _ _ _ _ _ _ _ _ _ _ stable _ _ _ _ _ _ _ _ _ _ ?firm
      larger enough).symm.trans searched
    case firm =>
      have checked := prune_firm_checked
      unfold pruneCheck pruneFirm at checked
      try dsimp only at checked
      split at checked
      · cases checked
      rename_i headIndex' arguments' readAgain
      rw [read] at readAgain
      cases readAgain
      split at checked
      · cases checked
      rename_i olderSpine' discoveredAgain
      rw [discovered] at discoveredAgain
      cases discoveredAgain
      try dsimp only at checked
      split at checked
      · cases checked
      rename_i values' valuedAgain
      rw [valued] at valuedAgain
      cases valuedAgain
      split at checked
      · cases checked
      rename_i olderArgs' assignedAgain
      rw [assigned] at assignedAgain
      cases assignedAgain
      simp only [dif_pos distinct, dif_pos olderCompatible, dif_pos sameType, dif_pos rightSame, dropped, formed,
        discoveredKept, dif_pos keptDistinct] at checked
      split at checked
      · cases checked
      rename_i keep' keptAssignedAgain
      rw [keptAssigned] at keptAssignedAgain
      cases keptAssignedAgain
      simp only [dif_pos keptCompatible, dif_pos keptResult, dif_pos covering] at checked
      exact checked
    simp only [key]

/-- The orientation of the prune rule that fires, at one budget. -/
abbrev pruneReading (fuel : Nat) :=
  pruneActive (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique fuel twoStore.2.1 twoStore.2.2.1 twoReading.1
    twoReading.2.1 twoEquation twoReading.2.2 []

theorem prune_reading_fires : (pruneReading 16).isSome := by decide +kernel

theorem prune_reading_kept : ∀ larger, 16 ≤ larger → pruneReading larger = pruneReading 16 :=
  pruneActive_kept ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique stable twoStore.2.1 twoStore.2.2.1 twoReading.1
    twoReading.2.1 twoEquation twoReading.2.2 [] (Option.some_get two_read).symm (Option.some_get two_spine).symm
    (Option.some_get two_recognized).symm prune_step_kept

theorem prune_search_kept : ∀ larger, 16 ≤ larger →
    pruneSearch (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
        TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
        ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
        DispatchControls.tower_normalizes DispatchControls.certifyNormal
        ContextualDependentNormalCheckingTower.head_typing_unique larger twoStore.2.1 twoStore.2.2.1 twoStore.2.2.2 =
      pruneSearch (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
        TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
        ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
        DispatchControls.tower_normalizes DispatchControls.certifyNormal
        ContextualDependentNormalCheckingTower.head_typing_unique 16 twoStore.2.1 twoStore.2.2.1 twoStore.2.2.2 := by
  have equationKept := pruneEquation_kept ContextualDependentPiSpine.Controls.rigid TowerModel.facts
    TowerModel.complete TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
    DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique twoStore.2.1
    twoStore.2.2.1 twoEquation [] (Option.some_get two_viewed).symm two_reading_kept
    (Option.some_get prune_reading_fires).symm prune_reading_kept
  have searchKept := pruneSearch_singleton_kept ContextualDependentPiSpine.Controls.rigid TowerModel.facts
    TowerModel.complete TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
    DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique twoStore.2.1
    twoStore.2.2.1 twoEquation equationKept
  intro larger enough
  rw [two_eq]
  exact (searchKept larger enough).trans (searchKept 16 le_rfl).symm

/-- **The prune rule on the store is kept from budget 16.** -/
theorem flex_prune_kept : ∀ larger, 16 ≤ larger → pruned larger flexFlexStore = pruned 16 flexFlexStore :=
  pruneRule_kept ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique stable flexFlexStore
    (Option.some_get flex_newest_read).symm (Option.some_get flex_inner_read).symm prune_search_kept

theorem flex_prune_fires : (pruned 16 flexFlexStore).isSome := by decide +kernel

/-- **The first rule that fires on the store is the prune rule's answer, kept from budget 16.** -/
theorem flex_first_kept : ∀ larger, 16 ≤ larger → first larger flexFlexStore = first 16 flexFlexStore := by
  have kept := firstRule_kept_of_prune ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique flexFlexStore flex_pattern_kept flex_pattern_none
    flex_prune_kept (Option.some_get flex_prune_fires).symm
  intro larger enough
  exact (kept larger enough).trans (kept 16 le_rfl).symm

theorem flex_first_fires : (first 16 flexFlexStore).isSome := by decide +kernel

/-- At budget 16 the first rule solves the store and leaves nothing. -/
theorem flex_first_finishes :
    (match first 16 flexFlexStore with
      | some (.solved update _) => update.remaining.isEmpty
      | _ => false) = true := by decide +kernel

/-! ## The class, the criterion, and decisiveness -/

/-- The store `G y z ≐ F x y`, and every empty store. -/
def flexClass {Γ : Context setting.R} (problem : EquationStore (TotalTerm Γ)) : Prop :=
  problem = [] ∨
    (⟨Γ, problem⟩ : (Γ : Context setting.R) × EquationStore (TotalTerm Γ)) =
      ⟨ContextualDependentPrune.Controls.metas, flexFlexStore⟩

/-- **The class satisfies the settling criterion.** -/
def flexSettled : Settled family :=
  settledWhereRuleFires (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique stable (fun problem => flexClass problem)
    (by
      intro Γ problem inside nonempty
      rcases inside with empty | same
      · exact absurd empty nonempty
      · cases same
        refine ⟨16, fun larger enough => .inr ⟨flex_locals_kept larger enough, ?_, ?_⟩⟩
        · change (first larger flexFlexStore).isSome
          rw [flex_first_kept larger enough]
          exact flex_first_fires
        · intro update smaller fired
          change first larger flexFlexStore = _ at fired
          rw [flex_first_kept larger enough] at fired
          have finishes := flex_first_finishes
          rw [fired] at finishes
          exact .inl (List.isEmpty_iff.mp finishes))

/-- **Decisiveness at one joint budget** on a store of the dynamic pattern fragment with three
metavariables, whose solution needs pruning: from one budget on, used both for the executables and
for the rounds, the rigid solver reaches the same outcome, a principal answer or a certified
refutation. -/
theorem flex_decided :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (family.solver larger) flexFlexStore larger = run (family.solver budget) flexFlexStore budget ∧
      ((∃ state finished, run (family.solver larger) flexFlexStore larger = .solved state finished ∧
          (frames setting.levels).Principal flexFlexStore state.answer) ∨
        (∃ absent, run (family.solver larger) flexFlexStore larger = .refuted absent)) :=
  flexSettled.decided (Or.inr rfl)

/-- The store is solvable, so the decided outcome is the principal answer. -/
theorem flex_solvable : (frames setting.levels).Solvable flexFlexStore := by
  obtain ⟨state, _, _, principal⟩ := ContextualDependentPatternSolver.Controls.flexFlex_principal
  exact ⟨_, state.answer, principal.sound⟩

/-- **The pruning store, in the fragment, decided with a principal answer at one joint budget.** -/
theorem flex_decided_principal :
    InFragmentStore flexFlexStore ∧
    ∃ budget, ∀ larger, budget ≤ larger →
      run (family.solver larger) flexFlexStore larger = run (family.solver budget) flexFlexStore budget ∧
      ∃ state finished, run (family.solver larger) flexFlexStore larger = .solved state finished ∧
        (frames setting.levels).Principal flexFlexStore state.answer := by
  refine ⟨flexFlex_in_fragment, ?_⟩
  obtain ⟨budget, decided⟩ := flex_decided
  refine ⟨budget, fun larger enough => ⟨(decided larger enough).1, ?_⟩⟩
  rcases (decided larger enough).2 with principal | ⟨absent, _⟩
  · exact principal
  · exact absurd flex_solvable absent

end ContextualDependentDecisiveFragment.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
