import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.MillerFamily
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.RankRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MixedControls

/-!
# The computable settler with no budget of rounds

The computable settler's families ran the tree's worklist driver with fixed budgets of rounds: 4 for the tree's step,
16 for the in-place solver after type extraction, 6 for the Miller solver. A run cut off by its budget declines, and a
decline postpones, so the budgets were sound; but a store needing one more round was postponed although its solver
decides it. Every solver of the driver carries the decrease of its own rank in every round that progresses, so its run
needs no budget (`UnificationWithLevels.TreeFibre.runRank`, computed by structural recursion with the budgets read off
the rank).

* **A driver family with no budget** (`rankFamily`): the decision read off the run driven by the solver's rank. Wherever
  the family with some budget decides, it decides the same (`rankFamily_of_decisive`), and it is the family of every
  large enough budget (`rankFamily_eventually`).
* **The settler's families with no budget** (`rankFamilies`): the tree's step (`stepRankFamily`), the older-unknown
  family (`olderRankFamily`: type extraction, then the in-place solver driven by its own rank, the telescope's length
  then the number of equations), the Miller family with computed trimming (`millerRankFamily`), and the family of the
  one common rank (`mixedRankFamily`: the solver of stores mixing Miller patterns with arrow codes).
* **It decides every store the budgeted settler decides** (`rank_decidedBy_of_all`), and on the union of its decided
  fragments it agrees with the semantic settler (`rank_agrees_ideal`, `rank_steps_iff_ideal`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate
open UnificationWithLevels (InitialSolution Agree)
open UnificationWithLevels.TreeFibre (runRank run_eq_runRank runRank_eventually)

/-! ## A driver family with no budget of rounds -/

section Driver

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} (levels : LevelModel rules L)
variable [DecidableEq Head]

/-- **The decision a driver family reads off an outcome**: a solved run whose answer covers its frame settles along it,
a refuted run refutes, every other outcome declines. -/
def decisionOf {Δ : Context rules} {I : EquationStore (TotalTerm Δ)} :
    ContextualDependentWorklist.Outcome levels I → Decision levels I
  | .solved state finished =>
      if cover : VariableCover state.answer then
        .settled state.target state.answer (initial_of_cover levels (state.completed finished) cover)
      else .undecided
  | .refuted absent => .refuted absent
  | .stuck _ => .undecided
  | .cutoff _ => .undecided

/-- A driver family with a budget reads its decision off the run with that budget. -/
theorem driverFamily_eq (solver : ContextualDependentWorklist.Solver levels) (fuel : Nat) {Δ : Context rules}
    (I : EquationStore (TotalTerm Δ)) :
    driverFamily levels solver fuel I = decisionOf levels (ContextualDependentWorklist.run solver I fuel) := by
  unfold driverFamily decisionOf
  cases ContextualDependentWorklist.run solver I fuel <;> rfl

/-- **The tree's worklist driver as a decided family, with no budget of rounds**: its run is driven by the solver's
rank. -/
def rankFamily (solver : ContextualDependentWorklist.Solver levels) : Family levels :=
  fun I => decisionOf levels (runRank solver I)

/-- A decisive decision is read off a finished run. -/
theorem finished_of_decisive {Δ : Context rules} {I : EquationStore (TotalTerm Δ)}
    {outcome : ContextualDependentWorklist.Outcome levels I} (decisive : (decisionOf levels outcome).Decisive) :
    outcome.Finished := by
  cases outcome
  · trivial
  · trivial
  · trivial
  · exact False.elim decisive

/-- **No cliff**: wherever the driver family with some budget decides, the family driven by the rank decides the
same. -/
theorem rankFamily_of_decisive {solver : ContextualDependentWorklist.Solver levels} {fuel : Nat} {Δ : Context rules}
    {I : EquationStore (TotalTerm Δ)} (decisive : (driverFamily levels solver fuel I).Decisive) :
    rankFamily levels solver I = driverFamily levels solver fuel I := by
  rw [driverFamily_eq] at decisive ⊢
  unfold rankFamily
  rw [← run_eq_runRank solver (finished_of_decisive levels decisive)]

/-- **The family driven by the rank is the driver family of every large enough budget.** -/
theorem rankFamily_eventually (solver : ContextualDependentWorklist.Solver levels) {Δ : Context rules}
    (I : EquationStore (TotalTerm Δ)) :
    ∃ bound, ∀ fuel, bound ≤ fuel → driverFamily levels solver fuel I = rankFamily levels solver I := by
  obtain ⟨bound, same⟩ := runRank_eventually solver I
  refine ⟨bound, fun fuel enough => ?_⟩
  rw [driverFamily_eq, same fuel enough]
  rfl

end Driver

/-! ## The settler's families with no budget of rounds -/

namespace RankSettler

open Interface.DependentFull Interface.DependentFull.Controls
open UnificationWithLevels.TreeFibre (famCode trimOut)
open ComputableControls OlderUnknown MillerFamily

/-- **The tree's step, driven by its rank.** -/
def stepRankFamily : Family setting.levels :=
  rankFamily setting.levels ContextualDependentWorklist.Controls.step

/-- **The older-unknown family, driven by the in-place solver's rank**: type extraction, then the tree's in-place solver,
whose rank is the telescope's length then the number of equations. -/
def olderRankFamily : Family setting.levels :=
  Family.prepared setting.levels (fun I => prepareTower I) (rankFamily setting.levels inPlace)

/-- **The Miller family, driven by the Miller rank**: on a store of the fragment, a solved run settles along its trimmed
answer, a refuted run refutes; every other store is declined. -/
def millerRankFamily : Family setting.levels := fun I =>
  if inside : UnificationWithLevels.TreeFibre.Miller.inMillerGlbB (S := setting) I = true then
    match solved : runRank millerTower I with
    | .solved state finished =>
        match views? state.target with
        | some v =>
            .settled _
              (trimOut v.val v.property.1 (fun j => v.property.2 j) towerInh
                (UnificationWithLevels.TreeFibre.Miller.mentionedOf state.answer) ≫ state.answer)
              (by
                obtain ⟨bound, same⟩ := runRank_eventually millerTower I
                exact UnificationWithLevels.TreeFibre.Miller.initial_of_patternTrimmed (S := setting)
                  TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
                  ContextualDependentPiSpine.Controls.rigid TowerModel.complete towerInh
                  (state.completed finished) v.val v.property.1 (fun j => v.property.2 j)
                  (UnificationWithLevels.TreeFibre.Miller.drive_inv (S := setting) TowerModel.facts
                    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentPiSpine.Controls.rigid
                    TowerModel.complete ContextualDependentGeneralPattern.DispatchControls.tower_normalizes towerInh
                    ContextualDependentNormalCheckingTower.head_typing_unique
                    UnificationWithLevels.TreeFibre.LevelGlb.towerGlb
                    UnificationWithLevels.TreeFibre.LevelGlb.towerGlb_isGlb bound
                    (Update.pending setting.levels I)
                    (UnificationWithLevels.TreeFibre.Miller.MillerInv.pending
                      (UnificationWithLevels.TreeFibre.Miller.inMillerGlb_of_B I inside).families I)
                    (UnificationWithLevels.TreeFibre.Miller.inMillerGlb_of_B I inside) state finished
                    ((same bound le_rfl).trans solved)).1.covered)
        | none => .undecided
    | .refuted absent => .refuted absent
    | .stuck _ => .undecided
    | .cutoff _ => .undecided
  else .undecided

/-- **The family of the one common rank**: the solver of stores mixing Miller patterns with arrow codes, driven by the
common rank (the occurrence weight, then the size). -/
def mixedRankFamily : Family setting.levels :=
  rankFamily setting.levels UnificationWithLevels.TreeFibre.Controls.towerMixedSolver

/-- **The settler's families with no budget of rounds.** -/
def rankFamilies : List (Family setting.levels) :=
  [stepRankFamily, olderRankFamily, millerRankFamily, mixedRankFamily]

/-- **The computable settler with no budget of rounds.** -/
def rankSettler : Settler setting.levels := Settler.ofFamilies setting.levels rankFamilies

/-! ## Every store the budgeted settler decides, the settler with no budget decides -/

/-- The older-unknown family with no budget decides a store exactly when the in-place solver, driven by its rank,
decides its extraction. -/
theorem olderRankFamily_decisive_iff {Δ : Context setting.R} (I : EquationStore (TotalTerm Δ)) :
    (olderRankFamily I).Decisive ↔
      (rankFamily setting.levels inPlace (extract setting.levels ExecutableTowerChoices.choices I)).Decisive :=
  Decision.ofEquivalent_decisive (prepareTower I).property _

/-- **Wherever the older-unknown family with some budget decides, the one with no budget decides.** -/
theorem olderRankFamily_of_decisive {fuel : Nat} {Δ : Context setting.R} {I : EquationStore (TotalTerm Δ)}
    (decisive : (olderFamily fuel I).Decisive) : (olderRankFamily I).Decisive := by
  have inner := (olderFamily_decisive_iff fuel I).mp decisive
  refine (olderRankFamily_decisive_iff I).mpr ?_
  rw [rankFamily_of_decisive setting.levels inner]
  exact inner

/-- A solved Miller run with its frame read as families: the Miller family with no budget settles. -/
theorem millerRankFamily_settles {fuel : Nat} {Δ : Context setting.R} {I : EquationStore (TotalTerm Δ)}
    (inside : UnificationWithLevels.TreeFibre.Miller.inMillerGlbB (S := setting) I = true)
    {state : Update setting.levels I} {finished : state.remaining = []}
    (solved : ContextualDependentWorklist.run millerTower I fuel = .solved state finished)
    {v : {view : Fin state.target.arity → List Tower.Head × Tower.Head //
      (∀ j, Ctx.lookup state.target.raw j = famCode (view j).1 (view j).2) ∧
        ∀ j, (∀ p ∈ (view j).1, setting.R.isUniverse p) ∧ setting.R.isUniverse (view j).2}}
    (read : views? state.target = some v) : (millerRankFamily I).isSettled = true := by
  have reached : runRank millerTower I = .solved state finished := by
    rw [← run_eq_runRank millerTower (by rw [solved]; trivial)]
    exact solved
  unfold millerRankFamily
  rw [dif_pos inside]
  split
  · rename_i state' finished' solved'
    rw [reached] at solved'
    cases solved'
    rw [read]
    rfl
  · rename_i absent solved'
    rw [reached] at solved'
    cases solved'
  · rename_i stuck solved'
    rw [reached] at solved'
    cases solved'
  · rename_i cut solved'
    rw [reached] at solved'
    cases solved'

/-- A refuted Miller run: the Miller family with no budget refutes. -/
theorem millerRankFamily_refutes {fuel : Nat} {Δ : Context setting.R} {I : EquationStore (TotalTerm Δ)}
    (inside : UnificationWithLevels.TreeFibre.Miller.inMillerGlbB (S := setting) I = true)
    {absent : ¬ (frames setting.levels).Solvable I}
    (refuted : ContextualDependentWorklist.run millerTower I fuel = .refuted absent) :
    (millerRankFamily I).isRefuted = true := by
  have reached : runRank millerTower I = .refuted absent := by
    rw [← run_eq_runRank millerTower (by rw [refuted]; trivial)]
    exact refuted
  unfold millerRankFamily
  rw [dif_pos inside]
  split
  · rename_i state' finished' solved'
    rw [reached] at solved'
    cases solved'
  · rfl
  · rename_i stuck solved'
    rw [reached] at solved'
    cases solved'
  · rename_i cut solved'
    rw [reached] at solved'
    cases solved'

/-- A family that settles is decisive. -/
theorem decisive_of_isSettled {Δ : Context setting.R} {I : EquationStore (TotalTerm Δ)}
    {d : Decision setting.levels I} (settles : d.isSettled = true) : d.Decisive := by
  cases d
  · trivial
  · trivial
  · cases settles

/-- A family that refutes is decisive. -/
theorem decisive_of_isRefuted {Δ : Context setting.R} {I : EquationStore (TotalTerm Δ)}
    {d : Decision setting.levels I} (refutes : d.isRefuted = true) : d.Decisive := by
  cases d
  · trivial
  · trivial
  · cases refutes

/-- **Wherever the Miller family with some budget settles, the one with no budget settles.** -/
theorem millerRankFamily_settles_of {fuel : Nat} {Δ : Context setting.R} {I : EquationStore (TotalTerm Δ)}
    (settles : (millerFamily fuel I).isSettled = true) : (millerRankFamily I).isSettled = true := by
  unfold millerFamily at settles
  split_ifs at settles with inside
  · split at settles
    · rename_i state finished solved
      split at settles
      · rename_i v read
        exact millerRankFamily_settles inside solved read
      · cases settles
    · cases settles
    · cases settles
    · cases settles
  · cases settles

/-- **Wherever the Miller family with some budget refutes, the one with no budget refutes.** -/
theorem millerRankFamily_refutes_of {fuel : Nat} {Δ : Context setting.R} {I : EquationStore (TotalTerm Δ)}
    (refutes : (millerFamily fuel I).isRefuted = true) : (millerRankFamily I).isRefuted = true := by
  unfold millerFamily at refutes
  split_ifs at refutes with inside
  · split at refutes
    · rename_i state finished solved
      split at refutes
      · cases refutes
      · cases refutes
    · rename_i absent refuted
      exact millerRankFamily_refutes inside refuted
    · cases refutes
    · cases refutes
  · cases refutes

/-- **Wherever the Miller family with some budget decides, the one with no budget decides.** -/
theorem millerRankFamily_of_decisive {fuel : Nat} {Δ : Context setting.R} {I : EquationStore (TotalTerm Δ)}
    (decisive : (millerFamily fuel I).Decisive) : (millerRankFamily I).Decisive := by
  cases h : millerFamily fuel I
  · exact decisive_of_isSettled (millerRankFamily_settles_of (fuel := fuel) (by rw [h]; rfl))
  · exact decisive_of_isRefuted (millerRankFamily_refutes_of (fuel := fuel) (by rw [h]; rfl))
  · rw [h] at decisive
    exact False.elim decisive

/-- **Every store the budgeted settler decides, the settler with no budget decides.** -/
theorem rank_decidedBy_of_all {Δ : Context setting.R} {I : EquationStore (TotalTerm Δ)}
    (decided : DecidedBy setting.levels allFamilies I) : DecidedBy setting.levels rankFamilies I := by
  obtain ⟨F, member, decisive⟩ := decided
  unfold allFamilies at member
  rcases List.mem_append.mp member with older | miller
  · unfold olderFamilies at older
    rcases List.mem_append.mp older with tower | older
    · unfold towerFamilies at tower
      obtain rfl := List.mem_singleton.mp tower
      refine ⟨stepRankFamily, List.mem_cons_self, ?_⟩
      change (rankFamily setting.levels ContextualDependentWorklist.Controls.step I).Decisive
      rw [rankFamily_of_decisive setting.levels decisive]
      exact decisive
    · obtain rfl := List.mem_singleton.mp older
      exact ⟨olderRankFamily, List.mem_cons_of_mem _ List.mem_cons_self, olderRankFamily_of_decisive decisive⟩
  · obtain rfl := List.mem_singleton.mp miller
    exact ⟨millerRankFamily, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
      millerRankFamily_of_decisive decisive⟩

/-! ## Agreement with the semantic settler -/

/-- **On the union of its decided fragments the settler with no budget agrees with the semantic settler**: both settle
exactly the solvable stores, along answers inverse to each other up to agreement. -/
theorem rank_agrees_ideal {Δ : Context setting.R} {I : EquationStore (TotalTerm Δ)}
    (decided : DecidedBy setting.levels rankFamilies I) :
    ((∃ (M : Context setting.R) (σ : M ⟶ Δ) (initial : InitialSolution (frames setting.levels) I σ),
        rankSettler I = .settled M σ initial) ↔ (frames setting.levels).Solvable I) ∧
      ((∃ (M : Context setting.R) (σ : M ⟶ Δ) (initial : InitialSolution (frames setting.levels) I σ),
        Settler.ideal setting.levels I = .settled M σ initial) ↔ (frames setting.levels).Solvable I) ∧
      ∀ (M M' : Context setting.R) (σ : M ⟶ Δ) (σ' : M' ⟶ Δ)
        (initial : InitialSolution (frames setting.levels) I σ)
        (initial' : InitialSolution (frames setting.levels) I σ'),
        rankSettler I = .settled M σ initial → Settler.ideal setting.levels I = .settled M' σ' initial' →
        ∃ (g : M ⟶ M') (g' : M' ⟶ M), Agree (frames setting.levels) σ (g ≫ σ') ∧
          Agree (frames setting.levels) σ' (g' ≫ σ) ∧ Agree (frames setting.levels) (g ≫ g') (𝟙 M) ∧
          Agree (frames setting.levels) (g' ≫ g) (𝟙 M') :=
  ofFamilies_agrees_ideal setting.levels decided

/-- **The converting and templating steps with the settler with no budget admit what the semantic settler's admit**,
on the union of its decided fragments. -/
theorem rank_steps_iff_ideal {s : State setting.R Nat} {f : Firing setting.levels s}
    (decided : DecidedBy setting.levels rankFamilies f.information) :
    ((convertingStep setting.levels Nat rankSettler).Admits f ↔
        (convertingStep setting.levels Nat (Settler.ideal setting.levels)).Admits f) ∧
      ((templatingStep setting.levels Nat rankSettler).Admits f ↔
        (templatingStep setting.levels Nat (Settler.ideal setting.levels)).Admits f) :=
  ⟨ofFamilies_converting_iff_ideal setting.levels rankFamilies decided,
    ofFamilies_templating_iff_ideal setting.levels rankFamilies decided⟩

/-- **Wherever the budgeted settler decides, the settler with no budget decides and agrees with the semantic
settler.** -/
theorem rank_steps_iff_ideal_of_all {s : State setting.R Nat} {f : Firing setting.levels s}
    (decided : DecidedBy setting.levels allFamilies f.information) :
    ((convertingStep setting.levels Nat rankSettler).Admits f ↔
        (convertingStep setting.levels Nat (Settler.ideal setting.levels)).Admits f) ∧
      ((templatingStep setting.levels Nat rankSettler).Admits f ↔
        (templatingStep setting.levels Nat (Settler.ideal setting.levels)).Admits f) :=
  rank_steps_iff_ideal (rank_decidedBy_of_all decided)

end RankSettler

end NativeTypesOnTheStep

#print axioms NativeTypesOnTheStep.decisionOf
#print axioms NativeTypesOnTheStep.driverFamily_eq
#print axioms NativeTypesOnTheStep.rankFamily
#print axioms NativeTypesOnTheStep.finished_of_decisive
#print axioms NativeTypesOnTheStep.rankFamily_of_decisive
#print axioms NativeTypesOnTheStep.rankFamily_eventually
#print axioms NativeTypesOnTheStep.RankSettler.stepRankFamily
#print axioms NativeTypesOnTheStep.RankSettler.olderRankFamily
#print axioms NativeTypesOnTheStep.RankSettler.millerRankFamily
#print axioms NativeTypesOnTheStep.RankSettler.mixedRankFamily
#print axioms NativeTypesOnTheStep.RankSettler.rankSettler
#print axioms NativeTypesOnTheStep.RankSettler.olderRankFamily_decisive_iff
#print axioms NativeTypesOnTheStep.RankSettler.olderRankFamily_of_decisive
#print axioms NativeTypesOnTheStep.RankSettler.millerRankFamily_settles
#print axioms NativeTypesOnTheStep.RankSettler.millerRankFamily_refutes
#print axioms NativeTypesOnTheStep.RankSettler.millerRankFamily_settles_of
#print axioms NativeTypesOnTheStep.RankSettler.millerRankFamily_refutes_of
#print axioms NativeTypesOnTheStep.RankSettler.millerRankFamily_of_decisive
#print axioms NativeTypesOnTheStep.RankSettler.rank_decidedBy_of_all
#print axioms NativeTypesOnTheStep.RankSettler.rank_agrees_ideal
#print axioms NativeTypesOnTheStep.RankSettler.rank_steps_iff_ideal
#print axioms NativeTypesOnTheStep.RankSettler.rank_steps_iff_ideal_of_all

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
