import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainInitial
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainArrowsControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbJoinInitialControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainArrowsInitial
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.UnionInitial

/-!
# Controls for initial solutions of answers with codomains, in the tree's tower

* **Committed runs have initial solutions** (`codA_initial`, `overA_initial`, `chainCodA_initial`): the stores with an
  unknown at a codomain, over telescopes of universes; and for the solver of arrow codes with codomains, unknowns at
  codomains on both sides (`decA_initial`), first-order decomposition (`decomposeA_initial`), and unknowns at
  incomparable universes (`frLevelA_initial`).
* **Untrimmed, the answer is principal and not initial** (`codAnswer_not_initial`): after `X := Π (_ : U0). Y` the
  telescope still declares `X : U1`; the identity and the merge `X, Y := Y` agree on the answer, and differ at `X`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

namespace Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternFiring.Controls ContextualDependentSweep.Witnesses

/-- A committed run of the flex–rigid solver with codomains, over a telescope of universe families, has an initial
solution. -/
theorem initial_of_commitCod {Θ : Context setting.R} {original : EquationStore (TotalTerm Θ)} {fuel : Nat}
    (inside : InFlexCod ExecutableTowerChoices.choices original) (families : Miller.Families Θ)
    (committed : (run flexCodTowerSolver original fuel).readout = .commit) :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ Θ), InitialSolution (frames setting.levels) original answer := by
  cases outcome : run flexCodTowerSolver original fuel with
  | solved state finished =>
      exact flexCod_solved_initial (S := setting) ExecutableTowerChoices.choices LevelGlb.towerGlb
        (fun found => LevelGlb.towerGlb_isGlb found) TowerModel.facts TowerModel.roots TowerModel.heads
        TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
        ContextualDependentNormalCheckingTower.head_typing_unique ContextualDependentExecutableChecking.declared
        Miller.Controls.towerInh inside families outcome
  | stuck _ => rw [outcome] at committed; cases committed
  | refuted _ => rw [outcome] at committed; cases committed
  | cutoff _ => rw [outcome] at committed; cases committed

/-! ## Committed runs have initial solutions -/

theorem codA_initial :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxCod), InitialSolution (frames setting.levels) codStore answer :=
  initial_of_commitCod cod_inside (families_of_universes ctxCod_universes) cod_committed

theorem overA_initial :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxOneTwo), InitialSolution (frames setting.levels) overStore answer :=
  initial_of_commitCod over_insideCod (families_of_universes ctxOneTwo_universes) over_committedCod

theorem ctxChainCod_universes : AllUniverseDecls ctxChainCod := allUniverseDecls_of_B (by decide +kernel)

theorem chainCodA_initial :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxChainCod),
      InitialSolution (frames setting.levels) chainCodStore answer :=
  initial_of_commitCod chainCod_inside (families_of_universes ctxChainCod_universes) chainCod_committed

/-- A committed run of the solver of arrow codes with codomains, over a telescope of universe families, has an initial
solution. -/
theorem initial_of_commitArrowCod {Θ : Context setting.R} {original : EquationStore (TotalTerm Θ)} {fuel : Nat}
    (inside : InArrowsCod ExecutableTowerChoices.choices original) (families : Miller.Families Θ)
    (committed : (run arrowCodTowerSolver original fuel).readout = .commit) :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ Θ), InitialSolution (frames setting.levels) original answer := by
  cases outcome : run arrowCodTowerSolver original fuel with
  | solved state finished =>
      exact arrowsCod_solved_initial (S := setting) ExecutableTowerChoices.choices LevelGlb.towerGlb
        (fun found => LevelGlb.towerGlb_isGlb found) TowerModel.facts TowerModel.roots TowerModel.heads
        TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
        ContextualDependentNormalCheckingTower.head_typing_unique ContextualDependentExecutableChecking.declared
        ContextualDependentIntersectionGeneral.DeadControls.tower_strengthening Miller.Controls.towerInh inside
        families outcome
  | stuck _ => rw [outcome] at committed; cases committed
  | refuted _ => rw [outcome] at committed; cases committed
  | cutoff _ => rw [outcome] at committed; cases committed

theorem ctxDec_universes : AllUniverseDecls ctxDec := allUniverseDecls_of_B (by decide +kernel)
theorem ctxZeroOne_universes : AllUniverseDecls ctxZeroOne := allUniverseDecls_of_B (by decide +kernel)
theorem ctxUab_universes : AllUniverseDecls ctxUab := allUniverseDecls_of_B (by decide +kernel)

/-- **Unknowns at codomains on both sides**: the decomposed store has an initial solution. -/
theorem decA_initial :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxDec), InitialSolution (frames setting.levels) decStore answer :=
  initial_of_commitArrowCod dec_insideA (families_of_universes ctxDec_universes) dec_committedA

theorem decomposeA_initial :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxZeroOne),
      InitialSolution (frames setting.levels) decomposeStore answer :=
  initial_of_commitArrowCod decomposeA_inside (families_of_universes ctxZeroOne_universes) decomposeA_committed

/-- **Incomparable declared universes**: `X ≐ Y` over `X : U_a, Y : U_b` has an initial solution. -/
theorem frLevelA_initial :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxUab), InitialSolution (frames setting.levels) frLevelStore answer :=
  initial_of_commitArrowCod frLevelA_inside (families_of_universes ctxUab_universes) frLevelA_committed

/-- **The union in the tower**: every solvable store the tower's classifier reads into a piece, over a telescope of
universe families, has an initial solution. -/
theorem towerUnion_initial {Θ : Context setting.R} {original : EquationStore (TotalTerm Θ)} {k : Piece}
    (picked : towerClassify original = some k) (families : Miller.Families Θ)
    (solvable : (frames setting.levels).Solvable original) :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ Θ), InitialSolution (frames setting.levels) original answer :=
  union_initial (S := setting) ExecutableTowerChoices.choices TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes Miller.Controls.towerInh
    ContextualDependentNormalCheckingTower.head_typing_unique ContextualDependentExecutableChecking.declared
    ContextualDependentIntersectionGeneral.DeadControls.tower_strengthening towerJoin towerJoin_sound LevelGlb.towerGlb
    (fun found => LevelGlb.towerGlb_isGlb found) towerJoin_total (fun ha hb => LevelGlb.towerGlb_total ha hb)
    ⟨k, towerClassify_sound picked⟩ families solvable

/-- **The decomposed store through the union**: read into the piece of arrow codes, solvable, initial. -/
theorem decUnion_initial :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxDec), InitialSolution (frames setting.levels) decStore answer :=
  towerUnion_initial dec_piece (families_of_universes ctxDec_universes) dec_solvable

/-! ## Untrimmed, the answer is not initial -/

/-- The telescope after the step: `X : U1` still declared, `Y` lowered to `U1`. -/
noncomputable abbrev codTarget' : Context setting.R :=
  codNarrowed (S := setting) LevelGlb.towerGlb (fun found => LevelGlb.towerGlb_isGlb found) codView

def codTargetX : Fin codTarget'.arity := ⟨1, by show 1 < 2; decide⟩
def codTargetY : Fin codTarget'.arity := ⟨0, by show 0 < 2; decide⟩

/-- The greatest lower bound of `U1` and `U2` in the tower, as computed. -/
abbrev Ulow : Tower.Head := .sort (.const 1)

theorem codTarget_lookupX : Ctx.lookup codTarget'.raw codTargetX = .head U1 := by decide +kernel
theorem codTarget_lookupY : Ctx.lookup codTarget'.raw codTargetY = .head Ulow := by decide +kernel
theorem Ulow_below : setting.R.cumulative Ulow U1 := by decide +kernel
theorem codTarget_cases : ∀ i : Fin codTarget'.arity, i = codTargetY ∨ i = codTargetX := by decide

/-- `X := Y`, `Y := Y`, on the telescope after the step. -/
noncomputable def codMerge : codTarget' ⟶ codTarget' where
  substitution := fun _ => .var codTargetY
  typed := by
    intro i
    have typed := Derivable.var (R := setting.R) (Γ := codTarget'.raw) codTargetY
    rw [codTarget_lookupY] at typed
    change Typed setting.R codTarget'.raw (.var codTargetY) (Presentation.subst _ (Ctx.lookup codTarget'.raw i))
    rcases codTarget_cases i with rfl | rfl
    · rw [codTarget_lookupY]
      exact typed
    · rw [codTarget_lookupX]
      exact Derivable.cumul typed Ulow_below

/-- **The merge fixes the answer**: the answer's image mentions `Y` only. -/
theorem codMerge_answer :
    ∀ i : Fin ctxCod.arity, Presentation.subst codMerge.substitution (codAnswer.substitution i) =
      codAnswer.substitution i := by
  decide +kernel

theorem codMerge_agrees (t : TotalTerm ctxCod) :
    (frames setting.levels).E
      ((frames setting.levels).act codMerge ((frames setting.levels).act codAnswer t))
      ((frames setting.levels).act codAnswer t) := by
  have codes : ∀ code : Tm Tower.Head ctxCod.arity,
      Presentation.subst codMerge.substitution (Presentation.subst codAnswer.substitution code) =
        Presentation.subst codAnswer.substitution code := by
    intro code
    rw [subst_comp]
    congr 1
    funext i
    exact codMerge_answer i
  refine ⟨?_, ?_⟩
  · change TypeEq setting.R codTarget'.raw
      (Presentation.subst codMerge.substitution (Presentation.subst codAnswer.substitution t.1.code))
      (Presentation.subst codAnswer.substitution t.1.code)
    rw [codes]
    exact ⟨t.1.level, t.1.universeWitness, .refl (t.1.formed.substitute codAnswer.typed)⟩
  · change Equal setting.R codTarget'.raw
      (Presentation.subst codMerge.substitution (Presentation.subst codAnswer.substitution t.2.code))
      (Presentation.subst codAnswer.substitution t.2.code)
      (Presentation.subst codMerge.substitution (Presentation.subst codAnswer.substitution t.1.code))
    rw [codes, codes]
    exact .refl (t.2.typed.substitute codAnswer.typed)

/-- **Untrimmed, the principal answer is not initial**: `X` stays declared and is a free choice of every factor. -/
theorem codAnswer_not_initial : ¬ InitialSolution (frames setting.levels) codStore codAnswer := by
  intro initial
  have agreeId : Agree (frames setting.levels) codAnswer ((frames setting.levels).comp (𝟙 codTarget') codAnswer) :=
    agree_id_comp (X := frames setting.levels) codAnswer
  have agreeMerge : Agree (frames setting.levels) codAnswer ((frames setting.levels).comp codMerge codAnswer) := by
    intro t
    rw [(frames setting.levels).act_comp]
    exact ((frames setting.levels).equivalence _).symm (codMerge_agrees t)
  have both := initial.unique codTarget' codAnswer (𝟙 codTarget') codMerge agreeId agreeMerge
  have atX := (both (unknownTerm codTarget' codTargetX)).2
  change Equal setting.R codTarget'.raw (Presentation.subst ids (.var codTargetX)) (.var codTargetY)
    (Presentation.subst ids (Ctx.lookup codTarget'.raw codTargetX)) at atX
  rw [subst_ids, subst_ids] at atX
  exact Miller.var_ne_var ContextualDependentPiSpine.Controls.rigid TowerModel.complete codTarget'.formed
    (by decide) atX

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
