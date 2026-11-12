import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbJoinInitial
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbJoinControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerInitialControls

/-!
# Controls: initial solutions of join answers, in the tree's tower

* **Trimmed, every committed run is initial** (`initial_of_commitGJ`): the stores with incomparable codomains and
  domains (`twin_initial`), with a position whose domain exceeds its codomain (`spare_initial`), with equivalent
  different codomains (`equiv_initial`), and the join-meet solver's stores (`triple_initialGJ`,
  `meetTwist_initialGJ`) have initial solutions.
* **Untrimmed, the join answer is not initial** (`equivJoin_not_initial`): one glb-join step on `X : U0 → U_a`,
  `Y : U0 → U_{max 0 a}` declares `Y` again at `U0 → U_a` and sends `X` and `Y` to `λ x. Y x`; `X` stays declared and is
  mentioned by nothing, so the identity and the morphism sending `X` to `Y` give the same composite with the answer
  and are not equal.
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

/-! ## Trimmed, committed runs are initial -/

/-- **A store of the glb-join fragment on which the solver commits has an initial solution.** -/
theorem initial_of_commitGJ {Θ : Context setting.R} {original : EquationStore (TotalTerm Θ)} {fuel : Nat}
    (inside : InGlbJoinFragmentK original) (committed : (run glbJoinTowerSolver original fuel).readout = .commit) :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ Θ), InitialSolution (frames setting.levels) original answer := by
  cases outcome : run glbJoinTowerSolver original fuel with
  | solved state finished =>
      exact glbJoin_solved_initial TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
        ContextualDependentPiSpine.Controls.rigid TowerModel.complete
        ContextualDependentNormalCheckingTower.head_typing_unique towerJoin towerJoin_sound LevelGlb.towerGlb
        (fun found => LevelGlb.towerGlb_isGlb found) Miller.Controls.towerInh inside outcome
  | stuck _ => rw [outcome] at committed; cases committed
  | refuted _ => rw [outcome] at committed; cases committed
  | cutoff _ => rw [outcome] at committed; cases committed

/-- **Every store of the glb-join fragment has an initial solution in the tower.** -/
theorem glbJoinTower_initial {Θ : Context setting.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InGlbJoinFragmentK original) :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ Θ), InitialSolution (frames setting.levels) original answer :=
  glbJoin_initial TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentNormalCheckingTower.head_typing_unique towerJoin towerJoin_sound LevelGlb.towerGlb
    (fun found => LevelGlb.towerGlb_isGlb found) Miller.Controls.towerInh towerJoin_total
    (fun ha hb => LevelGlb.towerGlb_total ha hb) inside

theorem twin_initial :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxTwin), InitialSolution (frames setting.levels) twinStore answer :=
  initial_of_commitGJ twin_inside twin_committed

theorem spare_initial :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxSpare), InitialSolution (frames setting.levels) spareStore answer :=
  initial_of_commitGJ spare_inside spare_committed

theorem equiv_initial :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxEquiv), InitialSolution (frames setting.levels) equivStore answer :=
  initial_of_commitGJ equiv_inside equiv_committed

theorem triple_initialGJ :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxTriple), InitialSolution (frames setting.levels) tripleStore answer :=
  initial_of_commitGJ triple_insideGJ triple_committedGJ

theorem meetTwist_initialGJ :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxMeetTwist),
      InitialSolution (frames setting.levels) meetTwistStore answer :=
  initial_of_commitGJ meetTwist_insideGJ meetTwist_committedGJ

/-! ## Untrimmed, the join answer is not initial -/

theorem equivAnnotation_right : equivEquation.2.1.code = famCode [U0] U0a := by decide +kernel

/-- **The view**: `X` on the left with the codomain `U_a`, `Y` on the right with `U_{max 0 a}`. -/
def equivViewK : FlexK (S := setting) equivEquation where
  ps := [U0]
  q := U0a
  left := 1
  right := 0
  psl := [U0]
  cl := Ua
  psr := [U0]
  cr := U0a
  annotation_left := equivAnnotation_code
  annotation_right := equivAnnotation_right
  side_left := equivLeft_code
  side_right := equivRight_code
  declared_left := equivX_declared
  declared_right := equivY_declared
  universes := by decide
  universes_left := by decide
  universes_right := by decide
  universe_q := by decide
  universe_cl := by decide
  universe_cr := by decide
  domain_left := .cons (by decide) .nil
  domain_right := .cons (by decide) .nil
  codomain_left := by decide +kernel
  codomain_right := by decide +kernel

theorem equivFamilies : Miller.Families (S := setting) ctxEquiv := by decide +kernel

theorem equivJoins : JoinsK setting.R [U0] [U0] [U0] :=
  .cons (by decide) (isLub_left (S := setting) (by decide) (by decide)) .nil

/-- `U_a` is a greatest lower bound of `U_a` and `U_{max 0 a}`. -/
theorem equivGlb : IsGlb setting.R Ua Ua U0a :=
  ⟨by decide, by decide +kernel, by decide +kernel, fun _ _ below _ => below⟩

theorem equivCross : List.Forall₂ (CrossAt setting.R Ua U0a) [U0] [U0] := .cons (by decide +kernel) .nil

/-- **One glb-join step**: `Y` declared again at `U0 → U_a`, `X, Y := λ x. Y x`; `X` stays declared. -/
noncomputable def equivJoinUpdate : Update setting.levels equivStore :=
  joinRereadKUpdate equivFamilies equivViewK equivJoins equivGlb.1 equivGlb.2.1 equivGlb.2.2.1
    (glbJoinK_forces TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentNormalCheckingTower.head_typing_unique equivViewK equivGlb equivJoins equivCross) []

/-- The telescope after the step: `X Y : U0 → U_a`. -/
noncomputable abbrev equivTarget : Context setting.R := equivJoinUpdate.target

def equivTargetX : Fin equivTarget.arity := ⟨1, by show 1 < 2; decide⟩
def equivTargetY : Fin equivTarget.arity := ⟨0, by show 0 < 2; decide⟩

theorem equivTarget_lookup : ∀ i : Fin equivTarget.arity, Ctx.lookup equivTarget.raw i = famCode [U0] Ua := by
  decide +kernel

/-- **The step solves the store**: nothing remains. -/
theorem equivJoin_remaining : equivJoinUpdate.remaining = [] := rfl

/-- `X := Y`, `Y := Y`, on the telescope after the step. -/
noncomputable def equivMerge : equivTarget ⟶ equivTarget where
  substitution := fun _ => .var equivTargetY
  typed := by
    intro i
    have typed := Derivable.var (R := setting.R) (Γ := equivTarget.raw) equivTargetY
    rw [equivTarget_lookup equivTargetY] at typed
    change Typed setting.R equivTarget.raw (.var equivTargetY) (Presentation.subst _ (Ctx.lookup equivTarget.raw i))
    rw [equivTarget_lookup i, famCode_subst]
    exact typed

/-- **The merge fixes the answer**: the answer's image mentions `Y` only. -/
theorem equivMerge_answer :
    ∀ i : Fin ctxEquiv.arity, Presentation.subst equivMerge.substitution (equivJoinUpdate.answer.substitution i) =
      equivJoinUpdate.answer.substitution i := by
  decide +kernel

theorem equivMerge_agrees (t : TotalTerm ctxEquiv) :
    (frames setting.levels).E
      ((frames setting.levels).act equivMerge ((frames setting.levels).act equivJoinUpdate.answer t))
      ((frames setting.levels).act equivJoinUpdate.answer t) := by
  have codes : ∀ code : Tm Tower.Head ctxEquiv.arity,
      Presentation.subst equivMerge.substitution (Presentation.subst equivJoinUpdate.answer.substitution code) =
        Presentation.subst equivJoinUpdate.answer.substitution code := by
    intro code
    rw [subst_comp]
    congr 1
    funext i
    exact equivMerge_answer i
  refine ⟨?_, ?_⟩
  · change TypeEq setting.R equivTarget.raw
      (Presentation.subst equivMerge.substitution (Presentation.subst equivJoinUpdate.answer.substitution t.1.code))
      (Presentation.subst equivJoinUpdate.answer.substitution t.1.code)
    rw [codes]
    exact ⟨t.1.level, t.1.universeWitness, .refl (t.1.formed.substitute equivJoinUpdate.answer.typed)⟩
  · change Equal setting.R equivTarget.raw
      (Presentation.subst equivMerge.substitution (Presentation.subst equivJoinUpdate.answer.substitution t.2.code))
      (Presentation.subst equivJoinUpdate.answer.substitution t.2.code)
      (Presentation.subst equivMerge.substitution (Presentation.subst equivJoinUpdate.answer.substitution t.1.code))
    rw [codes, codes]
    exact .refl (t.2.typed.substitute equivJoinUpdate.answer.typed)

/-- **The join answer is principal.** -/
theorem equivJoin_principal : (frames setting.levels).Principal equivStore equivJoinUpdate.answer :=
  equivJoinUpdate.completed equivJoin_remaining

/-- **Untrimmed, the join answer is not the initial solution**: `X` stays declared, and the identity and the merge
`X := Y` give the same composite with the answer. -/
theorem equivJoin_not_initial :
    ¬ InitialSolution (frames setting.levels) equivStore equivJoinUpdate.answer := by
  intro initial
  have agreeId : Agree (frames setting.levels) equivJoinUpdate.answer
      ((frames setting.levels).comp (𝟙 equivTarget) equivJoinUpdate.answer) :=
    agree_id_comp (X := frames setting.levels) equivJoinUpdate.answer
  have agreeMerge : Agree (frames setting.levels) equivJoinUpdate.answer
      ((frames setting.levels).comp equivMerge equivJoinUpdate.answer) := by
    intro t
    rw [(frames setting.levels).act_comp]
    exact ((frames setting.levels).equivalence _).symm (equivMerge_agrees t)
  have both := initial.unique equivTarget equivJoinUpdate.answer (𝟙 equivTarget) equivMerge agreeId agreeMerge
  have atX := (both (unknownTerm equivTarget equivTargetX)).2
  change Equal setting.R equivTarget.raw (Presentation.subst ids (.var equivTargetX)) (.var equivTargetY)
    (Presentation.subst ids (Ctx.lookup equivTarget.raw equivTargetX)) at atX
  rw [subst_ids, subst_ids] at atX
  exact Miller.var_ne_var ContextualDependentPiSpine.Controls.rigid TowerModel.complete equivTarget.formed
    (by decide) atX

/-! ## The answer on incomparable codomains and domains -/

theorem twinAnnotation_right : twinEquation.2.1.code = famCode [U0, U0] UabSucc := by decide +kernel

/-- **The view** of `λ x y. X x y ≐ λ x y. Y x y`: `X : U0 → U1 → U_{a+1}`, `Y : U1 → U0 → U_{b+1}`. -/
def twinViewK : FlexK (S := setting) twinEquation where
  ps := [U0, U0]
  q := UabSucc
  left := 1
  right := 0
  psl := [U0, U1]
  cl := Ua1
  psr := [U1, U0]
  cr := UbSucc
  annotation_left := twinAnnotation_code
  annotation_right := twinAnnotation_right
  side_left := twinLeft_code
  side_right := twinRight_code
  declared_left := twinX_declared
  declared_right := twinY_declared
  universes := by decide
  universes_left := by decide
  universes_right := by decide
  universe_q := by decide
  universe_cl := by decide
  universe_cr := by decide
  domain_left := .cons (by decide +kernel) (.cons (by decide +kernel) .nil)
  domain_right := .cons (by decide +kernel) (.cons (by decide +kernel) .nil)
  codomain_left := by decide +kernel
  codomain_right := by decide +kernel

theorem twinFamilies : Miller.Families (S := setting) ctxTwin := by decide +kernel

/-- **The tower's greatest lower bound of `U_{a+1}` and `U_{b+1}`**: the universe of level `1`. -/
theorem twin_glb : LevelGlb.towerGlb Ua1 UbSucc = some (.sort (.const 1)) := by decide +kernel

theorem twinGlb : IsGlb setting.R (.sort (.const 1)) Ua1 UbSucc := LevelGlb.towerGlb_isGlb twin_glb

/-- The least upper bounds of the domains: `U0 ⊔ U1 = U1` and `U1 ⊔ U0 = U1`. -/
theorem twinJoins : JoinsK setting.R [U0, U1] [U1, U0] [U1, U1] :=
  .cons (by decide) (isLub_right (S := setting) (by decide) (by decide))
    (.cons (by decide) (isLub_left (S := setting) (by decide) (by decide)) .nil)

theorem twinCross : List.Forall₂ (CrossAt setting.R Ua1 UbSucc) [U0, U1] [U1, U0] :=
  .cons (by decide +kernel) (.cons (by decide +kernel) .nil)

/-- **One glb-join step** on the store. -/
noncomputable def twinJoinUpdate : Update setting.levels twinStore :=
  joinRereadKUpdate twinFamilies twinViewK twinJoins twinGlb.1 twinGlb.2.1 twinGlb.2.2.1
    (glbJoinK_forces TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentNormalCheckingTower.head_typing_unique twinViewK twinGlb twinJoins twinCross) []

/-- The redeclared unknown `Y` of the telescope after the step. -/
def twinTargetY : Fin twinJoinUpdate.target.arity := ⟨0, by show 0 < 2; decide⟩

/-- **The principal answer**: `Y` declared again at `U1 → U1 → U_1`, and `X, Y := λ x y. Y x y`; nothing remains. -/
theorem twinJoin_answer :
    Ctx.lookup twinJoinUpdate.target.raw twinTargetY = famCode [U1, U1] (.sort (.const 1)) ∧
      twinJoinUpdate.answer.substitution 1 = etaExp 2 (.var twinTargetY) ∧
      twinJoinUpdate.answer.substitution 0 = etaExp 2 (.var twinTargetY) ∧ twinJoinUpdate.remaining = [] :=
  ⟨by decide +kernel, rfl, rfl, rfl⟩

theorem twinJoin_principal : (frames setting.levels).Principal twinStore twinJoinUpdate.answer :=
  twinJoinUpdate.completed rfl

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
