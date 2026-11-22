import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainRule
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.UnionControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FlexRigidGlbControls

/-!
# Controls: unknowns at codomain positions, in the tree's tower

* **An unknown only at a codomain** (`cod_*`): over `X : U1, Y : U2`, the equation `X ≐ Π (_ : U0). Y` at `U2`. The
  first-order arrow codes have heads at their codomains, so the store lies outside the flex–rigid fragment without the
  chain and the fragment of arrow codes, and the solver without the chain is stuck on it. The rule with codomains
  lowers `Y` to the greatest lower bound of `U1` and `U2` and sets `X := Π (_ : U0). Y`, one exact step to the empty
  store: **a principal answer** (`cod_principal`).
* **The over store** (`overCod_principal`): `X ≐ Π (y : Y). Y` over `X : U1, Y : U2` gets a principal answer by the
  same rule.
* **Where the rule's conditions fail** (`codOccurs_absent_fails`, `codMisfitHead_fails`): `X ≐ Π (_ : U0). X` (the
  unknown at its own codomain) and `X ≐ Π (_ : U1). Y` over `X : U1` (a head of `U2`) are not narrowed.
* **The solver with codomains** (`flexCodTowerSolver`, `flexCodTower_decided`), kernel runs: both stores above commit;
  `X ≐ Π (_ : U0). X` is refuted by the occurs check at its codomain (`occ_refuted`); `X ≐ Π (_ : U1). Y` is refuted by
  its misfit head (`mis_refuted`); two chained equations with unknowns at codomains commit at the third round
  (`chainCod_committed`); a store of the fragment without the chain is inside and commits; the union run reads the
  first store into the flex–rigid piece and commits (`cod_piece`, `cod_union`).
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

/-! ## An unknown only at a codomain -/

def codX : TypeOver (empty setting.R) := formIn (empty setting.R) (.head U1) (by decide +kernel)
abbrev ctxCod1 := extend (empty setting.R) codX
def codY : TypeOver ctxCod1 := formIn ctxCod1 (.head U2) (by decide +kernel)
/-- `X : U1, Y : U2`. -/
abbrev ctxCod := extend ctxCod1 codY
def codType : TypeOver ctxCod := formIn ctxCod (.head U2) (by decide +kernel)

/-- `X ≐ Π (_ : U0). Y` at `U2`. -/
def codEquation : Equation (TotalTerm ctxCod) :=
  (termIn ctxCod codType (.var 1) (by decide +kernel),
    termIn ctxCod codType (.pi (.head U0) (.var 1)) (by decide +kernel))

def codStore : EquationStore (TotalTerm ctxCod) := [codEquation]

theorem codRight_code : codEquation.2.2.code = .pi (.head U0) (Presentation.rename wk (.var 0)) := by
  decide +kernel

/-- **The view**: `X : U1` on the left, the code `Π (_ : U0). Y` with `Y` at its codomain. -/
def codView : FlexCod (S := setting) codEquation where
  v := U2
  X := 1
  u := U1
  annotation_left := by decide +kernel
  annotation_right := by decide +kernel
  side_left := by decide +kernel
  declared := by decide +kernel
  universe_u := by decide
  universe_v := by decide
  code := by
    rw [codRight_code]
    exact .pi (.head U0) (.var 0)

/-- The tower's head `U0` is typed by `U1`, which lies below `U1`. -/
theorem U0_typed_below_U1 : ∃ k, setting.R.headTyping U0 k ∧ setting.R.cumulative k U1 := by
  have fit : fitPred (S := setting) ExecutableTowerChoices.choices U1 U0 = true := by decide +kernel
  unfold fitPred at fit
  cases hk : ExecutableTowerChoices.choices.typing U0 with
  | none => rw [hk] at fit; cases fit
  | some k =>
      rw [hk] at fit
      exact ⟨k.1, k.2, of_decide_eq_true fit⟩

theorem ctxCod_universes : AllUniverseDecls ctxCod := allUniverseDecls_of_B (by decide +kernel)

/-- **The conditions of the rule hold**: `X` is absent from the code, its head `U0` is typed below `U1`, every
declaration is a universe, and the misfit `Y : U2` has a greatest lower bound with `U1`. -/
theorem codSolvable : CodSolvable (S := setting) LevelGlb.towerGlb codView where
  absent := by
    change (1 : Fin ctxCod.arity) ∉ codEquation.2.2.code.support
    rw [codRight_code]
    decide +kernel
  heads := by
    intro h member
    change h ∈ codHeads codEquation.2.2.code at member
    rw [codRight_code] at member
    have h0 : h = U0 := by simpa [codHeads, codHeads_rename] using member
    rw [h0]
    exact U0_typed_below_U1
  occurring := fun Y _ => ctxCod_universes Y
  apart := apart_of_universes ctxCod_universes
  meets := by
    intro i _ w hw
    obtain ⟨w', hw', uw'⟩ := ctxCod_universes i
    have same : w = w' := Tm.head.inj (hw.symm.trans hw')
    rw [same]
    exact LevelGlb.towerGlb_total (by decide) uw'

/-- **The answer**: `Y` lowered to the greatest lower bound of `U1` and `U2`, and `X := Π (_ : U0). Y`. -/
noncomputable def codAnswer :=
  codNarrowSolve (S := setting) LevelGlb.towerGlb (fun found => LevelGlb.towerGlb_isGlb found) TowerModel.algebra
    codView codSolvable

/-- **One exact step to the empty store.** -/
theorem cod_exact : Exact (frames setting.levels) codStore codAnswer [] :=
  codNarrowSolve_exact (S := setting) LevelGlb.towerGlb (fun found => LevelGlb.towerGlb_isGlb found) TowerModel.facts
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentNormalCheckingTower.head_typing_unique ContextualDependentExecutableChecking.declared codView
    codSolvable []

/-- **An unknown only at a codomain: a principal answer.** -/
theorem cod_principal : (frames setting.levels).Principal codStore codAnswer :=
  exact_nil_iff_principal.mp cod_exact

/-- **It lies outside the flex–rigid fragments and the fragment of arrow codes.** -/
theorem cod_outside : inFlexRigidGlbB ExecutableTowerChoices.choices codStore = false ∧
    inArrowsB ExecutableTowerChoices.choices codStore = false := by
  decide +kernel

/-- **The flex–rigid solver without the chain is stuck on it.** -/
theorem cod_frGlb_stuck : isStuck (run frGlbTowerSolver codStore 1) = true := by decide +kernel

/-! ## The solver with codomains in the tower -/

/-- The solver of flex–rigid stores with codomains, at the tower's facts and its greatest lower bound. -/
def flexCodTowerSolver : ContextualDependentWorklist.Solver setting.levels :=
  flexCodSolver (S := setting) ExecutableTowerChoices.choices LevelGlb.towerGlb
    (fun found => LevelGlb.towerGlb_isGlb found) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentNormalCheckingTower.head_typing_unique ContextualDependentExecutableChecking.declared

/-- **Decided in the tower.** -/
theorem flexCodTower_decided {Θ : Context setting.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InFlexCod ExecutableTowerChoices.choices original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run flexCodTowerSolver original larger = run flexCodTowerSolver original fuel ∧
        ((∃ state finished, run flexCodTowerSolver original larger = .solved state finished ∧
            (frames setting.levels).Principal original state.answer) ∨
          (∃ absent, run flexCodTowerSolver original larger = .refuted absent)) :=
  flexCod_decided (S := setting) ExecutableTowerChoices.choices LevelGlb.towerGlb
    (fun found => LevelGlb.towerGlb_isGlb found) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentNormalCheckingTower.head_typing_unique ContextualDependentExecutableChecking.declared
    (fun ha hb => LevelGlb.towerGlb_total ha hb) inside

theorem cod_inside : InFlexCod ExecutableTowerChoices.choices codStore := inFlexCod_of_B _ (by decide +kernel)

/-- **The solver commits**: `Y` lowered, `X := Π (_ : U0). Y`. -/
theorem cod_committed : (run flexCodTowerSolver codStore 2).readout = .commit := by decide +kernel

theorem over_insideCod : InFlexCod ExecutableTowerChoices.choices overStore := inFlexCod_of_B _ (by decide +kernel)
theorem over_committedCod : (run flexCodTowerSolver overStore 2).readout = .commit := by decide +kernel

/-- **The union run reads the store into the flex–rigid piece and commits.** -/
theorem cod_piece : towerClassify codStore = some .flexRigid := by decide +kernel
theorem cod_union : (towerUnionRun codStore 2).readout = .commit := by decide +kernel

/-! ### The occurs check at a codomain -/

def occX : TypeOver (empty setting.R) := formIn (empty setting.R) (.head U1) (by decide +kernel)
/-- `X : U1`. -/
abbrev ctxOcc := extend (empty setting.R) occX
def occType : TypeOver ctxOcc := formIn ctxOcc (.head U2) (by decide +kernel)

/-- `X ≐ Π (_ : U0). X` at `U2`. -/
def occStore : EquationStore (TotalTerm ctxOcc) :=
  [(termIn ctxOcc occType (.var 0) (by decide +kernel),
    termIn ctxOcc occType (.pi (.head U0) (.var 1)) (by decide +kernel))]

theorem occ_inside : InFlexCod ExecutableTowerChoices.choices occStore := inFlexCod_of_B _ (by decide +kernel)

/-- **Refuted by the occurs check at the codomain**, with a certificate. -/
theorem occ_refuted : (run flexCodTowerSolver occStore 1).readout = .refuted := by decide +kernel

theorem occ_unsolvable : ¬ (frames setting.levels).Solvable occStore :=
  refuted_of_readout occ_refuted

/-! ### A misfit head -/

def misX : TypeOver (empty setting.R) := formIn (empty setting.R) (.head U1) (by decide +kernel)
abbrev ctxMis1 := extend (empty setting.R) misX
def misY : TypeOver ctxMis1 := formIn ctxMis1 (.head U0) (by decide +kernel)
/-- `X : U1, Y : U0`. -/
abbrev ctxMis := extend ctxMis1 misY
def misType : TypeOver ctxMis := formIn ctxMis (.head U2) (by decide +kernel)

/-- `X ≐ Π (_ : U1). Y` at `U2`: the head `U1` is typed by `U2`, not below `U1`. -/
def misStore : EquationStore (TotalTerm ctxMis) :=
  [(termIn ctxMis misType (.var 1) (by decide +kernel),
    termIn ctxMis misType (.pi (.head U1) (.var 1)) (by decide +kernel))]

theorem mis_inside : InFlexCod ExecutableTowerChoices.choices misStore := inFlexCod_of_B _ (by decide +kernel)

/-- **Refuted by the misfit head**, with a certificate. -/
theorem mis_refuted : (run flexCodTowerSolver misStore 1).readout = .refuted := by decide +kernel

/-! ### Two equations, unknowns at codomains, chained -/

def chainCodX : TypeOver (empty setting.R) := formIn (empty setting.R) (.head U1) (by decide +kernel)
abbrev ctxChainCod1 := extend (empty setting.R) chainCodX
def chainCodY : TypeOver ctxChainCod1 := formIn ctxChainCod1 (.head U2) (by decide +kernel)
abbrev ctxChainCod2 := extend ctxChainCod1 chainCodY
def chainCodZ : TypeOver ctxChainCod2 := formIn ctxChainCod2 (.head U3) (by decide +kernel)
/-- `X : U1, Y : U2, Z : U3`. -/
abbrev ctxChainCod := extend ctxChainCod2 chainCodZ
def chainCodTypeTwo : TypeOver ctxChainCod := formIn ctxChainCod (.head U2) (by decide +kernel)
def chainCodTypeThree : TypeOver ctxChainCod := formIn ctxChainCod (.head U3) (by decide +kernel)

/-- `X ≐ Π (_ : U0). Y` at `U2` and `Y ≐ Π (_ : U0). Z` at `U3`. -/
def chainCodStore : EquationStore (TotalTerm ctxChainCod) :=
  [(termIn ctxChainCod chainCodTypeTwo (.var 2) (by decide +kernel),
      termIn ctxChainCod chainCodTypeTwo (.pi (.head U0) (.var 2)) (by decide +kernel)),
    (termIn ctxChainCod chainCodTypeThree (.var 1) (by decide +kernel),
      termIn ctxChainCod chainCodTypeThree (.pi (.head U0) (.var 1)) (by decide +kernel))]

theorem chainCod_inside : InFlexCod ExecutableTowerChoices.choices chainCodStore :=
  inFlexCod_of_B _ (by decide +kernel)

/-- **The solver commits**: `Y` lowered and `X` solved; the second equation instantiated, `Z` lowered and `Y`
solved. -/
theorem chainCod_committed : (run flexCodTowerSolver chainCodStore 3).readout = .commit := by decide +kernel

theorem chainCod_suspended_before : (run flexCodTowerSolver chainCodStore 2).readout = .suspended := by
  decide +kernel

/-! ### The fragment without the chain lies inside -/

theorem frThree_insideCod : InFlexCod ExecutableTowerChoices.choices frThreeStore :=
  inFlexCod_of_flexRigidGlb frThree_glb_inside

theorem frThree_committedCod : (run flexCodTowerSolver frThreeStore 3).readout = .commit := by decide +kernel

/-! ## The over store -/

theorem overRight_code : overEquation.2.2.code = .pi (.var 0) (Presentation.rename wk (.var 0)) := by decide +kernel

/-- The view of `X ≐ Π (y : Y). Y`: `Y` at the domain and at the codomain. -/
def overViewCod : FlexCod (S := setting) overEquation where
  v := U2
  X := 1
  u := U1
  annotation_left := by decide +kernel
  annotation_right := by decide +kernel
  side_left := by decide +kernel
  declared := by decide +kernel
  universe_u := by decide
  universe_v := by decide
  code := by
    rw [overRight_code]
    exact .pi (.var 0) (.var 0)

theorem ctxOneTwo_universes : AllUniverseDecls ctxOneTwo := allUniverseDecls_of_B (by decide +kernel)

theorem overSolvableCod : CodSolvable (S := setting) LevelGlb.towerGlb overViewCod where
  absent := by
    change (1 : Fin ctxOneTwo.arity) ∉ overEquation.2.2.code.support
    rw [overRight_code]
    decide +kernel
  heads := by
    intro h member
    change h ∈ codHeads overEquation.2.2.code at member
    rw [overRight_code] at member
    simp [codHeads, codHeads_rename] at member
  occurring := fun Y _ => ctxOneTwo_universes Y
  apart := apart_of_universes ctxOneTwo_universes
  meets := by
    intro i _ w hw
    obtain ⟨w', hw', uw'⟩ := ctxOneTwo_universes i
    have same : w = w' := Tm.head.inj (hw.symm.trans hw')
    rw [same]
    exact LevelGlb.towerGlb_total (by decide) uw'

theorem overCod_exact :
    Exact (frames setting.levels) overStore
      (codNarrowSolve (S := setting) LevelGlb.towerGlb (fun found => LevelGlb.towerGlb_isGlb found)
        TowerModel.algebra overViewCod overSolvableCod) [] :=
  codNarrowSolve_exact (S := setting) LevelGlb.towerGlb (fun found => LevelGlb.towerGlb_isGlb found) TowerModel.facts
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentNormalCheckingTower.head_typing_unique ContextualDependentExecutableChecking.declared
    overViewCod overSolvableCod []

/-- **The over store: a principal answer.** -/
theorem overCod_principal :
    (frames setting.levels).Principal overStore
      (codNarrowSolve (S := setting) LevelGlb.towerGlb (fun found => LevelGlb.towerGlb_isGlb found)
        TowerModel.algebra overViewCod overSolvableCod) :=
  exact_nil_iff_principal.mp overCod_exact

theorem over_outside_flexRigidGlb : inFlexRigidGlbB ExecutableTowerChoices.choices overStore = false := by
  decide +kernel

/-! ## Where the rule's conditions fail -/

/-- `X ≐ Π (_ : U0). X`: `X` at its own codomain; the rule's condition that `X` be absent fails. -/
theorem codOccurs_absent_fails :
    (1 : Fin 2) ∈ (Tm.pi (.head U0) (Presentation.rename wk (Tm.var (1 : Fin 2))) : Tm Tower.Head 2).support := by
  decide +kernel

/-- `X ≐ Π (_ : U1). Y` over `X : U1`: the head `U1` is typed by `U2`, which does not lie below `U1`. -/
theorem codMisfitHead_fails : ∀ k, setting.R.headTyping U1 k → ¬ setting.R.cumulative k U1 := by
  intro k typing below
  have fit : fitPred (S := setting) ExecutableTowerChoices.choices U1 U1 = false := by decide +kernel
  unfold fitPred at fit
  cases hk : ExecutableTowerChoices.choices.typing U1 with
  | none => rw [hk] at fit; exact absurd hk (by decide +kernel)
  | some k' =>
      rw [hk] at fit
      have fit' : decide (setting.R.cumulative k'.1 U1) = false := fit
      have same : k = k'.1 := ContextualDependentNormalCheckingTower.head_typing_unique typing k'.2
      rw [same] at below
      exact absurd (decide_eq_true below) (by rw [fit']; decide)

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
