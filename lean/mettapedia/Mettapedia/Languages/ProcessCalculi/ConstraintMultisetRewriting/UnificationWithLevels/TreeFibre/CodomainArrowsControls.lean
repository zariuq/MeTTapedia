import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainArrows

/-!
# Controls for equations between arrow codes with codomains, in the tree's tower

The solver at the tower's facts, its greatest lower bound and its strengthening of typed equality
(`arrowCodTowerSolver`, `arrowCodTower_decided`); memberships and runs evaluated by the kernel.

* **Unknowns at codomains on both sides** (`dec_*`): `Π (_ : U0). X ≐ Π (_ : U0). Y` over `X Y : U0` decomposes into
  `U0 ≐ U0` and `X ≐ Y`: a principal answer.
* **The first-order fragment, its chain dropped**: the stores of first-order arrow codes commit (`decomposeA_*`,
  `twiceA_*`, `orientA_*`); so does the equation between two unknowns at incomparable universes, outside the
  first-order fragment for its chain (`frLevelA_*`: `Y` lowered to the greatest lower bound).
* **The flex–rigid stores with codomains** commit (`codA_*`, `overA_*`, `chainCodA_*`).
* **Refutations**: the occurs check at a codomain, a misfit head, two clashing heads, a head against a Π type, two Π
  types whose codomains clash after decomposition, and two Π types whose domains clash
  (`decClash_refuted`: `Π (_ : U0). X ≐ Π (_ : U1). Y`).
* **The telescope**: only the unknowns met must be declared at universes, and no declaration may mention them; the
  equation over a telescope of families is inside and commits (`blendArrow_insideA`, `blendArrow_committedA`).
* **Just outside, and principal** (the boundaries are the rule's, not necessities): a dependent Π type
  (`dep_outsideA`, `dep_stuckA`, `dep_principal`: `X ≐ Π (y : U0). y`, `X := Π (y : U0). y`), and a declaration that
  mentions the unknown met (`dd_outsideA`, `dd_piece`, `dd_principal`: `X ≐ Π (_ : U0). U0` over `X : U1, y : X`, answered
  over `y' : Π (_ : U0). U0` with `X := Π (_ : U0). U0, y := y'`: the declaration of `y` instantiated, which the
  rule's target, the narrowed telescope, does not do).
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

/-- The solver of equations between arrow codes with codomains, at the tower's facts. -/
def arrowCodTowerSolver : ContextualDependentWorklist.Solver setting.levels :=
  arrowCodSolver (S := setting) ExecutableTowerChoices.choices LevelGlb.towerGlb
    (fun found => LevelGlb.towerGlb_isGlb found) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentNormalCheckingTower.head_typing_unique ContextualDependentExecutableChecking.declared
    ContextualDependentIntersectionGeneral.DeadControls.tower_strengthening

/-- **Decided in the tower.** -/
theorem arrowCodTower_decided {Θ : Context setting.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InArrowsCod ExecutableTowerChoices.choices original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run arrowCodTowerSolver original larger = run arrowCodTowerSolver original fuel ∧
        ((∃ state finished, run arrowCodTowerSolver original larger = .solved state finished ∧
            (frames setting.levels).Principal original state.answer) ∨
          (∃ absent, run arrowCodTowerSolver original larger = .refuted absent)) :=
  arrowsCod_decided (S := setting) ExecutableTowerChoices.choices LevelGlb.towerGlb
    (fun found => LevelGlb.towerGlb_isGlb found) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentNormalCheckingTower.head_typing_unique ContextualDependentExecutableChecking.declared
    ContextualDependentIntersectionGeneral.DeadControls.tower_strengthening
    (fun ha hb => LevelGlb.towerGlb_total ha hb) inside

/-! ## Unknowns at codomains on both sides -/

theorem dec_insideA : InArrowsCod ExecutableTowerChoices.choices decStore := inArrowsCod_of_B _ (by decide +kernel)

/-- **The solver commits**: decomposition into `U0 ≐ U0` and `X ≐ Y`, deletion, `X := Y`. -/
theorem dec_committedA : (run arrowCodTowerSolver decStore 4).readout = .commit := by decide +kernel

theorem dec_suspendedA : (run arrowCodTowerSolver decStore 3).readout = .suspended := by decide +kernel

theorem dec_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxDec), (frames setting.levels).Principal decStore answer :=
  principal_of_commit dec_committedA

/-! ## The first-order fragment, its chain dropped -/

theorem decomposeA_inside : InArrowsCod ExecutableTowerChoices.choices decomposeStore :=
  inArrowsCod_of_arrows decompose_inside

theorem decomposeA_committed : (run arrowCodTowerSolver decomposeStore 4).readout = .commit := by decide +kernel

theorem twiceA_inside : InArrowsCod ExecutableTowerChoices.choices frTwiceStore := inArrowsCod_of_arrows twiceArrow_inside

/-- `X := Π (_ : Y). U0`; the Π types decompose into `Y ≐ Z` and `U0 ≐ U0`; `Y := Z`; deletion. -/
theorem twiceA_committed : (run arrowCodTowerSolver frTwiceStore 5).readout = .commit := by decide +kernel

theorem orientA_inside : InArrowsCod ExecutableTowerChoices.choices orientStore := inArrowsCod_of_arrows orient_inside

theorem orientA_committed : (run arrowCodTowerSolver orientStore 2).readout = .commit := by decide +kernel

/-- **Incomparable declared universes**: `X ≐ Y` over `X : U_a, Y : U_b` lies outside the first-order fragment of arrow
codes (its chain), and inside this one. -/
theorem frLevelA_outside_first : inArrowsB ExecutableTowerChoices.choices frLevelStore = false := by decide +kernel

theorem frLevelA_inside : InArrowsCod ExecutableTowerChoices.choices frLevelStore :=
  inArrowsCod_of_B _ (by decide +kernel)

/-- **The solver commits**: `Y` lowered to the greatest lower bound of `U_a` and `U_b`, `X := Y`. -/
theorem frLevelA_committed : (run arrowCodTowerSolver frLevelStore 2).readout = .commit := by decide +kernel

theorem frLevelA_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxUab), (frames setting.levels).Principal frLevelStore answer :=
  principal_of_commit frLevelA_committed

/-! ## The flex–rigid stores with codomains -/

theorem codA_inside : InArrowsCod ExecutableTowerChoices.choices codStore := inArrowsCod_of_flexCod cod_inside
theorem codA_committed : (run arrowCodTowerSolver codStore 2).readout = .commit := by decide +kernel

theorem overA_inside : InArrowsCod ExecutableTowerChoices.choices overStore := inArrowsCod_of_flexCod over_insideCod
theorem overA_committed : (run arrowCodTowerSolver overStore 2).readout = .commit := by decide +kernel

theorem chainCodA_inside : InArrowsCod ExecutableTowerChoices.choices chainCodStore :=
  inArrowsCod_of_flexCod chainCod_inside
theorem chainCodA_committed : (run arrowCodTowerSolver chainCodStore 3).readout = .commit := by decide +kernel

/-! ## Refutations -/

theorem occA_refuted : (run arrowCodTowerSolver occStore 1).readout = .refuted := by decide +kernel
theorem misA_refuted : (run arrowCodTowerSolver misStore 1).readout = .refuted := by decide +kernel
theorem headClashA_refuted : (run arrowCodTowerSolver headClashStore 1).readout = .refuted := by decide +kernel
theorem piHeadA_refuted : (run arrowCodTowerSolver piHeadStore 1).readout = .refuted := by decide +kernel

/-- `Π (_ : Y). U0 ≐ Π (_ : Y). U1`: decomposition, `Y ≐ Y` deleted, `U0 ≐ U1` refuted. -/
theorem codomainClashA_refuted : (run arrowCodTowerSolver codomainClashStore 3).readout = .refuted := by
  decide +kernel

/-- `Π (_ : U0). X ≐ Π (_ : U1). Y` at `U2` over `X Y : U0`. -/
def decClashType : TypeOver ctxDec := formIn ctxDec (.head U2) (by decide +kernel)

def decClashStore : EquationStore (TotalTerm ctxDec) :=
  [(termIn ctxDec decClashType (.pi (.head U0) (.var 2)) (by decide +kernel),
    termIn ctxDec decClashType (.pi (.head U1) (.var 1)) (by decide +kernel))]

theorem decClash_inside : InArrowsCod ExecutableTowerChoices.choices decClashStore :=
  inArrowsCod_of_B _ (by decide +kernel)

/-- **Refuted after decomposition**: the domains `U0 ≐ U1` clash. -/
theorem decClash_refuted : (run arrowCodTowerSolver decClashStore 2).readout = .refuted := by decide +kernel

theorem decClash_unsolvable : ¬ (frames setting.levels).Solvable decClashStore :=
  refuted_of_readout decClash_refuted

/-! ## Just outside -/

/-- **A dependent Π type**: the codomain uses the argument; outside the fragment, and the solver is stuck. -/
theorem dep_outsideA : inArrowsCodB ExecutableTowerChoices.choices depStore = false := by decide +kernel
theorem dep_stuckA : isStuck (run arrowCodTowerSolver depStore 1) = true := by decide +kernel

/-- The morphism into the empty telescope. -/
def toEmpty (Δ : Context setting.R) : Δ ⟶ empty setting.R where
  substitution := fun i => Fin.elim0 i
  typed := fun i => Fin.elim0 i

/-- **The boundary is not a necessity**: the store with a dependent Π type has a principal answer,
`X := Π (y : U0). y`. -/
theorem dep_principal : (frames setting.levels).Principal depStore depSolution := by
  refine ⟨models_by depSolution depEquation.1.2 depEquation.2.2 (by decide +kernel), fun Δ f solved => ⟨toEmpty Δ, ?_⟩⟩
  have eq := ((equivalent_iff setting.levels _ _).mp (solved depEquation List.mem_cons_self)).2
  have factored : homTypedEquality setting.R f (toEmpty Δ ≫ depSolution) := by
    refine ⟨f.typed, fun i => ?_⟩
    obtain ⟨k, hk⟩ := i
    change k < 1 at hk
    obtain rfl : k = 0 := by omega
    change Equal setting.R Δ.raw (Presentation.subst f.substitution (.var 0))
      (Presentation.subst f.substitution (.pi (.head U0) (.var 0))) (Presentation.subst f.substitution (.head U1))
      at eq
    exact eq
  exact act_equal_of_substEq setting.levels factored

/-! ## The telescope: only the unknowns met and the declarations mentioning them matter -/

/-- **A telescope with families**: `Z ≐ Π (_ : U0). U0` over `X Y : U0 → U0, Z : U1` is inside: the families are
neither met nor mentioned. -/
theorem blendArrow_insideA : InArrowsCod ExecutableTowerChoices.choices [blendArrow] :=
  inArrowsCod_of_B _ (by decide +kernel)

theorem blendArrow_committedA : (run arrowCodTowerSolver [blendArrow] 2).readout = .commit := by decide +kernel

def ddX : TypeOver (empty setting.R) := formIn (empty setting.R) (.head U1) (by decide +kernel)
abbrev ctxDd1 := extend (empty setting.R) ddX
def ddY : TypeOver ctxDd1 := formIn ctxDd1 (.var 0) (by decide +kernel)
/-- `X : U1, y : X`: the declaration of `y` mentions `X`. -/
abbrev ctxDd := extend ctxDd1 ddY
def ddType : TypeOver ctxDd := formIn ctxDd (.head U1) (by decide +kernel)

/-- `X ≐ Π (_ : U0). U0` at `U1`, over a declaration that mentions `X`. -/
def ddEquation : Equation (TotalTerm ctxDd) :=
  (termIn ctxDd ddType (.var 1) (by decide +kernel),
    termIn ctxDd ddType (.pi (.head U0) (.head U0)) (by decide +kernel))

def ddStore : EquationStore (TotalTerm ctxDd) := [ddEquation]

/-- **Just outside the condition on declarations**: `y : X` mentions the unknown met, so the store is outside both
pieces of arrow codes and is read into no piece; solving `X` would have to instantiate the declaration of `y`, which
the rule's target, the narrowed telescope, does not do. -/
theorem dd_outsideA : inArrowsCodB ExecutableTowerChoices.choices ddStore = false := by decide +kernel
theorem dd_piece : towerClassify ddStore = none := by decide +kernel

def ddArrow : TypeOver (empty setting.R) := formIn (empty setting.R) (.pi (.head U0) (.head U0)) (by decide +kernel)
/-- `y' : Π (_ : U0). U0`. -/
abbrev ctxDdY := extend (empty setting.R) ddArrow

/-- `X := Π (_ : U0). U0`, from the telescope `y'`. -/
def ddFirst : ctxDdY ⟶ ctxDd1 :=
  toEmpty ctxDdY ≫
    Elimination.instantiate (empty setting.R)
      (termIn (empty setting.R) ddX (.pi (.head U0) (.head U0)) (by decide +kernel)).2

/-- **The answer**: `X := Π (_ : U0). U0`, `y := y'`, the declaration of `y` instantiated. -/
def ddAnswer : ctxDdY ⟶ ctxDd :=
  pair ddFirst (termIn ctxDdY (ddY.reindex ddFirst) (.var 0) (by decide +kernel)).2

/-- **The boundary is not a necessity**: the store just outside the condition on declarations has a principal answer,
whose telescope declares `y` at the instantiated type. -/
theorem dd_principal : (frames setting.levels).Principal ddStore ddAnswer := by
  refine ⟨models_by ddAnswer ddEquation.1.2 ddEquation.2.2 (by decide +kernel), fun Δ f solved => ?_⟩
  have eq := ((equivalent_iff setting.levels _ _).mp (solved ddEquation List.mem_cons_self)).2
  change Equal setting.R Δ.raw (Presentation.subst f.substitution (.var 1))
    (Presentation.subst f.substitution (.pi (.head U0) (.head U0))) (Presentation.subst f.substitution (.head U1))
    at eq
  have tY : Typed setting.R Δ.raw (f.substitution 0) (.pi (.head U0) (.head U0)) := by
    have typed := f.typed 0
    change Typed setting.R Δ.raw (f.substitution 0) (f.substitution 1) at typed
    exact Derivable.conv typed eq (by decide)
  let r : Δ ⟶ ctxDdY := pair (toEmpty Δ) ⟨f.substitution 0, tY⟩
  refine ⟨r, ?_⟩
  have factored : homTypedEquality setting.R f (r ≫ ddAnswer) := by
    refine ⟨f.typed, fun i => ?_⟩
    obtain ⟨k, hk⟩ := i
    change k < 2 at hk
    match k, hk with
    | 0, _ => exact .refl (f.typed 0)
    | 1, _ => exact eq
  exact act_equal_of_substEq setting.levels factored

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
