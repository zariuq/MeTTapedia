import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.UnionSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbJoinNecessity
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerGlbRoundControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ArrowControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FlexRigidGlbControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionGeneralDeadBinderControls

/-!
# Controls: one run for the decided fragments, in the tree's tower

* **The tower's classifier** (`towerClassify`, `towerClassify_sound`): the decided memberships, in the order Miller
  patterns, flex–rigid, arrow codes, the glb join, glb groups. **Decided** (`towerUnion_decided`).
* **One run, every piece** (kernel runs): a Miller permutation with incomparable codomains, a scope escape refuted,
  a decomposition of arrow codes, a flex–rigid equation narrowed to a greatest lower bound, a misfit refuted, and the
  glb join's stores with incomparable codomains and domains, and with a position whose domain exceeds its codomain;
  the flex–rigid piece reads unknowns at codomains (`over_piece`, `over_union`: `X ≐ Π (y : Y). Y`), and the piece of
  arrow codes decomposes unknowns at codomains (`dec_piece`, `dec_union`: `Π (_ : U0). X ≐ Π (_ : U0). Y`).
* **Just outside each boundary**, read into no piece and reported pending:
  * the glb join's condition (`ctrStore`: solvable, no principal answer);
  * the Miller fragment's exact domains (the cross store: solvable, no principal answer);
  * Miller patterns (`twiceStore`, `X y y`);
  * a dependent Π type (`depStore`: `X ≐ Π (y : U0). y`, the codomain using the argument): solvable;
  * **a mixed store** (`blendStore`: a flex–flex equation of families with an equation between arrow codes, over
    disjoint unknowns): solvable and outside every piece. The flex–flex equation alone is a Miller store, and the
    equation between arrow codes alone is a flex–rigid store over the same telescope of families, which commits
    (`blend_parts`, `blendArrow_union`): the boundary is the mixing of two pieces in one store.
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

/-! ## The classifier and the run -/

/-- **The tower's classifier**: the first piece whose decided membership holds. -/
def towerClassify {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) : Option Piece :=
  if Miller.inMillerGlbB (S := setting) problem = true then some .miller
  else if inFlexCodB ExecutableTowerChoices.choices problem = true then some .flexRigid
  else if inArrowsCodB ExecutableTowerChoices.choices problem = true then some .arrows
  else if inGlbJoinFragmentKB problem = true then some .glbJoin
  else if inGlbFragmentB problem = true then some .glbGroups
  else none

theorem towerClassify_sound {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} {k : Piece}
    (picked : towerClassify problem = some k) : InPiece ExecutableTowerChoices.choices k problem := by
  unfold towerClassify at picked
  split_ifs at picked with h1 h2 h3 h4 h5 <;> cases picked
  · exact Miller.inMillerGlb_of_B problem h1
  · exact inFlexCod_of_B _ h2
  · exact inArrowsCod_of_B _ h3
  · exact inGlbJoinFragmentK_of_B h4
  · exact inGlbFragment_of_B h5

/-- **The combined run in the tower.** -/
def towerUnionRun {Θ : Context setting.R} (original : EquationStore (TotalTerm Θ)) (fuel : Nat) :
    Outcome setting.levels original :=
  unionRun (S := setting) ExecutableTowerChoices.choices TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes Miller.Controls.towerInh
    ContextualDependentNormalCheckingTower.head_typing_unique ContextualDependentExecutableChecking.declared
    ContextualDependentIntersectionGeneral.DeadControls.tower_strengthening towerJoin towerJoin_sound LevelGlb.towerGlb
    (fun found => LevelGlb.towerGlb_isGlb found) towerClassify original fuel

/-- **Every store the tower's classifier reads into a piece is decided by the combined run.** -/
theorem towerUnion_decided {Θ : Context setting.R} {original : EquationStore (TotalTerm Θ)} {k : Piece}
    (picked : towerClassify original = some k) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      towerUnionRun original larger = towerUnionRun original fuel ∧
        ((∃ state finished, towerUnionRun original larger = .solved state finished ∧
            (frames setting.levels).Principal original state.answer) ∨
          (∃ absent, towerUnionRun original larger = .refuted absent)) :=
  unionRun_decided (S := setting) ExecutableTowerChoices.choices TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes Miller.Controls.towerInh
    ContextualDependentNormalCheckingTower.head_typing_unique ContextualDependentExecutableChecking.declared
    ContextualDependentIntersectionGeneral.DeadControls.tower_strengthening towerJoin towerJoin_sound LevelGlb.towerGlb
    (fun found => LevelGlb.towerGlb_isGlb found) towerJoin_total (fun ha hb => LevelGlb.towerGlb_total ha hb)
    towerClassify towerClassify_sound picked

/-! ## One run, every piece -/

theorem levelPerm_piece : towerClassify Miller.Controls.levelPermStore = some .miller := by decide +kernel
theorem levelPerm_union : (towerUnionRun Miller.Controls.levelPermStore 3).readout = .commit := by decide +kernel

theorem scope_piece : towerClassify Miller.Controls.scopeStore = some .miller := by decide +kernel
theorem scope_union : (towerUnionRun Miller.Controls.scopeStore 1).readout = .refuted := by decide +kernel

theorem decompose_piece : towerClassify decomposeStore = some .arrows := by decide +kernel
/-- The piece of arrow codes decomposes the codomains too: `X ≐ Y` and `U0 ≐ U0`, one round more than first-order
decomposition. -/
theorem decompose_union : (towerUnionRun decomposeStore 4).readout = .commit := by decide +kernel

theorem frThree_piece : towerClassify frThreeStore = some .flexRigid := by decide +kernel
theorem frThree_union : (towerUnionRun frThreeStore 3).readout = .commit := by decide +kernel

/-- An equation between two unknowns of universe type lies in two pieces; the classifier reads it as a Miller
equation. -/
theorem frLevel_piece : towerClassify frLevelStore = some .miller ∧
    InFlexRigidGlb ExecutableTowerChoices.choices frLevelStore := by
  exact ⟨by decide +kernel, frLevel_glb_inside⟩

theorem frMisfit_union : (towerUnionRun frMisfitStore 1).readout = .refuted := by decide +kernel

theorem twin_piece : towerClassify twinStore = some .glbJoin := by decide +kernel
theorem twin_union : (towerUnionRun twinStore 2).readout = .commit := by decide +kernel

theorem spare_piece : towerClassify spareStore = some .glbJoin := by decide +kernel
theorem spare_union : (towerUnionRun spareStore 2).readout = .commit := by decide +kernel

/-- **An unknown at a codomain**: `X ≐ Π (y : Y). Y` over `X : U1, Y : U2`, now read into the flex–rigid piece. -/
theorem over_piece : towerClassify overStore = some .flexRigid := by decide +kernel
theorem over_union : (towerUnionRun overStore 2).readout = .commit := by decide +kernel

/-! ### The decomposition of arrow codes with unknowns at codomains -/

def decX : TypeOver (empty setting.R) := formIn (empty setting.R) (.head U0) (by decide +kernel)
abbrev ctxDec1 := extend (empty setting.R) decX
def decY : TypeOver ctxDec1 := formIn ctxDec1 (.head U0) (by decide +kernel)
/-- `X Y : U0`. -/
abbrev ctxDec := extend ctxDec1 decY
def decType : TypeOver ctxDec := formIn ctxDec (.head U1) (by decide +kernel)

/-- `Π (_ : U0). X ≐ Π (_ : U0). Y` at `U1`. -/
def decEquation : Equation (TotalTerm ctxDec) :=
  (termIn ctxDec decType (.pi (.head U0) (.var 2)) (by decide +kernel),
    termIn ctxDec decType (.pi (.head U0) (.var 1)) (by decide +kernel))

def decStore : EquationStore (TotalTerm ctxDec) := [decEquation]

/-- `X, Y := G`, the ground type. -/
def decSolution : empty setting.R ⟶ ctxDec :=
  Elimination.instantiate (empty setting.R) (termIn (empty setting.R) decX (.head .legacyGround) (by decide +kernel)).2 ≫
    Elimination.instantiate ctxDec1 (termIn ctxDec1 decY (.head .legacyGround) (by decide +kernel)).2

theorem dec_solvable : (frames setting.levels).Solvable decStore :=
  ⟨_, decSolution, models_by decSolution decEquation.1.2 decEquation.2.2 (by decide +kernel)⟩

/-- **Rigid on both sides, with unknowns at codomains**: read into the piece of arrow codes, which decomposes it into
`U0 ≐ U0` and `X ≐ Y`, deletes the first and solves the second. -/
theorem dec_piece : towerClassify decStore = some .arrows := by decide +kernel
theorem dec_union : (towerUnionRun decStore 4).readout = .commit := by decide +kernel
theorem dec_suspended_before : (towerUnionRun decStore 3).readout = .suspended := by decide +kernel

/-- **Incomparable declared universes**: the equation between two unknowns of universe type is now in three pieces. -/
theorem frLevel_arrows : InArrowsCod ExecutableTowerChoices.choices frLevelStore :=
  inArrowsCod_of_B _ (by decide +kernel)

/-! ## Just outside each boundary -/

/-- **The glb join's condition**: the counterexample store is read into no piece and is pending. -/
theorem ctr_piece : towerClassify ctrStore = none := by decide +kernel
theorem ctr_union : (towerUnionRun ctrStore 3).readout = .suspended := by decide +kernel

/-- **The Miller fragment's exact domains, and the crossing**: the cross store is read into no piece. -/
theorem cross_piece : towerClassify crossStore = none := by decide +kernel
theorem cross_union : (towerUnionRun crossStore 3).readout = .suspended := by decide +kernel

/-- **Miller patterns**: `X y y` is read into no piece. -/
theorem twice_piece : towerClassify Miller.Controls.twiceStore = none := by decide +kernel

/-! ### A dependent Π type -/

def depX : TypeOver (empty setting.R) := formIn (empty setting.R) (.head U1) (by decide +kernel)
/-- `X : U1`. -/
abbrev ctxDep := extend (empty setting.R) depX
def depType : TypeOver ctxDep := formIn ctxDep (.head U1) (by decide +kernel)

/-- `X ≐ Π (y : U0). y` at `U1`: the codomain uses the argument. -/
def depEquation : Equation (TotalTerm ctxDep) :=
  (termIn ctxDep depType (.var 0) (by decide +kernel),
    termIn ctxDep depType (.pi (.head U0) (.var 0)) (by decide +kernel))

def depStore : EquationStore (TotalTerm ctxDep) := [depEquation]

/-- `X := Π (y : U0). y`. -/
def depSolution : empty setting.R ⟶ ctxDep :=
  Elimination.instantiate (empty setting.R)
    (termIn (empty setting.R) depX (.pi (.head U0) (.var 0)) (by decide +kernel)).2

theorem dep_solvable : (frames setting.levels).Solvable depStore :=
  ⟨_, depSolution, models_by depSolution depEquation.1.2 depEquation.2.2 (by decide +kernel)⟩

/-- **A dependent Π type**: read into no piece, pending. -/
theorem dep_piece : towerClassify depStore = none := by decide +kernel
theorem dep_union : (towerUnionRun depStore 2).readout = .suspended := by decide +kernel

/-! ### Arrow codes over a telescope with families -/

def blendX : TypeOver (empty setting.R) := formIn (empty setting.R) (.pi (.head U0) (.head U0)) (by decide +kernel)
abbrev ctxBlend1 := extend (empty setting.R) blendX
def blendY : TypeOver ctxBlend1 := formIn ctxBlend1 (.pi (.head U0) (.head U0)) (by decide +kernel)
abbrev ctxBlend2 := extend ctxBlend1 blendY
def blendZ : TypeOver ctxBlend2 := formIn ctxBlend2 (.head U1) (by decide +kernel)
/-- `X Y : U0 → U0, Z : U1`. -/
abbrev ctxBlend := extend ctxBlend2 blendZ
def blendFamType : TypeOver ctxBlend := formIn ctxBlend (.pi (.head U0) (.head U0)) (by decide +kernel)
def blendUniType : TypeOver ctxBlend := formIn ctxBlend (.head U1) (by decide +kernel)

/-- `λ x. X x ≐ λ x. Y x` at `Π (x : U0). U0`. -/
def blendFlex : Equation (TotalTerm ctxBlend) :=
  (termIn ctxBlend blendFamType (.lam (.app (.var 3) (.var 0))) (by decide +kernel),
    termIn ctxBlend blendFamType (.lam (.app (.var 2) (.var 0))) (by decide +kernel))

/-- `Z ≐ Π (_ : U0). U0` at `U1`. -/
def blendArrow : Equation (TotalTerm ctxBlend) :=
  (termIn ctxBlend blendUniType (.var 0) (by decide +kernel),
    termIn ctxBlend blendUniType (.pi (.head U0) (.head U0)) (by decide +kernel))

def blendStore : EquationStore (TotalTerm ctxBlend) := [blendFlex, blendArrow]

/-- `X, Y := λ x. x`, `Z := Π (_ : U0). U0`. -/
def blendSolution : empty setting.R ⟶ ctxBlend :=
  Elimination.instantiate (empty setting.R) (termIn (empty setting.R) blendX (.lam (.var 0)) (by decide +kernel)).2 ≫
    Elimination.instantiate ctxBlend1 (termIn ctxBlend1 blendY (.lam (.var 0)) (by decide +kernel)).2 ≫
      Elimination.instantiate ctxBlend2 (termIn ctxBlend2 blendZ (.pi (.head U0) (.head U0)) (by decide +kernel)).2

/-- **The store is solvable.** -/
theorem blend_solvable : (frames setting.levels).Solvable blendStore := by
  refine ⟨_, blendSolution, fun e member => ?_⟩
  rcases List.mem_cons.mp member with rfl | member
  · exact models_by blendSolution blendFlex.1.2 blendFlex.2.2 (by decide +kernel) _ List.mem_cons_self
  · rw [List.mem_singleton.mp member]
    exact models_by blendSolution blendArrow.1.2 blendArrow.2.2 (by decide +kernel) _ List.mem_cons_self

/-- **The boundary is the mixing, not the telescope**: the flex–flex equation alone is a Miller store; the equation
between arrow codes alone is in the flex–rigid piece over this telescope of families, since the pieces of arrow codes
ask only the unknowns they meet to be declared at universes, and no declaration to mention them. -/
theorem blend_parts : towerClassify [blendFlex] = some .miller ∧ towerClassify [blendArrow] = some .flexRigid := by
  decide +kernel

/-- **The equation between arrow codes alone commits** over the telescope with families. -/
theorem blendArrow_union : (towerUnionRun [blendArrow] 2).readout = .commit := by decide +kernel

/-- **Together they lie in no piece**, and the combined run is pending: a store mixing two pieces. -/
theorem blend_piece : towerClassify blendStore = none := by decide +kernel
theorem blend_union : (towerUnionRun blendStore 3).readout = .suspended := by decide +kernel

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
