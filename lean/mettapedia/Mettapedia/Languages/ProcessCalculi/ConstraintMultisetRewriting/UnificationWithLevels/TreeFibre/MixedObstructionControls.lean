import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MixedJoinControls

/-!
# Controls: where mixing stops, Miller patterns with glb-join families

Over `X F : U0 → U0 → U0` and `Y : U1 → U0 → U0`:
* `λ x y. F x y ≐ λ x y. X y x`, a Miller equation (a permutation, exact domains), not a family equation;
* `λ x y. X x y ≐ λ x y. Y x y`, a glb-join equation (`Y`'s first domain is not the binder's), not a Miller equation.

Each alone is decided: the Miller store commits under the mixed solver (`mjMiller_committed`), the glb-join store under
the mixed join solver (`mjJoin_committed`). Together the store is solvable (`mj_solvable`) and lies in neither mixed
fragment (`mj_outside_mixed`, `mj_outside_mixedJoin`); both mixed solvers are stuck on it (`mj_mixed_suspended`,
`mj_mixedJoin_suspended`).

**The obstruction, precisely** (`mj_stuck_store`): the Miller round answers `X := λ a b. F b a`. The glb-join equation is
not a Miller equation, so it is instantiated as it is: `λ x y. (λ a b. F b a) x y ≐ λ x y. Y x y`, a β-redex, which is
read neither as a Miller equation nor as a family equation. In the other order the join's answer `X := λ x y. Y' x y` meets
the Miller side `λ x y. X y x` the same way. What the one-rank solvers miss is one rule for flex–flex equations that are
permutations with domains that are not the binders' (a Miller step with the join's widening), and a re-reading that
contracts the redex an answer makes in a side it does not read. The tree's in-place solver, which normalizes the store
before its pattern, prune and exchange rules, decides this store with a principal answer (`mj_inPlace`, `mj_principal`
in `ThroughPhasesControls`).
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

def mjX : TypeOver (empty setting.R) :=
  formIn (empty setting.R) (.pi (.head U0) (.pi (.head U0) (.head U0))) (by decide +kernel)
abbrev ctxMJ1 := extend (empty setting.R) mjX
def mjF : TypeOver ctxMJ1 := formIn ctxMJ1 (.pi (.head U0) (.pi (.head U0) (.head U0))) (by decide +kernel)
abbrev ctxMJ2 := extend ctxMJ1 mjF
def mjY : TypeOver ctxMJ2 := formIn ctxMJ2 (.pi (.head U1) (.pi (.head U0) (.head U0))) (by decide +kernel)
/-- `X F : U0 → U0 → U0, Y : U1 → U0 → U0`. -/
abbrev ctxMJ := extend ctxMJ2 mjY
def mjType : TypeOver ctxMJ := formIn ctxMJ (.pi (.head U0) (.pi (.head U0) (.head U0))) (by decide +kernel)

/-- `λ x y. F x y ≐ λ x y. X y x`. -/
def mjMiller : Equation (TotalTerm ctxMJ) :=
  (termIn ctxMJ mjType (.lam (.lam (.app (.app (.var 3) (.var 1)) (.var 0)))) (by decide +kernel),
    termIn ctxMJ mjType (.lam (.lam (.app (.app (.var 4) (.var 0)) (.var 1)))) (by decide +kernel))

/-- `λ x y. X x y ≐ λ x y. Y x y`. -/
def mjJoin : Equation (TotalTerm ctxMJ) :=
  (termIn ctxMJ mjType (.lam (.lam (.app (.app (.var 4) (.var 1)) (.var 0)))) (by decide +kernel),
    termIn ctxMJ mjType (.lam (.lam (.app (.app (.var 2) (.var 1)) (.var 0)))) (by decide +kernel))

def mjStore : EquationStore (TotalTerm ctxMJ) := [mjMiller, mjJoin]

/-- **Which reader reads which equation.** -/
theorem mj_readers : (Miller.readEq (S := setting) mjMiller).isSome = true ∧
    (readFlexK (S := setting) mjMiller).isSome = false ∧ (Miller.readEq (S := setting) mjJoin).isSome = false ∧
    (readFlexK (S := setting) mjJoin).isSome = true := by decide +kernel

/-- **Each alone is decided.** -/
theorem mjMiller_committed : (run towerMixedSolver [mjMiller] 3).readout = .commit := by decide +kernel
theorem mjJoin_committed : (run towerMixedJoinSolver [mjJoin] 2).readout = .commit := by decide +kernel

/-- `X := λ a b. b`, `F := λ a b. a`, `Y := λ a b. b`. -/
def mjSolution : empty setting.R ⟶ ctxMJ :=
  Elimination.instantiate (empty setting.R) (termIn (empty setting.R) mjX (.lam (.lam (.var 0))) (by decide +kernel)).2 ≫
    Elimination.instantiate ctxMJ1 (termIn ctxMJ1 mjF (.lam (.lam (.var 1))) (by decide +kernel)).2 ≫
      Elimination.instantiate ctxMJ2 (termIn ctxMJ2 mjY (.lam (.lam (.var 0))) (by decide +kernel)).2

/-- **Together, solvable.** -/
theorem mj_solvable : (frames setting.levels).Solvable mjStore := by
  refine ⟨_, mjSolution, fun e member => ?_⟩
  rcases List.mem_cons.mp member with rfl | member
  · exact models_by mjSolution mjMiller.1.2 mjMiller.2.2 (by decide +kernel) _ List.mem_cons_self
  · rw [List.mem_singleton.mp member]
    exact models_by mjSolution mjJoin.1.2 mjJoin.2.2 (by decide +kernel) _ List.mem_cons_self

/-- **Outside the store mixing Miller patterns with arrow codes**: the glb-join equation is neither. -/
theorem mj_outside_mixed : ¬ InMixed ExecutableTowerChoices.choices mjStore := by
  have notArrow : ¬ InArrowsCod ExecutableTowerChoices.choices [mjJoin] := fun inside => by
    have h := Miller.inArrowsCodB_of (S := setting) ExecutableTowerChoices.choices (problem := [mjJoin]) inside
    revert h
    decide +kernel
  have notView : ¬ Nonempty (Miller.EqView (S := setting) mjJoin) := fun ⟨w⟩ => by
    have h := Miller.readEq_isSome_of_view w
    revert h
    decide +kernel
  rintro (arrows | mixed)
  · exact notArrow (Miller.inArrowsCod_iff.mp arrows mjJoin (List.mem_cons_of_mem _ List.mem_cons_self))
  · rcases mixed.each mjJoin (List.mem_cons_of_mem _ List.mem_cons_self) with view | arrow
    · exact notView view
    · exact notArrow arrow

/-- **Outside the store mixing glb-join families with arrow codes**: the Miller equation is neither. -/
theorem mj_outside_mixedJoin : ¬ InMixedJoin ExecutableTowerChoices.choices mjStore := by
  have notArrow : ¬ InArrowsCod ExecutableTowerChoices.choices [mjMiller] := fun inside => by
    have h := Miller.inArrowsCodB_of (S := setting) ExecutableTowerChoices.choices (problem := [mjMiller]) inside
    revert h
    decide +kernel
  have notFamily : ¬ Nonempty (FlexK (S := setting) mjMiller) := fun ⟨v⟩ => by
    have h : (readFlexK (S := setting) mjMiller).isSome = true := by
      rw [readFlexK_complete v]
      rfl
    revert h
    decide +kernel
  rintro (arrows | ⟨_, F, A, perm, inF, inA⟩)
  · exact notArrow (Miller.inArrowsCod_iff.mp arrows mjMiller List.mem_cons_self)
  · rcases List.mem_append.mp (perm.mem_iff.mp (List.mem_cons_self (a := mjMiller))) with inside | arrow
    · exact notFamily (inF.shapes mjMiller inside)
    · exact notArrow (inA mjMiller arrow)

/-- **Both mixed solvers are stuck on it.** -/
theorem mj_mixed_suspended : (run towerMixedSolver mjStore 5).readout = .suspended := by decide +kernel
theorem mj_mixedJoin_suspended : (run towerMixedJoinSolver mjStore 5).readout = .suspended := by decide +kernel

/-- What the mixed solver is stuck on: one equation, read by neither reader. -/
def mjStuckEquation : Bool :=
  match run towerMixedSolver mjStore 5 with
  | .stuck state =>
      match state.remaining with
      | [e] => !(Miller.readEq (S := setting) e).isSome && !(readFlexK (S := setting) e).isSome
      | _ => false
  | _ => false

/-- **The obstruction**: after the Miller answer `X := λ a b. F b a`, one equation remains, and neither the Miller
reader nor the family reader reads it (the instantiated glb-join equation is a β-redex). -/
theorem mj_stuck_store : mjStuckEquation = true := by decide +kernel

/-- The left side of the remaining equation, as computed: `λ x y. (λ a b. F b a) x y`. -/
def mjStuckLeft : Bool :=
  match run towerMixedSolver mjStore 5 with
  | .stuck state =>
      match state.remaining with
      | [e] => decide (e.1.2.code =
          .lam (.lam (.app (.app (.lam (.lam (.app (.app (.var 5) (.var 0)) (.var 1)))) (.var 1)) (.var 0))))
      | _ => false
  | _ => false

/-- **The remaining equation's left side is the β-redex `λ x y. (λ a b. F b a) x y`.** -/
theorem mj_stuck_redex : mjStuckLeft = true := by decide +kernel

/-- What the mixed join solver is stuck on: one equation, read by neither reader, its right side the β-redex
`λ x y. (λ a b. Y' a b) y x`. -/
def mjStuckJoin : Bool :=
  match run towerMixedJoinSolver mjStore 5 with
  | .stuck state =>
      match state.remaining with
      | [e] => !(Miller.readEq (S := setting) e).isSome && !(readFlexK (S := setting) e).isSome &&
          decide (e.2.2.code =
            .lam (.lam (.app (.app (.lam (.lam (.app (.app (.var 4) (.var 1)) (.var 0)))) (.var 0)) (.var 1))))
      | _ => false
  | _ => false

theorem mj_stuck_join : mjStuckJoin = true := by decide +kernel

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
