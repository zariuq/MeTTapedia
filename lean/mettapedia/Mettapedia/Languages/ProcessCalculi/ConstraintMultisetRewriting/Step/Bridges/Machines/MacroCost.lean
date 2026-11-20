import Mettapedia.Languages.PartrecMachine.Realization

/-!
# Finite costs of the existing eager-to-small-step realization

One Mathlib machine step may expand into several authored reductions.
The retained paths already constructed by `PartrecMachine.Realization`
are nonempty and bounded by the code/continuation structure. These bounds
depend on the supplied program, not on a global execution cap, and do not
assume that the whole program terminates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.MacroCost

open Mettapedia.Languages.PartrecMachine
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Turing.ToPartrec

/-- The longest setup path of one finite code, before it returns to the
machine's continuation state. Only the selected child is evaluated. -/
def setupBound : Code → Nat
  | .zero' | .succ | .tail => 1
  | .cons f _ => setupBound f + 1
  | .comp _ g => setupBound g + 1
  | .fix f => setupBound f + 1
  | .case f g => max (setupBound f) (setupBound g) + 1

/-- The longest administrative return path before the eager machine exposes
its next configuration. An alternative under `fix` is bounded on both sides. -/
def returnBound : Cont → Nat
  | .halt => 1
  | .cons₁ fs _ _ => setupBound fs + 1
  | .cons₂ _ k => returnBound k + 1
  | .comp f _ => setupBound f + 1
  | .fix f k => max (returnBound k) (setupBound f) + 1

theorem normalPath_cost (code : Code) (continuation : Cont) (input : List Nat) :
    0 < (normalPath code continuation input).length ∧
      (normalPath code continuation input).length ≤ setupBound code := by
  induction code generalizing continuation input with
  | zero' | succ | tail => simp [normalPath, reductionPath, Route.length, setupBound]
  | cons f fs ihf _ =>
      have bound := ihf (.cons₁ fs input continuation) input
      simp only [normalPath, reductionThen, Route.length, setupBound]
      omega
  | comp f g _ ihg =>
      have bound := ihg (.comp f continuation) input
      simp only [normalPath, reductionThen, Route.length, setupBound]
      omega
  | fix f ihf =>
      have bound := ihf (.fix f continuation) input
      simp only [normalPath, reductionThen, Route.length, setupBound]
      omega
  | case f g ihf ihg =>
      rcases input with _ | ⟨_ | n, tail⟩
      · have bound := ihf continuation []
        change 0 < (normalPath f continuation []).length + 1 ∧
          (normalPath f continuation []).length + 1 ≤ max (setupBound f) (setupBound g) + 1
        omega
      · have bound := ihf continuation tail
        change 0 < (normalPath f continuation tail).length + 1 ∧
          (normalPath f continuation tail).length + 1 ≤ max (setupBound f) (setupBound g) + 1
        omega
      · have bound := ihg continuation (n :: tail)
        change 0 < (normalPath g continuation (n :: tail)).length + 1 ∧
          (normalPath g continuation (n :: tail)).length + 1 ≤ max (setupBound f) (setupBound g) + 1
        omega

theorem retPath_cost (continuation : Cont) (input : List Nat) :
    0 < (retPath continuation input).length ∧
      (retPath continuation input).length ≤ returnBound continuation := by
  induction continuation generalizing input with
  | halt => simp [retPath, reductionPath, Route.length, returnBound]
  | cons₁ fs values k _ =>
      have bound := normalPath_cost fs (.cons₂ input k) values
      simp only [retPath, reductionThen, Route.length, returnBound]
      omega
  | cons₂ values k ih =>
      have bound := ih (values.headI :: input)
      simp only [retPath, reductionThen, Route.length, returnBound]
      omega
  | comp f k _ =>
      have bound := normalPath_cost f k input
      simp only [retPath, reductionThen, Route.length, returnBound]
      omega
  | fix f k ih =>
      rcases input with _ | ⟨_ | n, tail⟩
      · have bound := ih []
        change 0 < (retPath k []).length + 1 ∧
          (retPath k []).length + 1 ≤ max (returnBound k) (setupBound f) + 1
        omega
      · have bound := ih tail
        change 0 < (retPath k tail).length + 1 ∧
          (retPath k tail).length + 1 ≤ max (returnBound k) (setupBound f) + 1
        omega
      · have bound := normalPath_cost f (.fix f k) tail
        change 0 < (normalPath f (.fix f k) tail).length + 1 ∧
          (normalPath f (.fix f k) tail).length + 1 ≤ max (returnBound k) (setupBound f) + 1
        omega

def stepBound : Cfg → Nat
  | .halt _ => 0
  | .ret continuation _ => returnBound continuation

theorem machineStepPath_cost {before after : Cfg} (stepped : after ∈ step before) :
    0 < (machineStepPath stepped).length ∧ (machineStepPath stepped).length ≤ stepBound before := by
  cases before with
  | halt _ => simp [step] at stepped
  | ret continuation input =>
      have same := Option.some.inj stepped
      cases same
      exact retPath_cost continuation input

namespace Controls

theorem setup_expansion : (normalPath (.cons .succ .tail) .halt []).length = 2 := rfl

/-- The cost is a path length, not a statement that a complete recursive
program terminates. The fixpoint setup itself still has finite cost. -/
theorem divergent_setup_is_finite :
    (normalPath (.fix .succ) .halt []).length = 2 ∧ setupBound (.fix .succ) = 2 := ⟨rfl, rfl⟩

end Controls

#print axioms normalPath_cost
#print axioms retPath_cost
#print axioms machineStepPath_cost

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.MacroCost
