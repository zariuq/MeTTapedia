import Mettapedia.Languages.MeTTa.PeTTa.OutputPlanFormationCorrect

/-!
# Successful compilation is independent of a larger structural allowance

Increasing compiler recursion allowance changes neither the generated plan
nor its allocation/alias state after success. This is separate from evaluator
fuel: it permits no change to an execution cutoff or an earlier effect.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.OutputPlan

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

theorem compile_succ_of_success (context : Context) : ∀ depth supply expression result,
    compile context depth supply expression = some result →
      compile context (depth + 1) supply expression = some result := by
  intro depth
  induction depth with
  | zero => intro supply expression result computed; cases computed
  | succ depth ih =>
      intro supply expression result computed
      change perform context (compile context (depth + 1)) supply (classify expression) = some result
      apply layer_of_rule context (compile context (depth + 1)) (FormationAt context depth)
        (fun s e r derivation => ih s e r ((compile_iff context depth s e r).mpr derivation))
      exact (compile_iff context (depth + 1) supply expression result).mp computed

theorem compile_add_of_success (context : Context) (depth extra : Nat) (supply : Supply)
    (expression : Atom) (result : Result) (computed : compile context depth supply expression = some result) :
    compile context (depth + extra) supply expression = some result := by
  induction extra with
  | zero => exact computed
  | succ extra ih => exact compile_succ_of_success context (depth + extra) supply expression result ih

theorem compile_of_allowance_le (context : Context) (depth later : Nat) (supply : Supply)
    (expression : Atom) (result : Result) (grows : depth ≤ later)
    (computed : compile context depth supply expression = some result) :
    compile context later supply expression = some result := by
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le grows
  exact compile_add_of_success context depth extra supply expression result computed

theorem compile_success_independent (context : Context) (firstDepth secondDepth : Nat) (supply : Supply)
    (expression : Atom) (first second : Result)
    (left : compile context firstDepth supply expression = some first)
    (right : compile context secondDepth supply expression = some second) : first = second := by
  have leftLater := compile_add_of_success context firstDepth secondDepth supply expression first left
  have rightLater := compile_add_of_success context secondDepth firstDepth supply expression second right
  rw [Nat.add_comm secondDepth firstDepth] at rightLater
  exact Option.some.inj (leftLater.symm.trans rightLater)

theorem formation_success_independent {context : Context} {firstDepth secondDepth : Nat} {supply : Supply}
    {expression : Atom} {first second : Result}
    (left : FormationAt context firstDepth supply expression first)
    (right : FormationAt context secondDepth supply expression second) : first = second :=
  compile_success_independent context firstDepth secondDepth supply expression first second
    ((compile_iff context firstDepth supply expression first).mpr left)
    ((compile_iff context secondDepth supply expression second).mpr right)

end Mettapedia.Languages.MeTTa.PeTTa.OutputPlan
