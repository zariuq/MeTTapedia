import Mettapedia.ProbabilityTheory.StochasticInference.ProofSearch
import Mettapedia.ProbabilityTheory.StochasticInference.BetaPredictive

/-!
# Learned rule selection with a checked query interval

Training measures each clause's contribution on completed older queries.
The learned selector ranks clauses by their recorded contribution rates.
At query time it has the same number of offered clauses as a fixed agenda.
The common proof checker reads both selected subprograms.
-/

set_option autoImplicit false

namespace Mettapedia.Examples.PLN.LearnedHornReplay

open Mettapedia.Logic.BDDCore
open Mettapedia.ProbabilityTheory.StochasticInference
open StatePredicates HornClosure

private def sameClause {atoms : Nat} (first second : Clause atoms) : Bool :=
  first.head == second.head && first.body == second.body

private def headGoal : Fin 4 := 3

private def clauses : List (Clause 4) := [⟨headGoal, [2]⟩, ⟨headGoal, [1, 0]⟩, ⟨1, [0]⟩]

private def initial (distractorAvailable : Bool) : Table 1 4 :=
  ⟨#[bit 0, falsity 1, if distractorAvailable then truth 1 else falsity 1, falsity 1], rfl⟩

private def fair : UnitProbability := ⟨1 / 2, by decide +kernel, by decide +kernel⟩
private def likely : UnitProbability := ⟨2 / 3, by decide +kernel, by decide +kernel⟩

private def probability (p : UnitProbability) (rules : List (Clause 4)) (known : Table 1 4) : ℚ :=
  ProbLogic.productMass (fun _ => p) ((compile rules known).get headGoal)

private def credit (rule : Clause 4) (tasks : List (UnitProbability × Table 1 4)) : ℚ :=
  let successes := tasks.countP fun (p, facts) =>
    decide (probability p (clauses.filter fun r => !(sameClause r rule)) facts < probability p clauses facts)
  BetaPredictive.predictive ⟨successes, tasks.length - successes⟩ true

private def train : List (Clause 4) :=
  let tasks := [(fair, initial false), (likely, initial false)]
  let scored := clauses.map fun rule => (rule, credit rule tasks)
  (scored.mergeSort (fun left right => decide (left.2 ≥ right.2))).map Prod.fst

def lower (offered : List (Clause 4)) (known : Table 1 4) : Option (ℚ × ℚ) :=
  let checked := ProbLogic.budgetedHorn clauses known headGoal
    (fun rule => offered.any (sameClause rule)) 2
  checked.productInterval? (fun _ => fair) (truth 1)

def replay (shifted : Bool) : Option (ℚ × ℚ) × Option (ℚ × ℚ) × ℚ :=
  let known := initial shifted
  (lower (clauses.take 2) known, lower (train.take 2) known, probability fair clauses known)

#guard replay false == (some (0, 1), some (1 / 2, 1), 1 / 2)
#guard replay true == (some (1, 1), some (1 / 2, 1), 1)

end Mettapedia.Examples.PLN.LearnedHornReplay

def main : IO Unit := do
  IO.println (Mettapedia.Examples.PLN.LearnedHornReplay.replay false)
  IO.println (Mettapedia.Examples.PLN.LearnedHornReplay.replay true)
