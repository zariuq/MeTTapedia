import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilDriverControls
import Mettapedia.Machines.CTLUntilFiniteSupport

/-! Removing recursion from the actual driver loses a required predecessor.
The source control and independent finite-model computation are kept distinct;
the syntactic admission failure is additionally kernel checked. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilDriverNegative

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics
open ScopedQuerySource.Controls (call number answers finalRows)
open ScopedQuerySource.CTLUntilDriverControls

def oneRoundBody : Atom := call "let*" [.expression [
  .expression [.var "k1", call "+" [.var "k", number 1]],
  .expression [.var "n", call "eu-round" [.var "f", .var "a", .var "k", .var "k1"]],
  .expression [.var "d", call "drop" [.var "f", .var "k"]]], .var "k1"]

def oneRoundEquation : Equation := {loopEquation with body := oneRoundBody}
def mutant : Program := {program with equations := [
  ScopedQuerySource.CTLUntilControls.guard, ScopedQuerySource.CTLUntilControls.roundEquation,
  dropEquation, oneRoundEquation, entryEquation]}

theorem changed_loop_is_not_the_authored_equation : oneRoundEquation ≠ loopEquation := by
  intro same
  have body := congrArg Equation.body same
  exact (by decide +kernel : oneRoundBody ≠ loopBody) body

theorem mutant_does_not_supply_the_authored_loop : mutant.equations[3]? ≠ some loopEquation := by
  intro same
  exact changed_loop_is_not_the_authored_equation (Option.some.inj same)

def goalZero : Atom := ScopedQuerySource.CTLUntilControls.sat (.symbol "f") (number 0)

-- The authored source reaches all three states and counts the quiet round.
#guard answers program input entry 15000 == some [number 3]
#guard (finalRows program input entry 15000).map (fun rows => rows.contains goalZero) == some true
-- The actual changed source stops after one productive round and misses 0.
#guard answers mutant input entry 15000 == some [number 1]
#guard (finalRows mutant input entry 15000).map (fun rows => rows.contains goalZero) == some false

theorem independent_model_requires_zero :
    Mettapedia.Machines.CTLUntilCandidateBag.run [(0, 1), (1, 2)] [0, 1, 3] 3 0 ⟨[2], [2]⟩ =
      some (⟨[2, 1, 0], []⟩, 3) := rfl

theorem zero_has_until_path :
    Mettapedia.Logic.CTLFixedPoints.Until
      (Mettapedia.Machines.CTLUntilFrontier.Relation ([(0, 1), (1, 2)] : List (Nat × Nat)).toFinset)
      ↑([0, 1, 3] : List Nat).toFinset ↑([2] : List Nat).toFinset 0 := by
  apply (Mettapedia.Machines.CTLUntilCandidateBag.completed_until [(0, 1), (1, 2)] [0, 1, 3] [2]
    3 ⟨[2, 1, 0], []⟩ 3 independent_model_requires_zero 0).mp
  simp

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilDriverNegative
