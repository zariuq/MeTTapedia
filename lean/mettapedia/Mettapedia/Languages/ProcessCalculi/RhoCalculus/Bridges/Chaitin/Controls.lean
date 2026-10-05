import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.Chaitin.TablePrograms
import Mettapedia.Languages.Chaitin.GSLT.Controls

/-!
# Historical Lisp execution controls at the rho boundary

Successful source executions reach canonical rho normal forms. An already
halted machine still requires dispatch: the initial controller packet is
not itself a target normal form. These examples do not assert reflection
of arbitrary target executions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.Chaitin.Controls

open Mettapedia.Languages
open Mettapedia.Languages.TuringMachine
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open TablePrograms

def oneRow : Machine := ⟨[⟨0, 0, 1, .right, 1⟩]⟩
def written : Configuration := ⟨1, [1], 0, []⟩

theorem one_lisp_iteration_is_fifteen_communications :
    Nonempty (ReducesN 15 (TuringMachine.Persistent.encoding oneRow Configuration.blank)
      (TuringMachine.Persistent.encoding oneRow written)) := by
  apply iteration_preserved
  exact (Chaitin.GSLT.TableIteration.returns_iff _ _ _).mpr (by decide)

theorem empty_table_requires_dispatch (configuration : Configuration) :
    ¬ Reduction.NormalForm (TuringMachine.Persistent.encoding ⟨[]⟩ configuration) ∧
      Nonempty (ReducesN 5 (TuringMachine.Persistent.encoding ⟨[]⟩ configuration)
        (TuringMachine.Persistent.awaiting ⟨[]⟩ configuration)) ∧
      Reduction.NormalForm (TuringMachine.Persistent.awaiting ⟨[]⟩ configuration) := by
  refine ⟨TuringMachine.Halting.encoding_not_normal _ _, ?_⟩
  apply iteration_stopped_quiescent
  exact (Chaitin.GSLT.TableIteration.returns_iff _ _ _).mpr rfl

theorem busy_beaver_lisp_execution_is_quiescent_rho_execution :
    Nonempty (ReducesStar (TuringMachine.Persistent.encoding busyBeaver2 Configuration.blank)
      (TuringMachine.Persistent.awaiting busyBeaver2 busyBeaver2Final)) ∧
      Reduction.NormalForm (TuringMachine.Persistent.awaiting busyBeaver2 busyBeaver2Final) :=
  returns_quiescent _ _ _ Chaitin.GSLT.busyBeaver2_returns

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.Chaitin.Controls
