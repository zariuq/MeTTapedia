import Mettapedia.Logic.BDD.NestedCTL
import Mettapedia.Logic.BDD.CTLProgram
import Mettapedia.Logic.BDD.SymbolicCTLControls

/-! Executed nested CTL and shared-table controls. The fixed state relation
is part of every result; changed edges and deadlock policy are observable.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.BDDCore.NestedCTL.Controls

open StatePredicates StateTransducer FixedPointSolver CTLFormula CTLProgram

def flip : Certified 1 (truth 1) := SymbolicCTL.Controls.flipProgram
def empty : Certified 1 (truth 1) := SymbolicCTL.Controls.emptyProgram
def stutter : Certified 1 (truth 1) := empty.withStuttering
def atoms : Unit → Diagram 1 := fun _ => bit 0

local macro "compute_nested" : tactic => `(tactic|
  simp [compile, BoundedFixedPoints.least, BoundedFixedPoints.greatest, BoundedFixedPoints.budget,
    SymbolicCTL.untilOp, SymbolicCTL.globallyOp, advance, Result.frame, Result.finished,
    flip, empty, stutter, atoms, SymbolicCTL.Controls.flipProgram, SymbolicCTL.Controls.emptyProgram,
    Certified.withStuttering, equivalent, StateTransducer.pre, rawPre, rulePre, within, complement,
    totalize, stutterRule, anyEnabled, StateTransducer.Controls.flip, compileGuard, substitute,
    choose, truth, falsity, bit, conj, disj, neg, apply, bddVar, bddNot, mk, BDD.eval])

theorem globally_eventually_bit (state : State 1) :
    (compile flip atoms (.eg (.eu .truth (.atom ())))).val.eval state = true := by compute_nested

theorem eventually_globally_bit (state : State 1) :
    (compile flip atoms (.eu .truth (.eg (.atom ())))).val.eval state = false := by compute_nested

theorem nested_temporal_order_matters (state : State 1) :
    (compile flip atoms (.eg (.eu .truth (.atom ())))).val.eval state ≠
      (compile flip atoms (.eu .truth (.eg (.atom ())))).val.eval state := by
  rw [globally_eventually_bit, eventually_globally_bit]
  decide

theorem next_global_deadlock_policy (state : State 1) :
    (compile empty atoms (.ex (.eg .truth))).val.eval state = false ∧
      (compile stutter atoms (.ex (.eg .truth))).val.eval state = true := by compute_nested

theorem same_formula_different_relation_is_not_a_cache_hit :
    (compile empty atoms (.eu .truth (.atom ()))).val.eval (fun _ => false) = false ∧
      (compile flip atoms (.eu .truth (.atom ()))).val.eval (fun _ => false) = true := by compute_nested

def shared : List (Instruction Unit) :=
  [⟨"a", .atom ()⟩, ⟨"b", .neg "a"⟩, ⟨"c", .disj "a" "b"⟩, ⟨"d", .conj "c" "c"⟩]

def unfolded : Formula Unit := .conj (.disj (.atom ()) (.neg (.atom ())))
  (.disj (.atom ()) (.neg (.atom ())))

def formulaNodes : Formula Unit → Nat
  | .atom _ | .truth => 1
  | .neg body | .ex body | .eg body => 1 + formulaNodes body
  | .conj left right | .disj left right | .eu left right => 1 + formulaNodes left + formulaNodes right

theorem shared_formula_expands_exactly :
    (decodeFrom shared []).bind (lookup "d") = some unfolded := by decide +kernel

theorem four_shared_records_nine_unfolded_nodes : shared.length = 4 ∧ formulaNodes unfolded = 9 := by decide

theorem shared_root_exact : root flip atoms shared "d" = some (compile flip atoms unfolded) := by
  rw [root_refines, shared_formula_expands_exactly]
  rfl

theorem shared_visits_four_records : (executeCounted flip atoms shared []).1 = 4 := by
  have decoded : ∃ table, decodeFrom shared [] = some table := by
    refine ⟨[("d", unfolded), ("c", .disj (.atom ()) (.neg (.atom ()))),
      ("b", .neg (.atom ())), ("a", .atom ())], ?_⟩
    decide +kernel
  obtain ⟨table, decoded⟩ := decoded
  have run : executeFrom flip atoms shared [] = some (mapTable (compile flip atoms) table) := by
    rw [show ([] : Table (Diagram 1)) = mapTable (compile flip atoms) [] from rfl,
      program_refines, decoded]
    rfl
  exact successful_visits flip atoms shared [] _ run

theorem forward_reference_is_not_false :
    decodeFrom ([⟨"first", .eg "later"⟩, ⟨"later", .truth⟩] : List (Instruction Unit)) [] = none := by decide

theorem cyclic_reference_is_not_a_temporal_fixpoint :
    decodeFrom ([⟨"self", .ex "self"⟩] : List (Instruction Unit)) [] = none := by decide

end Mettapedia.Logic.BDDCore.NestedCTL.Controls
