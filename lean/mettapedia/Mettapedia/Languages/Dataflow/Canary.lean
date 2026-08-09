import Mettapedia.Languages.Dataflow.Operational

/-!
# Compiled canaries for the dataflow language

A concrete arithmetic instantiation, exercising both sides of the boundary.

Positive: a program with two *independent* instructions runs to the same
answer under two genuinely different schedules, and that answer is its
denotation.

Negative, one per well-formedness condition — none asserted, all proved:

* two writers for one cell;
* an operand with no writer and no input;
* a dependency cycle;
* an operator applied at the wrong arity.

The cycle case is the interesting one: no acyclicity predicate is consulted,
the cell simply denotes nothing at any budget.
-/

namespace Mettapedia.Languages.Dataflow.Canary

open Mettapedia.Languages.Dataflow

/-- A two-operator arithmetic signature. -/
inductive ArithOp where
  | add
  | mul
deriving DecidableEq, Repr

/-- Both operators are binary. -/
def arith : PureOperatorSpec ArithOp Nat where
  arity := fun _ => 2
  apply := fun op args =>
    match op, args with
    | .add, [x, y] => x + y
    | .mul, [x, y] => x * y
    | _, _ => 0

/-! ## Positive: independent instructions, two schedules, one answer -/

private def addNode : Instruction ArithOp Nat := .apply 10 .add [1, 2]
private def mulNode : Instruction ArithOp Nat := .apply 11 .mul [1, 2]
private def joinNode : Instruction ArithOp Nat := .apply 12 .add [10, 11]

/-- `c10 = c1 + c2` and `c11 = c1 * c2` are independent; `c12` joins them.
With `c1 = 5` and `c2 = 7` the answer is `12 + 35 = 47`. -/
def sumProduct : Program ArithOp Nat where
  inputs := [(1, 5), (2, 7)]
  instructions := [addNode, mulNode, joinNode]
  result := 12

/-- The returned cell denotes 47. -/
theorem sumProduct_denotes : Denotes arith sumProduct 12 47 := by
  have input1 : sumProduct.inputValue? 1 = some 5 := rfl
  have input2 : sumProduct.inputValue? 2 = some 7 := rfl
  have denote10 : Denotes arith sumProduct 10 12 :=
    Denotes.apply (c := 10) rfl rfl rfl
      (DenotesList.cons (Denotes.input input1)
        (DenotesList.cons (Denotes.input input2) DenotesList.nil))
  have denote11 : Denotes arith sumProduct 11 35 :=
    Denotes.apply (c := 11) rfl rfl rfl
      (DenotesList.cons (Denotes.input input1)
        (DenotesList.cons (Denotes.input input2) DenotesList.nil))
  exact Denotes.apply (c := 12) rfl rfl rfl
    (DenotesList.cons denote10 (DenotesList.cons denote11 DenotesList.nil))

/-! ### Two genuinely different schedules

Schedule A fires the sum before the product; schedule B fires the product
first.  Both reach the same terminal state content. -/

private def envStart : List (CellId × Nat) := [(1, 5), (2, 7)]

theorem schedule_add_first :
    Steps arith sumProduct.initialState
      ⟨[(12, 47), (11, 35), (10, 12)] ++ envStart, []⟩ := by
  refine Relation.ReflTransGen.head (b := ⟨(10, 12) :: envStart,
    [mulNode, joinNode]⟩) ?_ ?_
  · exact Step.fire (computed := envStart) (pre := [])
      (post := [mulNode, joinNode]) (i := addNode) (v := 12) rfl
  refine Relation.ReflTransGen.head (b := ⟨(11, 35) :: (10, 12) :: envStart,
    [joinNode]⟩) ?_ ?_
  · exact Step.fire (computed := (10, 12) :: envStart) (pre := [])
      (post := [joinNode]) (i := mulNode) (v := 35) rfl
  refine Relation.ReflTransGen.head (b := ⟨(12, 47) :: (11, 35) ::
    (10, 12) :: envStart, []⟩) ?_ Relation.ReflTransGen.refl
  exact Step.fire (computed := (11, 35) :: (10, 12) :: envStart) (pre := [])
    (post := []) (i := joinNode) (v := 47) rfl

theorem schedule_mul_first :
    Steps arith sumProduct.initialState
      ⟨[(12, 47), (10, 12), (11, 35)] ++ envStart, []⟩ := by
  refine Relation.ReflTransGen.head (b := ⟨(11, 35) :: envStart,
    [addNode, joinNode]⟩) ?_ ?_
  · exact Step.fire (computed := envStart) (pre := [addNode])
      (post := [joinNode]) (i := mulNode) (v := 35) rfl
  refine Relation.ReflTransGen.head (b := ⟨(10, 12) :: (11, 35) :: envStart,
    [joinNode]⟩) ?_ ?_
  · exact Step.fire (computed := (11, 35) :: envStart) (pre := [])
      (post := [joinNode]) (i := addNode) (v := 12) rfl
  refine Relation.ReflTransGen.head (b := ⟨(12, 47) :: (10, 12) ::
    (11, 35) :: envStart, []⟩) ?_ Relation.ReflTransGen.refl
  exact Step.fire (computed := (10, 12) :: (11, 35) :: envStart) (pre := [])
    (post := []) (i := joinNode) (v := 47) rfl

/-- The two schedules are genuinely different runs — their intermediate
environments differ — yet they agree on the returned cell. -/
theorem schedules_differ_but_agree :
    ([(12, 47), (11, 35), (10, 12)] ++ envStart) ≠
      ([(12, 47), (10, 12), (11, 35)] ++ envStart) ∧
    lookup ([(12, 47), (11, 35), (10, 12)] ++ envStart) 12 =
      lookup ([(12, 47), (10, 12), (11, 35)] ++ envStart) 12 := by
  refine ⟨by simp, rfl⟩

/-! ## Negative: two writers for one cell -/

def twoWriters : Program ArithOp Nat where
  inputs := [(1, 5)]
  instructions := [.const 7 1, .const 7 2]
  result := 7

theorem twoWriters_not_wellFormed : ¬ twoWriters.WellFormed arith := by
  intro wf
  have := wf.writersUnique
  simp [twoWriters, Instruction.dst] at this

/-! ## Negative: an operand with no writer and no input -/

def danglingOperand : Program ArithOp Nat where
  inputs := [(1, 5)]
  instructions := [.apply 0 .add [1, 9]]
  result := 0

/-- Cell 9 is supplied by nothing, so it denotes at no budget. -/
theorem dangling_cell_never_denotes :
    ∀ fuel, denoteCell arith danglingOperand fuel 9 = none := by
  intro fuel
  cases fuel with
  | zero => rw [denoteCell_zero]; rfl
  | succ fuel => rw [denoteCell_succ]; rfl

/-- Hence the returned cell denotes at no budget either. -/
theorem dangling_result_never_denotes :
    ∀ fuel, denoteCell arith danglingOperand fuel 0 = none := by
  intro fuel
  cases fuel with
  | zero => rw [denoteCell_zero]; rfl
  | succ fuel =>
      have operandsNone :
          denoteOperands arith danglingOperand fuel [1, 9] = none := by
        cases headValue : denoteCell arith danglingOperand fuel 1 with
        | none => simp [denoteOperands_cons, headValue]
        | some w =>
            simp [denoteOperands_cons, headValue,
              dangling_cell_never_denotes fuel]
      rw [denoteCell_succ,
        show danglingOperand.inputValue? 0 = none from rfl,
        show danglingOperand.writerOf? 0 =
          some (.apply 0 .add [1, 9]) from rfl]
      simp [operandsNone]

theorem danglingOperand_not_wellFormed :
    ¬ danglingOperand.WellFormed arith := by
  intro wf
  obtain ⟨v, fuel, evaluated⟩ := wf.resultDenotes
  have evaluated' : denoteCell arith danglingOperand fuel 0 = some v :=
    evaluated
  rw [dangling_result_never_denotes fuel] at evaluated'
  cases evaluated'

/-! ## Negative: a dependency cycle -/

def cyclic : Program ArithOp Nat where
  inputs := []
  instructions := [.apply 0 .add [1, 1], .apply 1 .add [0, 0]]
  result := 0

/-- Neither cell of the cycle denotes at any budget.  Nothing about
acyclicity is consulted: the recursion simply never bottoms out. -/
theorem cyclic_never_denotes : ∀ fuel,
    denoteCell arith cyclic fuel 0 = none ∧
      denoteCell arith cyclic fuel 1 = none := by
  intro fuel
  induction fuel with
  | zero => exact ⟨by rw [denoteCell_zero]; rfl, by rw [denoteCell_zero]; rfl⟩
  | succ fuel inductionHypothesis =>
      constructor
      · have operandsNone :
            denoteOperands arith cyclic fuel [1, 1] = none := by
          simp [denoteOperands_cons, inductionHypothesis.2]
        rw [denoteCell_succ,
          show cyclic.inputValue? 0 = none from rfl,
          show cyclic.writerOf? 0 = some (.apply 0 .add [1, 1]) from rfl]
        simp [operandsNone]
      · have operandsNone :
            denoteOperands arith cyclic fuel [0, 0] = none := by
          simp [denoteOperands_cons, inductionHypothesis.1]
        rw [denoteCell_succ,
          show cyclic.inputValue? 1 = none from rfl,
          show cyclic.writerOf? 1 = some (.apply 1 .add [0, 0]) from rfl]
        simp [operandsNone]

theorem cyclic_not_wellFormed : ¬ cyclic.WellFormed arith := by
  intro wf
  obtain ⟨v, fuel, evaluated⟩ := wf.resultDenotes
  have evaluated' : denoteCell arith cyclic fuel 0 = some v := evaluated
  rw [(cyclic_never_denotes fuel).1] at evaluated'
  cases evaluated'

/-! ## Negative: wrong operator arity -/

def wrongArity : Program ArithOp Nat where
  inputs := [(1, 5), (2, 7), (3, 9)]
  instructions := [.apply 0 .add [1, 2, 3]]
  result := 0

theorem wrongArity_not_wellFormed : ¬ wrongArity.WellFormed arith := by
  intro wf
  have := wf.aritiesOk (.apply 0 .add [1, 2, 3]) (by simp [wrongArity])
  simp [Instruction.arityOk, arith] at this

end Mettapedia.Languages.Dataflow.Canary
