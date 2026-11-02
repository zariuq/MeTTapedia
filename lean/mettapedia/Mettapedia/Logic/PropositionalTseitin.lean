import Foundation.Propositional.ClassicalSemantics.Basic
import Mettapedia.Logic.MarkovLogicClauseSemantics
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Tauto

/-!
# Definitional CNF with a unique auxiliary extension

The source is Foundation's propositional syntax. The target is a list of the
existing grounded clauses, with disjoint finite source and auxiliary names.
The compiler emits both directions of every gate definition in postorder.
An independent traversal evaluates all auxiliary values from the source.

The size bounds count syntax occurrences and emitted clauses. They make no
claim about a native implementation's time, allocation, or sharing policy.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.PropositionalTseitin

open LO.Propositional (Formula)
open MarkovLogicClauseSemantics

def eval {α : Type*} (input : α → Bool) : Formula α → Bool
  | .atom a => input a
  | .falsum => false
  | .and a b => eval input a && eval input b
  | .or a b => eval input a || eval input b
  | .imp a b => !(eval input a) || eval input b

theorem eval_eq_true_iff {α : Type*} (input : α → Bool) (formula : Formula α) :
    eval input formula = true ↔
      Formula.ClassicalSemantics.val (fun a => input a = true) formula := by
  classical
  induction formula <;> simp_all [eval, Formula.ClassicalSemantics.val, Bool.eq_false_iff]
  tauto

def auxCount {α : Type*} : Formula α → Nat
  | .atom _ => 0
  | .falsum => 1
  | .and a b | .or a b | .imp a b => auxCount a + (auxCount b + 1)

abbrev Wire (n k : Nat) := Fin n ⊕ Fin k

def read {n k : Nat} (input : Fin n → Bool) (auxiliary : Fin k → Bool) : Wire n k → Bool :=
  Sum.elim input auxiliary

def evalLiteral {α : Type*} (world : α → Bool) : Literal α → Bool
  | .pos a => world a
  | .neg a => !(world a)

def complement {α : Type*} : Literal α → Literal α
  | .pos a => .neg a
  | .neg a => .pos a

@[simp] theorem evalLiteral_pos {α : Type*} (world : α → Bool) (a : α) :
    evalLiteral world (.pos a) = world a := rfl

@[simp] theorem evalLiteral_neg {α : Type*} (world : α → Bool) (a : α) :
    evalLiteral world (.neg a) = !(world a) := rfl

@[simp] theorem evalLiteral_complement {α : Type*} (world : α → Bool) (literal : Literal α) :
    evalLiteral world (complement literal) = !(evalLiteral world literal) := by
  cases literal <;> simp [complement]

theorem evalLiteral_eq_true_iff {α : Type*} (world : α → Bool) (literal : Literal α) :
    evalLiteral world literal = true ↔ Literal.holds world literal := by
  cases literal <;> simp [evalLiteral, Literal.holds]

def evalClause {α : Type*} [DecidableEq α] (world : α → Bool) (clause : GroundClause α) : Bool :=
  decide (∃ literal ∈ clause, evalLiteral world literal = true)

def evalCNF {α : Type*} [DecidableEq α] (clauses : List (GroundClause α)) (world : α → Bool) : Bool :=
  clauses.all (evalClause world)

theorem evalClause_eq_true_iff {α : Type*} [DecidableEq α]
    (world : α → Bool) (clause : GroundClause α) :
    evalClause world clause = true ↔ clause.holds world := by
  simp [evalClause, GroundClause.holds, evalLiteral_eq_true_iff]

theorem evalCNF_eq_true_iff {α : Type*} [DecidableEq α]
    (clauses : List (GroundClause α)) (world : α → Bool) :
    evalCNF clauses world = true ↔ ∀ clause ∈ clauses, clause.holds world := by
  simp [evalCNF, List.all_eq_true, evalClause_eq_true_iff]

def renameLiteral {α β : Type*} (rename : α → β) : Literal α → Literal β
  | .pos a => .pos (rename a)
  | .neg a => .neg (rename a)

def renameClause {α β : Type*} [DecidableEq β] (rename : α → β) (clause : GroundClause α) :
    GroundClause β := clause.image (renameLiteral rename)

def renameCNF {α β : Type*} [DecidableEq β] (rename : α → β)
    (clauses : List (GroundClause α)) : List (GroundClause β) := clauses.map (renameClause rename)

@[simp] theorem evalLiteral_rename {α β : Type*} (rename : α → β) (world : β → Bool)
    (literal : Literal α) :
    evalLiteral world (renameLiteral rename literal) = evalLiteral (world ∘ rename) literal := by
  cases literal <;> rfl

@[simp] theorem evalClause_rename {α β : Type*} [DecidableEq α] [DecidableEq β] (rename : α → β)
    (world : β → Bool) (clause : GroundClause α) :
    evalClause world (renameClause rename clause) = evalClause (world ∘ rename) clause := by
  simp [evalClause, renameClause, Function.comp_def]

@[simp] theorem evalCNF_rename {α β : Type*} [DecidableEq α] [DecidableEq β] (rename : α → β)
    (world : β → Bool) (clauses : List (GroundClause α)) :
    evalCNF (renameCNF rename clauses) world = evalCNF clauses (world ∘ rename) := by
  simp [evalCNF, renameCNF, Function.comp_def]

inductive BinaryOp where
  | and | or | imp
  deriving DecidableEq, Repr

def BinaryOp.eval : BinaryOp → Bool → Bool → Bool
  | .and, a, b => a && b
  | .or, a, b => a || b
  | .imp, a, b => !a || b

/-- These are literal gate clauses, not an enumeration of satisfying worlds. -/
def gateClauses {α : Type*} [DecidableEq α] (op : BinaryOp)
    (left right : Literal α) (output : α) : List (GroundClause α) :=
  match op with
  | .and => [{.neg output, left}, {.neg output, right}, {.pos output, complement left, complement right}]
  | .or => [{.pos output, complement left}, {.pos output, complement right}, {.neg output, left, right}]
  | .imp => [{.pos output, left}, {.pos output, complement right}, {.neg output, complement left, right}]

theorem gateClauses_correct {α : Type*} [DecidableEq α] (op : BinaryOp)
    (left right : Literal α) (output : α) (world : α → Bool) :
    evalCNF (gateClauses op left right output) world = true ↔
      world output = op.eval (evalLiteral world left) (evalLiteral world right) := by
  cases op <;> cases hl : evalLiteral world left <;> cases hr : evalLiteral world right <;>
    cases ho : world output <;> simp [gateClauses, evalCNF, evalClause, BinaryOp.eval, hl, hr, ho]

structure Encoding (n k : Nat) where
  root : Literal (Wire n k)
  clauses : List (GroundClause (Wire n k))

def leftWire {n l : Nat} (r : Nat) : Wire n l → Wire n (l + (r + 1)) :=
  Sum.map id (Fin.castAdd (r + 1))

def rightWire {n r : Nat} (l : Nat) : Wire n r → Wire n (l + (r + 1)) :=
  Sum.map id (fun i => Fin.natAdd l i.castSucc)

def outputWire {n : Nat} (l r : Nat) : Wire n (l + (r + 1)) :=
  .inr (Fin.natAdd l (Fin.last r))

def combine {n l r : Nat} (op : BinaryOp) (left : Encoding n l) (right : Encoding n r) :
    Encoding n (l + (r + 1)) where
  root := .pos (outputWire l r)
  clauses := renameCNF (leftWire r) left.clauses ++ renameCNF (rightWire l) right.clauses ++
    gateClauses op (renameLiteral (leftWire r) left.root)
      (renameLiteral (rightWire l) right.root) (outputWire l r)

def compile {n : Nat} : (formula : Formula (Fin n)) → Encoding n (auxCount formula)
  | .atom a => ⟨.pos (.inl a), []⟩
  | .falsum => ⟨.pos (.inr (0 : Fin 1)), [{.neg (.inr (0 : Fin 1))}]⟩
  | .and a b => combine .and (compile a) (compile b)
  | .or a b => combine .or (compile a) (compile b)
  | .imp a b => combine .imp (compile a) (compile b)

/-- The auxiliary valuation lists left children, right children, then the parent. -/
def combineAux {l r : Nat} (left : Fin l → Bool) (right : Fin r → Bool) (output : Bool) :
    Fin (l + (r + 1)) → Bool := Fin.addCases left (Fin.lastCases output right)

/-- Source evaluation supplies auxiliary values independently of the clause interpreter. -/
def realizeAux {n : Nat} (input : Fin n → Bool) :
    (formula : Formula (Fin n)) → Fin (auxCount formula) → Bool
  | .atom _ => Fin.elim0
  | .falsum => fun _ => false
  | .and a b => combineAux (realizeAux input a) (realizeAux input b) (eval input a && eval input b)
  | .or a b => combineAux (realizeAux input a) (realizeAux input b) (eval input a || eval input b)
  | .imp a b => combineAux (realizeAux input a) (realizeAux input b) (!(eval input a) || eval input b)

def leftAux {l r : Nat} (auxiliary : Fin (l + (r + 1)) → Bool) : Fin l → Bool :=
  fun i => auxiliary (Fin.castAdd (r + 1) i)

def rightAux {l r : Nat} (auxiliary : Fin (l + (r + 1)) → Bool) : Fin r → Bool :=
  fun i => auxiliary (Fin.natAdd l i.castSucc)

def lastAux {l r : Nat} (auxiliary : Fin (l + (r + 1)) → Bool) : Bool :=
  auxiliary (Fin.natAdd l (Fin.last r))

@[simp] private theorem leftAux_combine {l r : Nat} (left : Fin l → Bool)
    (right : Fin r → Bool) (output : Bool) :
    leftAux (combineAux left right output) = left := by
  funext i
  simp [leftAux, combineAux]

@[simp] private theorem rightAux_combine {l r : Nat} (left : Fin l → Bool)
    (right : Fin r → Bool) (output : Bool) :
    rightAux (combineAux left right output) = right := by
  funext i
  simp [rightAux, combineAux]

@[simp] private theorem lastAux_combine {l r : Nat} (left : Fin l → Bool)
    (right : Fin r → Bool) (output : Bool) :
    lastAux (combineAux left right output) = output := by
  simp only [lastAux, combineAux, Fin.addCases_right, Fin.lastCases_last]

private theorem combineAux_eta {l r : Nat} (auxiliary : Fin (l + (r + 1)) → Bool) :
    combineAux (leftAux auxiliary) (rightAux auxiliary) (lastAux auxiliary) = auxiliary := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [combineAux, leftAux]
  · intro j
    refine Fin.lastCases ?_ ?_ j
    · simp only [combineAux, lastAux, Fin.addCases_right, Fin.lastCases_last]
    · intro k
      simp [combineAux, rightAux]

private theorem aux_eq_combine_iff {l r : Nat} (auxiliary : Fin (l + (r + 1)) → Bool)
    (left : Fin l → Bool) (right : Fin r → Bool) (output : Bool) :
    auxiliary = combineAux left right output ↔
      leftAux auxiliary = left ∧ rightAux auxiliary = right ∧ lastAux auxiliary = output := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨hl, hr, ho⟩
    rw [← combineAux_eta auxiliary, hl, hr, ho]

@[simp] theorem read_leftWire {n l r : Nat} (input : Fin n → Bool)
    (auxiliary : Fin (l + (r + 1)) → Bool) :
    read input auxiliary ∘ leftWire r = read input (leftAux auxiliary) := by
  funext wire
  cases wire <;> rfl

@[simp] theorem read_rightWire {n l r : Nat} (input : Fin n → Bool)
    (auxiliary : Fin (l + (r + 1)) → Bool) :
    read input auxiliary ∘ rightWire l = read input (rightAux auxiliary) := by
  funext wire
  cases wire <;> rfl

@[simp] theorem read_outputWire {n l r : Nat} (input : Fin n → Bool)
    (auxiliary : Fin (l + (r + 1)) → Bool) :
    read input auxiliary (outputWire l r) = lastAux auxiliary := rfl

@[simp] theorem evalCNF_append {α : Type*} [DecidableEq α]
    (first second : List (GroundClause α)) (world : α → Bool) :
    evalCNF (first ++ second) world = (evalCNF first world && evalCNF second world) := by
  simp [evalCNF]

@[simp] theorem evalClause_singleton {α : Type*} [DecidableEq α]
    (world : α → Bool) (literal : Literal α) :
    evalClause world {literal} = evalLiteral world literal := by
  simp [evalClause]

private theorem combine_clauses {n l r : Nat} (op : BinaryOp)
    (left : Encoding n l) (right : Encoding n r) (input : Fin n → Bool)
    (auxiliary : Fin (l + (r + 1)) → Bool) :
    evalCNF (combine op left right).clauses (read input auxiliary) = true ↔
      evalCNF left.clauses (read input (leftAux auxiliary)) = true ∧
      evalCNF right.clauses (read input (rightAux auxiliary)) = true ∧
      lastAux auxiliary = op.eval
        (evalLiteral (read input (leftAux auxiliary)) left.root)
        (evalLiteral (read input (rightAux auxiliary)) right.root) := by
  simp only [combine, evalCNF_append, Bool.and_eq_true, evalCNF_rename,
    gateClauses_correct, evalLiteral_rename, read_leftWire, read_rightWire, read_outputWire, and_assoc]

private theorem combine_spec {n l r : Nat} (op : BinaryOp)
    (left : Encoding n l) (right : Encoding n r) (input : Fin n → Bool)
    (leftValues : Fin l → Bool) (rightValues : Fin r → Bool) (leftValue rightValue : Bool)
    (leftClauses : ∀ auxiliary, evalCNF left.clauses (read input auxiliary) = true ↔ auxiliary = leftValues)
    (rightClauses : ∀ auxiliary, evalCNF right.clauses (read input auxiliary) = true ↔ auxiliary = rightValues)
    (leftRoot : evalLiteral (read input leftValues) left.root = leftValue)
    (rightRoot : evalLiteral (read input rightValues) right.root = rightValue) :
    (∀ auxiliary, evalCNF (combine op left right).clauses (read input auxiliary) = true ↔
      auxiliary = combineAux leftValues rightValues (op.eval leftValue rightValue)) ∧
    evalLiteral (read input (combineAux leftValues rightValues (op.eval leftValue rightValue)))
      (combine op left right).root = op.eval leftValue rightValue := by
  constructor
  · intro auxiliary
    rw [combine_clauses, leftClauses, rightClauses, aux_eq_combine_iff]
    constructor <;> rintro ⟨hl, hr, ho⟩ <;> refine ⟨hl, hr, ?_⟩
    · simpa only [hl, hr, leftRoot, rightRoot] using ho
    · simpa only [hl, hr, leftRoot, rightRoot] using ho
  · simp only [combine, evalLiteral_pos, read_outputWire, lastAux_combine]

/-- All gate values are determined, and the root has the independent source meaning. -/
theorem compile_correct {n : Nat} (formula : Formula (Fin n)) (input : Fin n → Bool) :
    (∀ auxiliary, evalCNF (compile formula).clauses (read input auxiliary) = true ↔
      auxiliary = realizeAux input formula) ∧
    evalLiteral (read input (realizeAux input formula)) (compile formula).root = eval input formula := by
  induction formula with
  | hatom a =>
    constructor
    · intro auxiliary
      simp only [compile, evalCNF, List.all_nil, true_iff]
      funext i
      exact Fin.elim0 i
    · rfl
  | hfalsum =>
    change (∀ auxiliary : Fin 1 → Bool,
      evalCNF [{.neg (.inr (0 : Fin 1))}] (read input auxiliary) = true ↔
        auxiliary = (fun _ => false)) ∧ (false : Bool) = false
    constructor
    · intro auxiliary
      constructor
      · intro holds
        have atZero : auxiliary (0 : Fin 1) = false := by
          simpa [evalCNF, read] using holds
        funext i
        have indexEq : i = (0 : Fin 1) := Subsingleton.elim _ _
        simpa [indexEq] using atZero
      · rintro rfl
        simp [evalCNF, read]
    · rfl
  | hand a b ha hb =>
    exact combine_spec .and (compile a) (compile b) input _ _ _ _ ha.1 hb.1 ha.2 hb.2
  | hor a b ha hb =>
    exact combine_spec .or (compile a) (compile b) input _ _ _ _ ha.1 hb.1 ha.2 hb.2
  | himp a b ha hb =>
    exact combine_spec .imp (compile a) (compile b) input _ _ _ _ ha.1 hb.1 ha.2 hb.2

theorem gates_iff {n : Nat} (formula : Formula (Fin n)) (input : Fin n → Bool)
    (auxiliary : Fin (auxCount formula) → Bool) :
    evalCNF (compile formula).clauses (read input auxiliary) = true ↔
      auxiliary = realizeAux input formula := (compile_correct formula input).1 auxiliary

theorem root_eval {n : Nat} (formula : Formula (Fin n)) (input : Fin n → Bool) :
    evalLiteral (read input (realizeAux input formula)) (compile formula).root = eval input formula :=
  (compile_correct formula input).2

theorem unique_extension {n : Nat} (formula : Formula (Fin n)) (input : Fin n → Bool) :
    ∃! auxiliary, evalCNF (compile formula).clauses (read input auxiliary) = true :=
  ⟨realizeAux input formula, (gates_iff formula input _).mpr rfl,
    fun auxiliary holds => (gates_iff formula input auxiliary).mp holds⟩

def Encoding.asserted {n k : Nat} (encoding : Encoding n k) : List (GroundClause (Wire n k)) :=
  encoding.clauses ++ [{encoding.root}]

/-- Asserting the root filters source worlds; it does not create additional extensions. -/
theorem asserted_correct {n : Nat} (formula : Formula (Fin n)) (input : Fin n → Bool)
    (auxiliary : Fin (auxCount formula) → Bool) :
    evalCNF (compile formula).asserted (read input auxiliary) = true ↔
      eval input formula = true ∧ auxiliary = realizeAux input formula := by
  rw [Encoding.asserted, evalCNF_append, Bool.and_eq_true, gates_iff]
  simp only [evalCNF, List.all_cons, List.all_nil, Bool.and_true, evalClause_singleton]
  constructor
  · rintro ⟨rfl, root⟩
    exact ⟨(root_eval formula input).symm.trans root, rfl⟩
  · rintro ⟨source, rfl⟩
    exact ⟨rfl, (root_eval formula input).trans source⟩

/-- Every target valuation is included: the statement is not restricted to
valuations preconstructed by the compiler. -/
theorem satisfiable_iff {n : Nat} (formula : Formula (Fin n)) :
    (∃ world, evalCNF (compile formula).asserted world = true) ↔
      ∃ input, eval input formula = true := by
  constructor
  · rintro ⟨world, holds⟩
    have reconstruct : read (world ∘ Sum.inl) (world ∘ Sum.inr) = world := by
      funext wire
      cases wire <;> rfl
    exact ⟨world ∘ Sum.inl, ((asserted_correct formula _ _).mp (reconstruct.symm ▸ holds)).1⟩
  · rintro ⟨input, holds⟩
    exact ⟨read input (realizeAux input formula), (asserted_correct formula _ _).mpr ⟨holds, rfl⟩⟩

/-! ## Size of the emitted representation -/

@[simp] theorem gateClauses_length {α : Type*} [DecidableEq α] (op : BinaryOp)
    (left right : Literal α) (output : α) : (gateClauses op left right output).length = 3 := by
  cases op <;> rfl

@[simp] theorem combine_length {n l r : Nat} (op : BinaryOp) (left : Encoding n l) (right : Encoding n r) :
    (combine op left right).clauses.length = left.clauses.length + right.clauses.length + 3 := by
  simp [combine, renameCNF, Nat.add_assoc]

theorem compile_length_le {n : Nat} (formula : Formula (Fin n)) :
    (compile formula).clauses.length ≤ 3 * auxCount formula := by
  induction formula with
  | hatom => simp [compile, auxCount]
  | hfalsum => norm_num [compile, auxCount]
  | _ => simp only [compile, auxCount, combine_length]; omega

theorem asserted_length_le {n : Nat} (formula : Formula (Fin n)) :
    (compile formula).asserted.length ≤ 3 * auxCount formula + 1 := by
  simpa only [Encoding.asserted, List.length_append, List.length_singleton] using
    Nat.add_le_add_right (compile_length_le formula) 1

private theorem pair_size {α : Type*} [DecidableEq α] (a b : α) : ({a, b} : Finset α).card ≤ 3 :=
  (Finset.card_insert_le _ _).trans (by simp)

private theorem triple_size {α : Type*} [DecidableEq α] (a b c : α) : ({a, b, c} : Finset α).card ≤ 3 := by
  apply (Finset.card_insert_le _ _).trans
  have pair := Finset.card_insert_le b ({c} : Finset α)
  simp only [Finset.card_singleton] at pair
  omega

theorem gateClauses_width {α : Type*} [DecidableEq α] (op : BinaryOp)
    (left right : Literal α) (output : α) :
    ∀ clause ∈ gateClauses op left right output, clause.card ≤ 3 := by
  intro clause member
  cases op <;> simp only [gateClauses, List.mem_cons, List.not_mem_nil, or_false] at member <;>
    rcases member with rfl | rfl | rfl
  all_goals first | exact pair_size _ _ | exact triple_size _ _ _

private theorem rename_width {α β : Type*} [DecidableEq β] (rename : α → β)
    (clauses : List (GroundClause α)) (bounded : ∀ clause ∈ clauses, clause.card ≤ 3) :
    ∀ clause ∈ renameCNF rename clauses, clause.card ≤ 3 := by
  intro clause member
  obtain ⟨original, originalMember, same⟩ :=
    List.mem_map.mp (show clause ∈ clauses.map (renameClause rename) from member)
  rw [← same]
  exact Finset.card_image_le.trans (bounded original originalMember)

private theorem combine_width {n l r : Nat} (op : BinaryOp)
    (left : Encoding n l) (right : Encoding n r)
    (leftBound : ∀ clause ∈ left.clauses, clause.card ≤ 3)
    (rightBound : ∀ clause ∈ right.clauses, clause.card ≤ 3) :
    ∀ clause ∈ (combine op left right).clauses, clause.card ≤ 3 := by
  intro clause member
  simp only [combine, List.mem_append] at member
  rcases member with (member | member) | member
  · exact rename_width _ _ leftBound clause member
  · exact rename_width _ _ rightBound clause member
  · exact gateClauses_width _ _ _ _ clause member

theorem compile_width {n : Nat} (formula : Formula (Fin n)) :
    ∀ clause ∈ (compile formula).clauses, clause.card ≤ 3 := by
  induction formula with
  | hatom => simp [compile]
  | hfalsum =>
    intro clause member
    have same : clause = {.neg (.inr (0 : Fin 1))} := List.mem_singleton.mp member
    rw [same]
    simp
  | hand a b ha hb => exact combine_width .and (compile a) (compile b) ha hb
  | hor a b ha hb => exact combine_width .or (compile a) (compile b) ha hb
  | himp a b ha hb => exact combine_width .imp (compile a) (compile b) ha hb

theorem asserted_width {n : Nat} (formula : Formula (Fin n)) :
    ∀ clause ∈ (compile formula).asserted, clause.card ≤ 3 := by
  intro clause member
  simp only [Encoding.asserted, List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact compile_width formula clause member
  · simp

end Mettapedia.Logic.PropositionalTseitin
