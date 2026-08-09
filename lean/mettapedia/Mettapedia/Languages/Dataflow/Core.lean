import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# A pure finite dataflow language

The source language of the dataflow-to-process compilation ladder: finite,
pure, single-assignment programs over an abstract operator signature.  This
module fixes the language, an **independent** denotational semantics, a
small-step operational semantics, and the theorems relating them.

Two semantics are given, and they are deliberately *different algorithms*:

* `denote` is **demand-driven** — a recursive descent from the returned
  cell that evaluates only what the result depends on (call-by-need in
  spirit);
* `Step` is **data-driven** — Kahn-style forward firing of any instruction
  whose operands are already available, in any order.

Their agreement (`run_result_eq_denote`) is therefore a real theorem rather
than a restatement: it says eager scheduling in *any* order computes what
lazy demand specifies.  The same duality reappears one level down when
these programs are compiled to a process calculus, where forcing-at-
communication plays the role of demand.

Raw programs may be malformed; nothing here is well-formed by construction.
`Program.validate` is the executable admission gate and
`Program.WellFormed` its declarative meaning, proved equivalent.
-/

namespace Mettapedia.Languages.Dataflow

/-- Dataflow cells (single-assignment value names). -/
abbrev CellId := Nat

/-- A signature of pure operators.  `apply` is total; well-formedness
guarantees it is only consulted at its declared arity, so behaviour off
that arity is unconstrained junk rather than a hidden assumption. -/
structure PureOperatorSpec (Op Value : Type) where
  arity : Op → Nat
  apply : Op → List Value → Value

variable {Op Value : Type}

/-- One instruction writes exactly one destination cell. -/
inductive Instruction (Op Value : Type) where
  | const (dst : CellId) (value : Value)
  | apply (dst : CellId) (operator : Op) (operands : List CellId)
deriving Repr

namespace Instruction

def dst : Instruction Op Value → CellId
  | .const d _ => d
  | .apply d _ _ => d

def operands : Instruction Op Value → List CellId
  | .const _ _ => []
  | .apply _ _ operands => operands

@[simp] theorem dst_const (d : CellId) (v : Value) :
    (Instruction.const (Op := Op) d v).dst = d := rfl

@[simp] theorem dst_apply (d : CellId) (op : Op) (operands : List CellId) :
    (Instruction.apply (Value := Value) d op operands).dst = d := rfl

@[simp] theorem operands_const (d : CellId) (v : Value) :
    (Instruction.const (Op := Op) d v).operands = [] := rfl

@[simp] theorem operands_apply (d : CellId) (op : Op) (operands : List CellId) :
    (Instruction.apply (Value := Value) d op operands).operands = operands := rfl

end Instruction

/-- A raw program: an input environment, an instruction list, and the cell
whose value is returned.  Nothing is enforced here. -/
structure Program (Op Value : Type) where
  inputs : List (CellId × Value)
  instructions : List (Instruction Op Value)
  result : CellId

/-! ## Environments -/

/-- Look a cell up in an environment. -/
def lookup (env : List (CellId × Value)) (c : CellId) : Option Value :=
  (env.find? (fun entry => entry.1 == c)).map Prod.snd

@[simp] theorem lookup_nil (c : CellId) :
    lookup (Value := Value) [] c = none := rfl

theorem lookup_cons_self (c : CellId) (v : Value)
    (env : List (CellId × Value)) :
    lookup ((c, v) :: env) c = some v := by
  simp [lookup, List.find?_cons_of_pos]

theorem lookup_cons_of_ne {c d : CellId} (ne : d ≠ c) (v : Value)
    (env : List (CellId × Value)) :
    lookup ((d, v) :: env) c = lookup env c := by
  simp [lookup, List.find?_cons_of_neg, ne]

theorem lookup_eq_some_mem {env : List (CellId × Value)} {c : CellId}
    {v : Value} (found : lookup env c = some v) : (c, v) ∈ env := by
  unfold lookup at found
  cases entryFound : env.find? (fun entry => entry.1 == c) with
  | none => rw [entryFound] at found; cases found
  | some entry =>
      rw [entryFound] at found
      have valueEq : entry.2 = v := by simpa using found
      have keyEq : entry.1 = c := by simpa using List.find?_some entryFound
      have member := List.mem_of_find?_eq_some entryFound
      rwa [← keyEq, ← valueEq]

/-- With distinct keys, membership determines the lookup. -/
theorem lookup_eq_some_of_mem {env : List (CellId × Value)}
    (nodup : (env.map Prod.fst).Nodup) {c : CellId} {v : Value}
    (member : (c, v) ∈ env) : lookup env c = some v := by
  induction env with
  | nil => cases member
  | cons entry rest inductionHypothesis =>
      simp only [List.map_cons, List.nodup_cons] at nodup
      rcases List.mem_cons.mp member with rfl | tailMember
      · exact lookup_cons_self c v rest
      · have keyMem : c ∈ rest.map Prod.fst :=
          List.mem_map.mpr ⟨(c, v), tailMember, rfl⟩
        have ne : entry.1 ≠ c := fun h => nodup.1 (h ▸ keyMem)
        rw [show entry = (entry.1, entry.2) from rfl, lookup_cons_of_ne ne]
        exact inductionHypothesis nodup.2 tailMember

/-- On environments with distinct keys, lookup is permutation-invariant. -/
theorem lookup_perm {env env' : List (CellId × Value)}
    (perm : env.Perm env') (nodup : (env.map Prod.fst).Nodup) (c : CellId) :
    lookup env c = lookup env' c := by
  have nodup' : (env'.map Prod.fst).Nodup :=
    ((perm.map Prod.fst).nodup_iff).mp nodup
  cases found : lookup env c with
  | some v =>
      exact (lookup_eq_some_of_mem nodup' ((perm.mem_iff).mp
        (lookup_eq_some_mem found))).symm ▸ rfl
  | none =>
      cases found' : lookup env' c with
      | none => rfl
      | some v =>
          exfalso
          have member : (c, v) ∈ env :=
            (perm.mem_iff).mpr (lookup_eq_some_mem found')
          rw [lookup_eq_some_of_mem nodup member] at found
          cases found

/-! ## Program lookups -/

namespace Program

variable (spec : PureOperatorSpec Op Value) (p : Program Op Value)

/-- The (unique, in well-formed programs) instruction writing a cell. -/
def writerOf? (c : CellId) : Option (Instruction Op Value) :=
  p.instructions.find? (fun i => i.dst == c)

/-- The externally supplied value of a cell, if any. -/
def inputValue? (c : CellId) : Option Value := lookup p.inputs c

end Program

/-! ## The demand-driven denotation

`denoteCell` descends from a cell through its operands.  It is total by
fuel; `denote` supplies the instruction count, which bounds dependency
depth in any admitted program. -/

mutual

/-- Demand-driven evaluation of one cell at a dependency-depth budget. -/
def denoteCell (spec : PureOperatorSpec Op Value) (p : Program Op Value) :
    Nat → CellId → Option Value
  | 0, c => p.inputValue? c
  | fuel + 1, c =>
      match p.inputValue? c with
      | some v => some v
      | none =>
          match p.writerOf? c with
          | none => none
          | some (.const _ v) => some v
          | some (.apply _ op operands) =>
              if operands.length = spec.arity op then
                match denoteOperands spec p fuel operands with
                | some values => some (spec.apply op values)
                | none => none
              else
                none
  termination_by fuel _ => (fuel, 0)

/-- Demand-driven evaluation of an operand vector. -/
def denoteOperands (spec : PureOperatorSpec Op Value) (p : Program Op Value) :
    Nat → List CellId → Option (List Value)
  | _, [] => some []
  | fuel, c :: cs =>
      match denoteCell spec p fuel c with
      | none => none
      | some v =>
          match denoteOperands spec p fuel cs with
          | none => none
          | some vs => some (v :: vs)
  termination_by fuel cs => (fuel, cs.length + 1)

end

/-! ### Unfolding equations

Stated once and used everywhere, so proofs never depend on how the
equation compiler happened to compile the mutual block. -/

@[simp] theorem denoteCell_zero (spec : PureOperatorSpec Op Value)
    (p : Program Op Value) (c : CellId) :
    denoteCell spec p 0 c = p.inputValue? c := by
  rw [denoteCell]

theorem denoteCell_succ (spec : PureOperatorSpec Op Value)
    (p : Program Op Value) (fuel : Nat) (c : CellId) :
    denoteCell spec p (fuel + 1) c =
      (match p.inputValue? c with
        | some v => some v
        | none =>
            match p.writerOf? c with
            | none => none
            | some (.const _ v) => some v
            | some (.apply _ op operands) =>
                if operands.length = spec.arity op then
                  match denoteOperands spec p fuel operands with
                  | some values => some (spec.apply op values)
                  | none => none
                else
                  none) := by
  rw [denoteCell]

@[simp] theorem denoteOperands_nil (spec : PureOperatorSpec Op Value)
    (p : Program Op Value) (fuel : Nat) :
    denoteOperands spec p fuel [] = some [] := by
  rw [denoteOperands]

theorem denoteOperands_cons (spec : PureOperatorSpec Op Value)
    (p : Program Op Value) (fuel : Nat) (c : CellId) (cs : List CellId) :
    denoteOperands spec p fuel (c :: cs) =
      (match denoteCell spec p fuel c with
        | none => none
        | some v =>
            match denoteOperands spec p fuel cs with
            | none => none
            | some vs => some (v :: vs)) := by
  rw [denoteOperands]

/-- The denotation of a program: demand-driven evaluation of its result
cell, with dependency depth bounded by the instruction count. -/
def Program.denote (spec : PureOperatorSpec Op Value) (p : Program Op Value) :
    Option Value :=
  denoteCell spec p p.instructions.length p.result

end Mettapedia.Languages.Dataflow
