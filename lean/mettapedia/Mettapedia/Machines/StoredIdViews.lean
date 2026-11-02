import Mettapedia.Machines.ShapeScopedUnification

/-!
# Stored IDs with frames and lazy substitutions

The operational reader exposes one constructor through IDs. Substitutions
remain closures around views; exposing an application propagates the closure
to its children without constructing a decoded term. Readback is used only
to state and prove the simulation. A faithful finite-term accessor is the
representation boundary; a concrete shared ID table instantiates it below.

This immutable reference does not model the native allocator, mutable cell
trail, unsupported grounded equality, or C pointer lifetimes.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.StoredIdViews

open ShapeStore ShapeScopedUnification
open Mettapedia.Logic.LP

variable {α Var Id : Type}

inductive Head (α Var Child : Type) where
  | atom (value : α)
  | cell (variableId : Var)
  | node (left right : Child)
  deriving DecidableEq

def rawMeaning (terms : Id → OpenTerm α Var) : Head α Var Id → OpenTerm α Var
  | .atom a => .atom (.inl a)
  | .cell v => .atom (.inr v)
  | .node l r => .node (terms l) (terms r)

structure Reader (α Var Id : Type) where
  inspect : Id → Head α Var Id
  source : Id → OpenTerm α Var
  faithful : ∀ id, rawMeaning source (inspect id) = source id

inductive View (Var Id : Type) where
  | cell (variableId : ScopedVar Var)
  | stored (id : Id) (frame : Nat)
  | subst (variableId : ScopedVar Var) (value body : View Var Id)
  deriving DecidableEq

def meaning [DecidableEq Var] (reader : Reader α Var Id) : View Var Id → LogicTerm α Var
  | .cell c => .var c
  | .stored id frame => encode frame (reader.source id)
  | .subst c value body =>
      (Subst.single c (meaning reader value)).applyTerm (meaning reader body)

def head [DecidableEq Var] (reader : Reader α Var Id) :
    View Var Id → Head α (ScopedVar Var) (View Var Id)
  | .cell c => .cell c
  | .stored id frame =>
      match reader.inspect id with
      | .atom a => .atom a
      | .cell v => .cell (ScopedVar.at frame v)
      | .node l r => .node (.stored l frame) (.stored r frame)
  | .subst c value body =>
      match head reader body with
      | .atom a => .atom a
      | .cell v => if v = c then head reader value else .cell v
      | .node l r => .node (.subst c value l) (.subst c value r)

def headMeaning [DecidableEq Var] (reader : Reader α Var Id) :
    Head α (ScopedVar Var) (View Var Id) → LogicTerm α Var
  | .atom a => .const a
  | .cell c => .var c
  | .node l r => pair (meaning reader l) (meaning reader r)

theorem head_correct [DecidableEq Var] (reader : Reader α Var Id) (v : View Var Id) :
    headMeaning reader (head reader v) = meaning reader v := by
  induction v with
  | cell c => rfl
  | stored id frame =>
      change headMeaning reader (head reader (.stored id frame)) = encode frame (reader.source id)
      rw [← reader.faithful id]
      cases found : reader.inspect id <;> simp [head, headMeaning, rawMeaning, meaning, encode, found]
  | subst c value body ihvalue ihbody =>
      cases hbody : head reader body with
      | atom a =>
          have source : meaning reader body = .const a := by
            simpa [hbody, headMeaning] using ihbody.symm
          simp [head, hbody, headMeaning, meaning, source]
      | cell v =>
          have source : meaning reader body = .var v := by
            simpa [hbody, headMeaning] using ihbody.symm
          by_cases same : v = c
          · simp [head, hbody, same, meaning, source, Subst.single, ihvalue]
          · simp [head, hbody, same, headMeaning, meaning, source, Subst.single]
      | node l r =>
          have source : meaning reader body = pair (meaning reader l) (meaning reader r) := by
            simpa [hbody, headMeaning] using ihbody.symm
          simp [head, hbody, headMeaning, meaning, source, apply_pair]

theorem left_smaller [DecidableEq Var] (reader : Reader α Var Id) (v l r : View Var Id)
    (exposed : head reader v = .node l r) : (meaning reader l).size < (meaning reader v).size := by
  have semantic := head_correct reader v
  rw [exposed] at semantic
  rw [← semantic]
  exact Term.size_subterm (σ := signature α Var) (f := ())
    (ts := ![meaning reader l, meaning reader r]) 0

theorem right_smaller [DecidableEq Var] (reader : Reader α Var Id) (v l r : View Var Id)
    (exposed : head reader v = .node l r) : (meaning reader r).size < (meaning reader v).size := by
  have semantic := head_correct reader v
  rw [exposed] at semantic
  rw [← semantic]
  exact Term.size_subterm (σ := signature α Var) (f := ())
    (ts := ![meaning reader l, meaning reader r]) 1

/-- Readback size is a proof of termination, not a traversal performed by
the operational body. Occurrence testing reads only exposed heads and IDs. -/
def occurs [DecidableEq Var] (reader : Reader α Var Id) (c : ScopedVar Var)
    (v : View Var Id) : Bool :=
  match _exposed : head reader v with
  | .cell other => c == other
  | .atom _ => false
  | .node l r => occurs reader c l || occurs reader c r
termination_by (meaning reader v).size
decreasing_by
  · exact left_smaller reader v l r _exposed
  · exact right_smaller reader v l r _exposed

theorem occurs_pair [DecidableEq Var] (c : ScopedVar Var) (l r : LogicTerm α Var) :
    (pair l r).occursIn c = (l.occursIn c || r.occursIn c) := by
  simp [pair, Term.occursIn, List.finRange_succ]

theorem occurs_correct [DecidableEq Var] (reader : Reader α Var Id) (c : ScopedVar Var)
    (v : View Var Id) : occurs reader c v = (meaning reader v).occursIn c := by
  rw [occurs]
  have semantic := head_correct reader v
  cases exposed : head reader v with
  | atom a => simp [exposed, headMeaning] at semantic; rw [← semantic]; rfl
  | cell other => simp [exposed, headMeaning] at semantic; rw [← semantic]; rfl
  | node l r =>
      simp [exposed, headMeaning] at semantic
      simp only
      rw [← semantic, occurs_pair, occurs_correct reader c l, occurs_correct reader c r]
termination_by (meaning reader v).size
decreasing_by
  · exact left_smaller reader v l r exposed
  · exact right_smaller reader v l r exposed

abbrev Equations (Var Id : Type) := List (View Var Id × View Var Id)

def readEquations [DecidableEq Var] (reader : Reader α Var Id) (eqs : Equations Var Id) :
    List (LogicTerm α Var × LogicTerm α Var) :=
  eqs.map fun p => (meaning reader p.1, meaning reader p.2)

/-- Wrapping pending operands keeps substitutions lazy. No source term is copied. -/
def substitute (c : ScopedVar Var) (value : View Var Id) (eqs : Equations Var Id) : Equations Var Id :=
  eqs.map fun p => (.subst c value p.1, .subst c value p.2)

theorem substitute_correct [DecidableEq Var] (reader : Reader α Var Id)
    (c : ScopedVar Var) (value : View Var Id) (eqs : Equations Var Id) :
    readEquations reader (substitute c value eqs) =
      (Subst.single c (meaning reader value)).applyEqs (readEquations reader eqs) := by
  simp [readEquations, substitute, Subst.applyEqs, meaning, List.map_map]

namespace Controls

def inspect : Nat → Head Bool Nat Nat
  | 0 => .cell 0
  | 1 => .atom false
  | 2 => .node 0 1
  | 3 => .node 2 2
  | _ => .atom true

def source : Nat → OpenTerm Bool Nat
  | 0 => .atom (.inr 0)
  | 1 => .atom (.inl false)
  | 2 => .node (.atom (.inr 0)) (.atom (.inl false))
  | 3 => .node (.node (.atom (.inr 0)) (.atom (.inl false)))
      (.node (.atom (.inr 0)) (.atom (.inl false)))
  | _ => .atom (.inl true)

/-- Two parents share ID 2, and ID 0 is a variable, not a rigid symbol. -/
def reader : Reader Bool Nat Nat where
  inspect := inspect
  source := source
  faithful := by
    intro id
    rcases id with _ | _ | _ | _ | id <;> rfl

example : head reader (.stored 3 7) = .node (.stored 2 7) (.stored 2 7) := rfl
example : head reader (.subst ⟨7, 0⟩ (.stored 1 8) (.stored 0 7)) = .atom false := by decide
example : head reader (.subst ⟨7, 0⟩ (.stored 1 8) (.stored 0 8)) = .cell ⟨8, 0⟩ := by decide
example : occurs reader ⟨7, 0⟩ (.stored 3 7) = true := by rw [occurs_correct]; decide
example : occurs reader ⟨8, 0⟩ (.stored 3 7) = false := by rw [occurs_correct]; decide

end Controls

#print axioms head_correct
#print axioms occurs_correct
#print axioms substitute_correct

end Mettapedia.Machines.StoredIdViews
