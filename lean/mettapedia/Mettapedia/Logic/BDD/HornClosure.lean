import Mettapedia.Logic.BDD.StatePredicates
import Mettapedia.Logic.LP.BackwardViaForward

/-!
# Symbolic closure of a finite Horn program

The leaves of a diagram describe the base facts in a world. One symbolic
round computes all Horn-rule bodies in the previous round and adds their
heads. Evaluating the resulting diagrams in a world agrees with ordinary
Horn saturation and with a completed demand chainer.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.BDDCore.HornClosure

open Mettapedia.Logic.LP
open StatePredicates

structure Clause (atoms : Nat) where
  head : Fin atoms
  body : List (Fin atoms)

def Clause.logical {atoms : Nat} (rule : Clause atoms) : PropRule (Fin atoms) :=
  ⟨rule.body.toFinset, rule.head⟩

def logical {atoms : Nat} (rules : List (Clause atoms)) : PropProgram (Fin atoms) :=
  (rules.map Clause.logical).toFinset

abbrev Table (n atoms : Nat) := Vector (Diagram n) atoms

variable {n atoms : Nat}

def bodyDiagram (table : Table n atoms) : List (Fin atoms) → Diagram n
  | [] => truth n
  | a :: rest => conj (table.get a) (bodyDiagram table rest)

def addHead (before after : Table n atoms) (rule : Clause atoms) : Table n atoms :=
  after.set rule.head.val (disj (after.get rule.head) (bodyDiagram before rule.body)) rule.head.isLt

def round (rules : List (Clause atoms)) (table : Table n atoms) : Table n atoms :=
  rules.foldl (addHead table) table

def iterate (rules : List (Clause atoms)) (initial : Table n atoms) : Nat → Table n atoms
  | 0 => initial
  | steps + 1 => round rules (iterate rules initial steps)

def compile (rules : List (Clause atoms)) (initial : Table n atoms) : Table n atoms :=
  iterate rules initial (atoms + 1)

def facts (table : Table n atoms) (world : Fin n → Bool) : Finset (Fin atoms) :=
  Finset.univ.filter fun a => (table.get a).val.eval world = true

@[simp] theorem mem_facts (table : Table n atoms) (world : Fin n → Bool) (a : Fin atoms) :
    a ∈ facts table world ↔ (table.get a).val.eval world = true := by
  simp [facts]

theorem bodyDiagram_eval (table : Table n atoms) (world : Fin n → Bool) (body : List (Fin atoms)) :
    (bodyDiagram table body).val.eval world =
      body.all (fun a => (table.get a).val.eval world) := by
  induction body with
  | nil => rfl
  | cons a rest ih => simp [bodyDiagram, conj, ih]

private theorem addHead_eval (before after : Table n atoms) (rule : Clause atoms)
    (world : Fin n → Bool) (a : Fin atoms) :
    ((addHead before after rule).get a).val.eval world =
      ((after.get a).val.eval world ||
        (decide (rule.head = a) && rule.body.all (fun b => (before.get b).val.eval world))) := by
  change ((after.set rule.head.val
    (disj (after.get rule.head) (bodyDiagram before rule.body)) rule.head.isLt)[a.val]).val.eval world = _
  rw [Vector.getElem_set]
  by_cases h : rule.head = a
  · subst a
    simp [disj, bodyDiagram_eval, Vector.get]
  · have neq : rule.head.val ≠ a.val := fun hval => h (Fin.ext hval)
    simp [h, neq, Vector.get]

private theorem fold_eval (rules : List (Clause atoms)) (before after : Table n atoms)
    (world : Fin n → Bool) (a : Fin atoms) :
    (((rules.foldl (addHead before) after).get a).val.eval world) =
      ((after.get a).val.eval world ||
        rules.any (fun rule => decide (rule.head = a) &&
          rule.body.all (fun b => (before.get b).val.eval world))) := by
  induction rules generalizing after with
  | nil => simp
  | cons rule rest ih => simp [ih, addHead_eval, Bool.or_assoc]

theorem round_facts (rules : List (Clause atoms)) (table : Table n atoms)
    (world : Fin n → Bool) :
    facts (round rules table) world = step (logical rules) (facts table world) := by
  ext a
  rw [mem_facts, round, fold_eval, step, Finset.mem_union, mem_fired_iff]
  simp [logical, Clause.logical, List.any_eq_true, List.all_eq_true, Finset.subset_iff, and_comm]

theorem iterate_facts (rules : List (Clause atoms)) (initial : Table n atoms)
    (world : Fin n → Bool) (steps : Nat) :
    facts (iterate rules initial steps) world =
      Mettapedia.Logic.LP.iterate (logical rules) (facts initial world) steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    rw [iterate, round_facts, ih, Mettapedia.Logic.LP.iterate]

theorem compiled_facts (rules : List (Clause atoms)) (initial : Table n atoms)
    (world : Fin n → Bool) :
    facts (compile rules initial) world = saturate (logical rules) (facts initial world) := by
  simp [compile, iterate_facts, saturate, maxSteps]

theorem compiled_demand (rules : List (Clause atoms)) (initial : Table n atoms)
    (world : Fin n → Bool) (query : Fin atoms) :
    ((compile rules initial).get query).val.eval world =
      demandChainerProves (logical rules) (facts initial world) query := by
  apply Bool.eq_iff_iff.mpr
  rw [← mem_facts, compiled_facts, saturate_iff_derivable, demandChainerProves_true_iff]

end Mettapedia.Logic.BDDCore.HornClosure
