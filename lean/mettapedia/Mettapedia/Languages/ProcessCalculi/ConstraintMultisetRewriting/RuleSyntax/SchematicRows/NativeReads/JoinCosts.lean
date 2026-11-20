import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.Enumeration
import Mettapedia.Machines.Cursor.EntryQueryTree
import Mathlib.Tactic

/-!
# Indexed joins preserve results; independent joins still have product output

The query evaluator is the existing sequential/union query tree. Pure index
exclusions remove only matcher calls known to return no result. The result
word, not just a set, is preserved. Fully independent read legs have the
stated product number of explicit results; a compressed observer may differ.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.JoinCosts

open Mettapedia.Machines.Cursor

variable {Pattern Row Env Key : Type}

def indexedMatch (keep : Pattern → Row → Env → Bool) (matchRow : Pattern → Row → Env → List Env)
    (pattern : Pattern) (row : Row) (env : Env) : List Env :=
  if keep pattern row env then matchRow pattern row env else []

theorem matcher_exact (keep : Pattern → Row → Env → Bool) (matchRow : Pattern → Row → Env → List Env)
    (complete : ∀ pattern row env, matchRow pattern row env ≠ [] → keep pattern row env = true) :
    indexedMatch keep matchRow = matchRow := by
  funext pattern row env
  by_cases accepted : keep pattern row env = true
  · simp [indexedMatch, accepted]
  · have empty : matchRow pattern row env = [] := by
      by_contra nonempty
      exact accepted (complete pattern row env nonempty)
    simp [indexedMatch, accepted, empty]

theorem indexed_query_word (keep : Pattern → Row → Env → Bool) (matchRow : Pattern → Row → Env → List Env)
    (complete : ∀ pattern row env, matchRow pattern row env ≠ [] → keep pattern row env = true)
    (entry : Key → List Row) (query : EntryQueryTree.Query Key Pattern) (env : Env) :
    EntryQueryTree.evaluate (indexedMatch keep matchRow) entry query env =
      EntryQueryTree.evaluate matchRow entry query env := by
  rw [matcher_exact keep matchRow complete]

theorem constant_fiber_length {A B : Type} (rows : List A) (fiber : A → List B) (n : Nat)
    (same : ∀ row ∈ rows, (fiber row).length = n) : (rows.flatMap fiber).length = rows.length * n := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [same row (List.mem_cons_self ..), ih (fun item member => same item (List.mem_cons_of_mem _ member))]
      ring

def independentQuery : Nat → EntryQueryTree.Query Unit Unit
  | 0 => .atom () ()
  | depth + 1 => .seq (independentQuery depth) (.atom () ())

def appendRow (_ : Unit) (row : Nat) (env : List Nat) : List (List Nat) := [env ++ [row]]

theorem independent_output_count (rows : List Nat) (depth : Nat) (env : List Nat) :
    (EntryQueryTree.evaluate appendRow (fun _ : Unit => rows) (independentQuery depth) env).length =
      rows.length ^ (depth + 1) := by
  induction depth generalizing env with
  | zero =>
      change (rows.flatMap (fun row => [env ++ [row]])).length = rows.length ^ 1
      rw [constant_fiber_length _ _ 1 (by simp)]
      simp
  | succ depth ih =>
      change ((EntryQueryTree.evaluate appendRow (fun _ : Unit => rows) (independentQuery depth) env).flatMap
        (EntryQueryTree.evaluate appendRow (fun _ : Unit => rows) (.atom () ()))).length = _
      rw [constant_fiber_length _ _ rows.length (by
        intro output _
        change (rows.flatMap (fun row => [output ++ [row]])).length = rows.length
        rw [constant_fiber_length _ _ 1 (by simp)]
        simp), ih, pow_succ]
      simp only [pow_succ]

#print axioms indexed_query_word
#print axioms independent_output_count

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.JoinCosts
