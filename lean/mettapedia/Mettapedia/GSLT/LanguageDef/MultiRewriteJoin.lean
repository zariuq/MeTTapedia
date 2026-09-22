import Mettapedia.OSLF.MeTTaIL.Match

/-!
# Joins on the commutative rung

A join is one substitution shared across several source patterns.  The
engine already implements that as `mergeBindingsWith` plus bag matching
(`matchBagWith` on `CollType.hashBag`).  This module names the substitution
and records the two controls:

* the same metavariable on two sources succeeds only when the images agree;
* distinct names do not conflict.

The COMM-shaped canary is that control on a shared channel name `n`:
recv-bindings and send-bindings join when the channel images agree, and
fail when they do not.  That is not rho COMM — the process grammar and
`...rest` are still missing.  The join becomes a multi-rewrite denotation
in `MultiRewriteSchematic`, still not a rho COMM modality.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.MultiRewriteJoin

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

def syntacticEq (a b : Pattern) : Bool := decide (a = b)

/-- Ordered join of two source matches. -/
def mergeJoin (first second : Bindings) : Option Bindings :=
  mergeBindingsWith syntacticEq first second

/-- Bag join: consume every pattern in some order, one substitution.
Well-founded bag search is the existing matcher; the substitution law
proved below is `mergeJoin`. -/
def joinBag (patterns terms : List Pattern) : List Bindings :=
  matchBagWith syntacticEq patterns none CollType.hashBag terms

theorem mergeJoin_same_key_agree (name : String) (value : Pattern) :
    mergeJoin [(name, value)] [(name, value)] = some [(name, value)] := by
  unfold mergeJoin mergeBindingsWith
  simp [List.foldlM, Option.bind, syntacticEq]

theorem mergeJoin_same_key_disagree
    (name : String) {left right : Pattern} (hne : left ≠ right) :
    mergeJoin [(name, left)] [(name, right)] = none := by
  unfold mergeJoin mergeBindingsWith
  simp [List.foldlM, Option.bind, syntacticEq, decide_eq_false hne]

private theorem find_singleton_other
    {leftName rightName : String} {left : Pattern}
    (hne : leftName ≠ rightName) :
    List.find? (fun p => p.1 == rightName) [(leftName, left)] = none := by
  simp [List.find?, BEq.beq, decide_eq_false hne]

theorem mergeJoin_distinct_names
    {leftName rightName : String} {left right : Pattern}
    (hne : leftName ≠ rightName) :
    mergeJoin [(leftName, left)] [(rightName, right)] =
      some ((rightName, right) :: [(leftName, left)]) := by
  unfold mergeJoin mergeBindingsWith
  simp [List.foldlM, Option.bind, find_singleton_other hne]

/-! ## Channel `n` across two sources

The substitution that COMM needs: one name, one image.  The two source
matches are already computed; the join is their merge.
-/

private def chA : Pattern := .apply "A" []
private def chB : Pattern := .apply "B" []
private def bodyP : Pattern := .apply "P" []
private def bodyQ : Pattern := .apply "Q" []

private theorem chA_ne_chB : chA ≠ chB := by
  decide

theorem mergeJoin_comm_same_channel :
    mergeJoin [("n", chA), ("x", bodyP)] [("n", chA), ("q", bodyQ)] =
      some [("q", bodyQ), ("n", chA), ("x", bodyP)] := by
  unfold mergeJoin mergeBindingsWith
  simp [List.foldlM, Option.bind, syntacticEq]

theorem mergeJoin_comm_mismatch :
    mergeJoin [("n", chA), ("x", bodyP)] [("n", chB), ("q", bodyQ)] = none := by
  unfold mergeJoin mergeBindingsWith
  simp [List.foldlM, Option.bind, syntacticEq, decide_eq_false chA_ne_chB]

/-- Rest binder absent: leftover terms are refused. -/
theorem unused_rest_none_refuses_leftover :
    matchBagWith syntacticEq [] none CollType.hashBag [chA] = [] := by
  simp [matchBagWith]

/-- An unused rest variable on an empty leftover binds the empty collection. -/
theorem unused_rest_binds_empty :
    matchBagWith syntacticEq [] (some "r") CollType.hashBag [] =
      [[("r", .collection CollType.hashBag [] none)]] := by
  simp [matchBagWith]

/-- That rest binding does not conflict with a disjoint channel join. -/
theorem unused_rest_ignored_by_join :
    mergeJoin [("r", .collection CollType.hashBag [] none)] [("n", chA)] =
      some [("n", chA), ("r", .collection CollType.hashBag [] none)] := by
  unfold mergeJoin mergeBindingsWith
  simp [List.foldlM, Option.bind]

#print axioms mergeJoin_same_key_agree
#print axioms mergeJoin_same_key_disagree
#print axioms mergeJoin_distinct_names
#print axioms mergeJoin_comm_same_channel
#print axioms mergeJoin_comm_mismatch
#print axioms unused_rest_none_refuses_leftover
#print axioms unused_rest_binds_empty
#print axioms unused_rest_ignored_by_join

end Mettapedia.GSLT.LanguageDef.MultiRewriteJoin
