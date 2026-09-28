import Mettapedia.GSLT.Parsing.PlainBnfReferenceSourceAdmission
import Mettapedia.GSLT.Parsing.SourceSExprPatternInstantiation
import Mathlib.Data.List.Basic

/-!
# FIFO refinement for the authored BNF reachability transformation

The abstract machine compares an append-based FIFO with a two-list FIFO,
including the exact pending sequence and visited order at every bounded prefix.
Duplicate edges are not erased. The source checks select the concrete enqueue,
rotation and accumulator rules from the live authored presentation.

These are queue refinement and source-instantiation theorems, not a theorem
about the entire generated PeTTa evaluator or its resource behavior.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfReachableQueue

variable {α : Type}

structure Queue (α : Type) where
  front : List α
  back : List α
  deriving Repr, DecidableEq

def contents (queue : Queue α) : List α := queue.front ++ queue.back.reverse

/-- The accumulator traverses new references, not the pending front. -/
def reverseOnto : List α → List α → List α
  | [], tail => tail
  | head :: rest, tail => reverseOnto rest (head :: tail)

theorem reverseOnto_exact (items tail : List α) :
    reverseOnto items tail = items.reverse ++ tail := by
  induction items generalizing tail with
  | nil => rfl
  | cons head rest ih => simp [reverseOnto, ih]

def enqueue (queue : Queue α) (items : List α) : Queue α :=
  ⟨queue.front, reverseOnto items queue.back⟩

theorem enqueue_contents (queue : Queue α) (items : List α) :
    contents (enqueue queue items) = contents queue ++ items := by
  simp [contents, enqueue, reverseOnto_exact, List.append_assoc]

def pop (queue : Queue α) : Option (α × Queue α) :=
  match queue.front with
  | head :: rest => some (head, ⟨rest, queue.back⟩)
  | [] => match queue.back.reverse with
    | [] => none
    | head :: rest => some (head, ⟨rest, []⟩)

theorem pop_contents (queue : Queue α) :
    (match pop queue with
      | none => []
      | some (head, rest) => head :: contents rest) = contents queue := by
  rcases queue with ⟨front, back⟩
  cases front with
  | cons head rest => rfl
  | nil => cases h : back.reverse <;> simp [pop, h, contents]

variable [DecidableEq α]

/-- Independently stated old FIFO traversal; fuel counts dequeued occurrences,
not grammar nodes or interpreter reductions. Exhaustion retains pending work. -/
def reference (edges : α → List α) : Nat → List α → List α → List α × List α
  | 0, pending, visited => (pending, visited)
  | _ + 1, [], visited => ([], visited)
  | fuel + 1, head :: rest, visited =>
    if head ∈ visited then reference edges fuel rest visited
    else reference edges fuel (rest ++ edges head) (visited ++ [head])

def queued (edges : α → List α) : Nat → Queue α → List α → List α × List α
  | 0, queue, visited => (contents queue, visited)
  | fuel + 1, queue, visited =>
    match pop queue with
    | none => ([], visited)
    | some (head, rest) =>
      if head ∈ visited then queued edges fuel rest visited
      else queued edges fuel (enqueue rest (edges head)) (visited ++ [head])

/-- Exact prefix equivalence includes remaining work, not just a set of names
or an eventual success bit. Cycles and repeated references are allowed. -/
theorem queued_reference (edges : α → List α) (fuel : Nat)
    (queue : Queue α) (visited : List α) :
    queued edges fuel queue visited = reference edges fuel (contents queue) visited := by
  induction fuel generalizing queue visited with
  | zero => rfl
  | succ fuel ih =>
    have view := pop_contents queue
    cases h : pop queue with
    | none =>
      simp only [h] at view
      simp [queued, h, ← view, reference]
    | some pair =>
      rcases pair with ⟨head, rest⟩
      simp only [h] at view
      simp only [queued, h, ← view, reference]
      split <;> simp [ih, enqueue_contents]

theorem repeated_edges_retained :
    contents (enqueue (⟨[0], [2, 1]⟩ : Queue Nat) [3, 3]) = [0, 1, 2, 3, 3] := rfl

theorem forgetting_back_reversal_is_wrong :
    ([0] ++ ([2, 1] ++ [3, 4]).reverse : List Nat) ≠
      contents (enqueue (⟨[0], [2, 1]⟩ : Queue Nat) [3, 4]) := by decide

section Source

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT (Rewrite)
open PlainBnfReferenceSourceAdmission (graphSource)
open SourceSExprPatternInstantiation (Env instantiate? instantiateList?)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

def instantiatedRule? (occurrence : Nat) (env : Env) : Option (SExpr × List SExpr) := do
  let row ← graphSource.rewrites[occurrence]?
  return (← instantiate? env row.head, ← instantiateList? env row.body)

def app (head : String) (args : List SExpr) : SExpr := .list (.atom head :: args)

def names : List SExpr → SExpr
  | [] => .atom "BNFNamesNilV1"
  | head :: tail => app "BNFNamesConsV1" [head, names tail]

private theorem reverse_nil_shape : graphSource.rewrites[95]? = some
    ⟨"bnf-reachable-reverse-nil-v1",
      metta_sexpr% petta "(BNFReachableReverseV1 BNFNamesNilV1 ?tail ?tail)", []⟩ := rfl

private theorem reverse_cons_shape : graphSource.rewrites[96]? = some
    ⟨"bnf-reachable-reverse-cons-v1",
      metta_sexpr% petta "(BNFReachableReverseV1 (BNFNamesConsV1 ?head ?rest) ?tail ?result)",
      [metta_sexpr% petta "(BNFReachableReverseV1 ?rest (BNFNamesConsV1 ?head ?tail) ?result)"]⟩ := rfl

theorem reverse_nil_source (tail : List SExpr) :
    instantiatedRule? 95 [("?tail", names tail)] =
      some (app "BNFReachableReverseV1" [names [], names tail, names tail], []) := by
  simp [instantiatedRule?, reverse_nil_shape, instantiate?, instantiateList?, names, app,
    SourceIntegerProvider.sourceVariableToken]

theorem reverse_cons_source (head : SExpr) (rest tail : List SExpr) (result : SExpr) :
    instantiatedRule? 96 [("?head", head), ("?rest", names rest), ("?tail", names tail), ("?result", result)] =
      some (app "BNFReachableReverseV1" [names (head :: rest), names tail, result],
        [app "BNFReachableReverseV1" [names rest, names (head :: tail), result]]) := by
  simp [instantiatedRule?, reverse_cons_shape, instantiate?, instantiateList?, names, app,
    SourceIntegerProvider.sourceVariableToken]

/-- The source really enqueues references onto the reverse back, and carries
the untouched front into the recursive call. These are not assumed hooks. -/
theorem enqueue_source_body : (graphSource.rewrites[19]?).map Rewrite.body = some [
    metta_sexpr% petta "(BNFDefinitionLookupV1 ?name ?definitions (BNFDefinitionFoundV1 ?expression ?span))",
    metta_sexpr% petta "(BNFCollectExpressionReferencesV1 ?expression ?lexicals ?references)",
    metta_sexpr% petta "(BNFReachableReverseV1 ?references ?back ?nextBack)",
    metta_sexpr% petta "(BNFAppendNameV1 ?visited ?name ?nextVisited)",
    metta_sexpr% petta "(BNFReachableQueueV1 ?rest ?nextBack ?definitions ?lexicals ?nextVisited ?reachable)"] := rfl

theorem rotation_source : graphSource.rewrites[94]? = some
    ⟨"bnf-reachable-queue-rotate-v1",
      metta_sexpr% petta "(BNFReachableQueueV1 BNFNamesNilV1 (BNFNamesConsV1 ?head ?tail) ?definitions ?lexicals ?visited ?result)",
      [metta_sexpr% petta "(BNFReachableReverseV1 (BNFNamesConsV1 ?head ?tail) BNFNamesNilV1 ?front)",
       metta_sexpr% petta "(BNFReachableQueueV1 ?front BNFNamesNilV1 ?definitions ?lexicals ?visited ?result)"]⟩ := rfl

end Source

#print axioms queued_reference
#print axioms reverse_cons_source
#print axioms enqueue_source_body

end Mettapedia.GSLT.Parsing.PlainBnfReachableQueue
