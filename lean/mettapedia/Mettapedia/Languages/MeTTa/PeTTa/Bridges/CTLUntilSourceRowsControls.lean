import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceCapture
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilDriverControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NamedPresenceSource

/-! Duplicate row coordinates, alias-safe capture and the distinction between
eight producer occurrences and one newly admitted frontier value. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceRows.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (applySubst)
open EagerDFS.Destination

def fronts : List (String × Nat × Nat) := [("f", 0, 2), ("f", 1, 2), ("f", 0, 2)]
def edges : List (Nat × Nat) := [(1, 2), (99, 7), (1, 2)]
def holds : List (String × Nat) := [("a", 1), ("other", 1), ("a", 1)]
def selected := sourceCandidates "f" 0 "a" "next" "prior" fronts edges holds

theorem eight_distinct_occurrence_coordinates :
    selected.map (fun row => (row.frontierOccurrence, row.edgeOccurrence, row.predicateOccurrence)) =
      [(0, 0, 0), (0, 0, 2), (0, 2, 0), (0, 2, 2),
       (2, 0, 0), (2, 0, 2), (2, 2, 0), (2, 2, 2)] := by decide +kernel

theorem eight_producers_one_value :
    selected.map (fun row => applySubst row.bindings (.var "prior")) =
      List.replicate 8 (number 1) := by decide +kernel

theorem variable_aliasing_is_not_a_renaming :
    sourceCandidates "f" 0 "a" "same" "same" fronts edges holds = [] := by decide +kernel

def candidates : List Nat := Mettapedia.Machines.CTLUntilCandidateBag.candidates edges
  (CTLPreimageSource.operand "a" holds) (frontierNodes "f" 0 fronts)
theorem fresh_count_is_not_producer_count :
    candidates.length = 8 ∧
      Mettapedia.Machines.CTLUntilCandidateBag.fresh candidates ∅ = [1] ∧
      Mettapedia.Machines.CTLUntilCandidateBag.fresh candidates {1} = [] := by decide +kernel

def capturedCaller : Control := {
  bindings := [(.var "next", .var "shared"), (.var "kept", number 9)]
  goals := [.evaluate (.var "kept") (.var "answer")]
  destination := .var "answer" }
def body : Atom := .expression [.symbol "quote", .expression [.var "next", .var "kept"]]
def captured := ScopedQuerySource.capture capturedCaller (frontier "f" 0 (.var "next")) body
  (.var "out") capturedCaller.goals 0 (frontierRows fronts)

#guard captured.map (fun rows => rows.map Prod.fst) == some [0, 2]
#guard captured.map (fun rows => rows.all (fun row =>
  row.2.bindings == capturedCaller.bindings ++ [(.var "next", number 2)] &&
  row.2.goals == .evaluate body (.var "out") :: capturedCaller.goals)) == some true

def outerBindings := ScopedQuerySource.extend capturedCaller.bindings [("next", number 2)]
def innerBindings := ScopedQuerySource.extend outerBindings [("prior", number 1)]
#guard (resolve outerBindings).map (fun principal => read principal (reversePattern "next" "prior")) ==
  some (CTLUntilSourceCapture.preparedEdge 2 "prior")
#guard (resolve innerBindings).map (fun principal => read principal (satPattern "a" "prior")) ==
  some (CTLUntilSourceCapture.preparedSatisfaction "a" 1)
#guard (resolve innerBindings).map (fun principal => read principal (.var "shared")) == some (number 2)

def correlatedBindings := ScopedQuerySource.extend [(.var "prior", .var "next")] [("next", number 2)]
#guard (resolve correlatedBindings).map (fun principal => read principal (reversePattern "next" "prior")) !=
  some (CTLUntilSourceCapture.preparedEdge 2 "prior")

-- A bound slot is a real constraint, not a fresh binder that may be replaced.
def constrained : Control := {capturedCaller with bindings := [(.var "next", number 7)]}
#guard (ScopedQuerySource.capture constrained (frontier "f" 0 (.var "next")) body
  (.var "out") [] 0 (frontierRows fronts)).isNone

-- A literal predicate query adds no equations, but keeps both occurrences.
def satisfied := ScopedQuerySource.capture capturedCaller
  (CTLUntilSourceCapture.preparedSatisfaction "a" 1) body (.var "out") [] 0 (satisfactionRows holds)
#guard satisfied.map (fun rows => rows.map Prod.fst) == some [0, 2]
#guard satisfied.map (fun rows => rows.all (fun row => row.2.bindings == capturedCaller.bindings)) == some true

#print axioms candidate_values
#print axioms ScopedQuerySource.capture_of_consistent_matches
#print axioms CTLUntilSourceCapture.frontier_entry
#print axioms CTLUntilSourceCapture.edge_entry
#print axioms CTLUntilSourceCapture.satisfaction_entry
#print axioms CTLUntilSourceCapture.edge_pattern_after_frontier
#print axioms CTLUntilSourceCapture.satisfaction_pattern_after_edge

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceRows.Controls
