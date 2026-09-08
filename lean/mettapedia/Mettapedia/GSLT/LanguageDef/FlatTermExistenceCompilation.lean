import Mettapedia.GSLT.LanguageDef.FlatTermViewCompilation
import Mettapedia.GSLT.LanguageDef.FiniteGroundFactIndexCompilation

/-!
# Flat term views composed with exact existence indexes

This module composes two independent refinements: an evaluator presents a
suspended term through an exact borrowed root projection, and storage answers
existence through an exact rigid-leaf index.  Their common boundary is the
Boolean `Any` collapse algebra, not an evaluator syntax or machine state.

The resulting index can therefore be reused by any evaluator representation
which implements `RootProjection.Algebra`.  Conversely, the evaluator-side
projection proof is unchanged if a hash table, trie, relation, or another
physical membership index replaces the finite-list model used here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.FlatTermExistenceCompilation

open Mettapedia.GSLT.Dynamics.Collapse
open Mettapedia.GSLT.LanguageDef.FlatTermViewCompilation
open Mettapedia.GSLT.LanguageDef.FiniteGroundFactIndexCompilation
open Mettapedia.GSLT.Parsing.HornCertificate

/-- Present ordinary answers as positive unit-multiplicity observations. -/
def positiveRows {Answer : Type}
    (answers : List Answer) : List (Obs Answer Unit) :=
  answers.map fun answer =>
    { answer := answer, multiplicity := 1, receipt := () }

/-- The `Any` fold of positive unit rows is exactly list nonemptiness. -/
theorem collapseAny_positiveRows {Answer : Type} (answers : List Answer) :
    collapseWith (AnyAlg Answer Unit) (positiveRows answers) =
      !answers.isEmpty := by
  induction answers with
  | nil => rfl
  | cons answer rest inductionHypothesis =>
      simp [positiveRows, collapseWith, foldStream, AnyAlg]

/-- Filtering and the corresponding payload-producing scan are empty under
exactly the same condition. -/
theorem sourceMatches_isEmpty_eq_filter_isEmpty
    {Payload : Type} (accepts : GroundFact Payload → Bool)
    (facts : List (GroundFact Payload)) :
    (sourceMatches accepts facts).isEmpty =
      (facts.filter accepts).isEmpty := by
  induction facts with
  | nil => rfl
  | cons fact facts inductionHypothesis =>
      by_cases accepted : accepts fact = true
      · simp [sourceMatches, accepted]
      · have rejected : accepts fact = false :=
          Bool.eq_false_of_not_eq_true accepted
        simp [sourceMatches, rejected, inductionHypothesis]

/-- Physical Boolean stored at an exact rigid leaf.  Duplicate occurrences
remain visible to counting, but existence deliberately quotients every
positive multiplicity to one witness. -/
def rigidLeafExists {Payload : Type} (query : GroundTerm)
    (facts : List (GroundFact Payload)) : Bool :=
  !(facts.filter (exactCoordinate query)).isEmpty

/-- Exact-leaf membership implements the semantic `Any` fold over a complete
scan of the provider. -/
theorem rigidLeafExists_exact {Payload : Type} (query : GroundTerm)
    (facts : List (GroundFact Payload)) :
    rigidLeafExists query facts =
      collapseWith (AnyAlg Payload Unit)
        (positiveRows (sourceMatches (exactCoordinate query) facts)) := by
  rw [collapseAny_positiveRows,
    sourceMatches_isEmpty_eq_filter_isEmpty]
  rfl

/-- The finite ground provider instantiates the evaluator-independent exact
existence-index interface. -/
def rigidLeafExistenceIndex {Payload : Type}
    (facts : List (GroundFact Payload)) :
    RootProjection.ExistenceIndex GroundTerm Payload Unit where
  observations query :=
    positiveRows (sourceMatches (exactCoordinate query) facts)
  contains query := rigidLeafExists query facts
  exact query := rigidLeafExists_exact query facts

/-! ## Positive and negative controls -/

private def duplicateFacts : List (GroundFact String) :=
  [{ coordinate := .app "edge" (.ofList [.atom "a", .atom "b"]),
      payload := "first" },
   { coordinate := .app "edge" (.ofList [.atom "a", .atom "b"]),
      payload := "second" },
   { coordinate := .app "edge" (.ofList [.atom "a", .atom "c"]),
      payload := "other" }]

/-- Positive: either duplicate occurrence is enough to witness existence. -/
example :
    (rigidLeafExistenceIndex duplicateFacts).contains
      (.app "edge" (.ofList [.atom "a", .atom "b"])) = true := by
  decide

/-- Negative: a missing rigid coordinate is observed as false. -/
example :
    (rigidLeafExistenceIndex duplicateFacts).contains
      (.app "edge" (.ofList [.atom "missing", .atom "path"])) = false := by
  decide

/-- Existence and occurrence counting are intentionally distinct observers:
two equal facts produce one Boolean witness but retain count two. -/
example :
    (rigidLeafExistenceIndex duplicateFacts).contains
        (.app "edge" (.ofList [.atom "a", .atom "b"])) = true ∧
      rigidLeafCount
        (.app "edge" (.ofList [.atom "a", .atom "b"])) duplicateFacts = 2 := by
  decide

#print axioms collapseAny_positiveRows
#print axioms sourceMatches_isEmpty_eq_filter_isEmpty
#print axioms rigidLeafExists_exact
#print axioms rigidLeafExistenceIndex

end Mettapedia.GSLT.LanguageDef.FlatTermExistenceCompilation
