import Mettapedia.GSLT.Core.InferenceControl

/-!
# Selection, expansion, and analysis

One controlled inference step has three distinct responsibilities:

1. a scheduler selects one authorized live occurrence;
2. an expansion realization computes that occurrence's emission and forward
   successors;
3. the controller analyzes the exact expansion and updates only its memory.

The branching system remains the semantic authority for expansion.  A native
index, including a PathMap-backed implementation, may replace the reference
calls only through `ExpansionRealization`, whose exactness law preserves the
selected occurrence, emission, successor order, and multiplicity.

Branch restoration is deliberately absent from this interface.  It may use
full images, shared roots, deltas, or replay trails independently of how
forward expansion is accelerated.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.SelectionExpansionAnalysis

open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.InferenceControl

universe uNode uAnswer uMemory

variable {Node : Type uNode} {Answer : Type uAnswer} {Memory : Type uMemory}

/-- The exact observable result of expanding one selected occurrence. -/
structure Expansion (Node : Type uNode) (Answer : Type uAnswer) where
  selected : Node
  emission : Option Answer
  successors : List Node
deriving Repr

/-- The specification expansion supplied by the branching authority. -/
def semanticExpansion (system : BranchingSystem Node Answer) (node : Node) :
    Expansion Node Answer :=
  { selected := node
    emission := system.emit node
    successors := system.successors node }

/-- An optimized forward-expansion engine together with exact adequacy to the
branching authority.  This is the admission boundary for a native index. -/
structure ExpansionRealization (system : BranchingSystem Node Answer) where
  expand : Node -> Expansion Node Answer
  exact : forall node, expand node = semanticExpansion system node

namespace ExpansionRealization

variable {Node : Type uNode} {Answer : Type uAnswer}

/-- The direct reference realization. -/
def reference (system : BranchingSystem Node Answer) :
    ExpansionRealization system where
  expand := semanticExpansion system
  exact _ := rfl

end ExpansionRealization

/-- Controller analysis consumes an already-authorized expansion.  It cannot
change the emission or successor list recorded in that expansion. -/
def analyze (controller : Controller Node Answer Memory) (memory : Memory)
    (expansion : Expansion Node Answer) : Memory :=
  controller.advance memory expansion.selected expansion.emission
    expansion.successors

private def eventFor (node : Node) :
    Option Answer -> List (Emission Node Answer)
  | none => []
  | some answer => [⟨node, answer⟩]

/-- Execute select -> expand -> analyze using an admitted expansion
realization.  Reordering and frontier integration remain scheduler concerns;
the realization supplies only the selected occurrence's forward expansion. -/
def tickWith (system : BranchingSystem Node Answer)
    (realization : ExpansionRealization system)
    (controller : Controller Node Answer Memory)
    (snapshot : InferenceControl.Snapshot Node Answer Memory) :
    InferenceControl.Snapshot Node Answer Memory :=
  let scheduler := controller.scheduler snapshot.memory
  match scheduler.reorder snapshot.search.frontier with
  | [] => snapshot
  | node :: pending =>
      let expansion := realization.expand node
      { search :=
          { events := snapshot.search.events ++
              eventFor expansion.selected expansion.emission
            frontier := scheduler.integrate pending expansion.successors }
        memory := analyze controller snapshot.memory expansion }

/-- Any admitted expansion realization executes exactly the existing
controller semantics.  Native forward indexing is therefore invisible at
this boundary. -/
theorem tickWith_eq_tick
    (system : BranchingSystem Node Answer)
    (realization : ExpansionRealization system)
    (controller : Controller Node Answer Memory)
    (snapshot : InferenceControl.Snapshot Node Answer Memory) :
    tickWith system realization controller snapshot =
      InferenceControl.Snapshot.tick system controller snapshot := by
  unfold tickWith InferenceControl.Snapshot.tick
  dsimp only
  split
  · rename_i reordered
    simp [BranchingTemporal.tick, reordered]
  · rename_i node pending reordered
    rw [realization.exact node]
    simp [BranchingTemporal.tick, reordered, semanticExpansion, analyze,
      eventFor]
    cases system.emit node <;> rfl

/-! ## Positive and negative controls -/

namespace Canary

def system : BranchingSystem Nat Nat where
  emit node := if node = 0 then some 7 else none
  successors node := if node = 0 then [1, 1] else []

def controller : Controller Nat Nat Nat where
  initialMemory := 0
  scheduler _ := Scheduler.breadthFirst
  advance count _ _ successors := count + successors.length

def initial : InferenceControl.Snapshot Nat Nat Nat :=
  InferenceControl.Snapshot.initial controller [0]

/-- The reference factorization retains the emitted answer, both equal
successor occurrences, and the analysis result. -/
theorem reference_step_preserves_occurrences :
    tickWith system (.reference system) controller initial =
      { search :=
          { events := [⟨0, 7⟩]
            frontier := [1, 1] }
        memory := 2 } := by
  rfl

def droppingExpansion (node : Nat) : Expansion Nat Nat :=
  { selected := node
    emission := system.emit node
    successors := [] }

/-- Negative control: a fast path which drops generated occurrences cannot
inhabit the exact expansion interface. -/
theorem droppingExpansion_is_not_exact :
    Not (forall node, droppingExpansion node = semanticExpansion system node) := by
  intro claimed
  have atRoot := claimed 0
  simp [droppingExpansion, semanticExpansion, system] at atRoot

end Canary

#print axioms tickWith_eq_tick
#print axioms Canary.reference_step_preserves_occurrences
#print axioms Canary.droppingExpansion_is_not_exact

end Mettapedia.GSLT.Core.SelectionExpansionAnalysis
