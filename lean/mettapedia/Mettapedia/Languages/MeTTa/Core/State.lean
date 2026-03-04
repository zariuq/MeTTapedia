import Mettapedia.Languages.MeTTa.Core.Atomspace

/-!
# MeTTaCore Interpreter State

The 4-register state model from the Meta-MeTTa paper:
- **i** (input): Terms to be evaluated
- **k** (knowledge): Atomspace with equations and type annotations
- **w** (workspace): Intermediate computation results
- **o** (output): Final results

## Main Definitions

* `MeTTaState` - The 4-register interpreter state
* State manipulation operations
* Initial state constructor

## References

* Meta-MeTTa paper (Meredith, Goertzel, Warrell, Vandervorst)
* Section 2: "State structure is a 4-tuple ⟨i, k, w, o⟩"
-/

namespace Mettapedia.Languages.MeTTa.Core

/-! ## MeTTa Interpreter State -/

/-- MeTTa interpreter state ⟨i, k, w, o⟩ from Meta-MeTTa paper.

    The four registers are:
    - `input`: Multiset of terms waiting to be evaluated
    - `knowledge`: The atomspace (equations, type annotations)
    - `workspace`: Multiset of terms being actively processed
    - `output`: Multiset of final (insensitive) results -/
structure MeTTaState where
  /-- i: Input terms to be evaluated -/
  input : Multiset Atom
  /-- k: Knowledge base (atomspace) -/
  knowledge : Atomspace
  /-- w: Workspace for intermediate results -/
  workspace : Multiset Atom
  /-- o: Output (fully reduced terms) -/
  output : Multiset Atom
  deriving Inhabited

namespace MeTTaState

/-! ### Construction -/

/-- Empty initial state -/
def empty : MeTTaState := ⟨∅, Atomspace.empty, ∅, ∅⟩

/-- Initial state with a single term to evaluate -/
def initial (a : Atom) (knowledge : Atomspace := Atomspace.empty) : MeTTaState :=
  ⟨∅, knowledge, {a}, ∅⟩

/-- Initial state with input terms -/
def withInput (input : Multiset Atom) (knowledge : Atomspace := Atomspace.empty) : MeTTaState :=
  ⟨input, knowledge, ∅, ∅⟩

/-! ### Register Access -/

/-- Get all input terms -/
def getInput (s : MeTTaState) : Multiset Atom := s.input

/-- Get the knowledge base -/
def getKnowledge (s : MeTTaState) : Atomspace := s.knowledge

/-- Get workspace contents -/
def getWorkspace (s : MeTTaState) : Multiset Atom := s.workspace

/-- Get output -/
def getOutput (s : MeTTaState) : Multiset Atom := s.output

/-! ### Register Modification -/

/-- Add term to input -/
def addInput (s : MeTTaState) (a : Atom) : MeTTaState :=
  { s with input := a ::ₘ s.input }

/-- Add term to workspace -/
def addWorkspace (s : MeTTaState) (a : Atom) : MeTTaState :=
  { s with workspace := a ::ₘ s.workspace }

/-- Add term to output -/
def addOutput (s : MeTTaState) (a : Atom) : MeTTaState :=
  { s with output := a ::ₘ s.output }

/-- Remove term from input -/
def removeInput (s : MeTTaState) (a : Atom) : MeTTaState :=
  { s with input := s.input.erase a }

/-- Remove term from workspace -/
def removeWorkspace (s : MeTTaState) (a : Atom) : MeTTaState :=
  { s with workspace := s.workspace.erase a }

/-- Move term from input to workspace -/
def inputToWorkspace (s : MeTTaState) (a : Atom) : MeTTaState :=
  { s with
    input := s.input.erase a
    workspace := a ::ₘ s.workspace }

/-- Move term from workspace to output -/
def workspaceToOutput (s : MeTTaState) (a : Atom) : MeTTaState :=
  { s with
    workspace := s.workspace.erase a
    output := a ::ₘ s.output }

/-! ### Knowledge Modification -/

/-- Add atom to knowledge -/
def addKnowledge (s : MeTTaState) (a : Atom) : MeTTaState :=
  { s with knowledge := s.knowledge.add a }

/-- Remove atom from knowledge -/
def removeKnowledge (s : MeTTaState) (a : Atom) : MeTTaState :=
  { s with knowledge := s.knowledge.remove a }

/-- Add equation to knowledge -/
def addEquation (s : MeTTaState) (pattern result : Atom) : MeTTaState :=
  { s with knowledge := s.knowledge.addEquation pattern result }

/-- Add type annotation to knowledge -/
def addType (s : MeTTaState) (a ty : Atom) : MeTTaState :=
  { s with knowledge := s.knowledge.addType a ty }

/-! ### Bulk Operations -/

/-- Replace workspace with new multiset -/
def setWorkspace (s : MeTTaState) (w : Multiset Atom) : MeTTaState :=
  { s with workspace := w }

/-- Replace input with new multiset -/
def setInput (s : MeTTaState) (i : Multiset Atom) : MeTTaState :=
  { s with input := i }

/-- Clear workspace -/
def clearWorkspace (s : MeTTaState) : MeTTaState :=
  { s with workspace := ∅ }

/-- Move all workspace to output -/
def flushWorkspaceToOutput (s : MeTTaState) : MeTTaState :=
  { s with
    workspace := ∅
    output := s.output + s.workspace }

/-! ### State Predicates -/

/-- Check if state is done (nothing left to process) -/
def isDone (s : MeTTaState) : Bool :=
  s.input.card == 0 && s.workspace.card == 0

/-- Check if workspace is empty -/
def workspaceEmpty (s : MeTTaState) : Bool :=
  s.workspace.card == 0

/-- Check if input is empty -/
def inputEmpty (s : MeTTaState) : Bool :=
  s.input.card == 0

/-- Total number of terms being processed -/
def activeCount (s : MeTTaState) : Nat :=
  s.input.card + s.workspace.card

end MeTTaState

/-! ## Theorems -/

/-- Empty state is done -/
theorem empty_isDone : MeTTaState.empty.isDone = true := rfl

/-- Initial state has term in workspace -/
theorem initial_workspace (a : Atom) :
    (MeTTaState.initial a).workspace = {a} := rfl

/-- Initial state has empty input -/
theorem initial_input_empty (a : Atom) :
    (MeTTaState.initial a).inputEmpty = true := rfl

/-- workspaceToOutput preserves total count -/
theorem workspaceToOutput_count (s : MeTTaState) (a : Atom) (h : a ∈ s.workspace) :
    (s.workspaceToOutput a).workspace.card + (s.workspaceToOutput a).output.card =
    s.workspace.card + s.output.card := by
  simp only [MeTTaState.workspaceToOutput, Multiset.card_erase_of_mem h, Multiset.card_cons]
  have h1 : 0 < s.workspace.card := Multiset.card_pos_iff_exists_mem.mpr ⟨a, h⟩
  have h2 : s.workspace.card.pred + 1 = s.workspace.card := Nat.succ_pred_eq_of_pos h1
  omega

/-! ## Unit Tests -/

section Tests

-- Empty state
example : MeTTaState.empty.isDone = true := rfl
example : MeTTaState.empty.activeCount = 0 := rfl

-- Initial state
example : (MeTTaState.initial (.symbol "x")).workspaceEmpty = false := by decide
example : (MeTTaState.initial (.symbol "x")).inputEmpty = true := rfl

-- Adding to workspace
example : (MeTTaState.empty.addWorkspace (.symbol "x")).activeCount = 1 := rfl

end Tests

end Mettapedia.Languages.MeTTa.Core
