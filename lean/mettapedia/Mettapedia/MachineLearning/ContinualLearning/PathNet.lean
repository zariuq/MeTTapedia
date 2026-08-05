import Mathlib.Tactic

/-!
# Routed module paths with frozen transfer

Fernando et al. (2017), *PathNet: Evolution Channels Gradient Descent in
Super Neural Networks*, represent an agent by a bounded-width path through a
layered modular network.  Only modules on the current path participate in the
forward and backward passes.  After a source task, its best path is frozen;
later paths may reuse those modules, but later optimization may change only
unfrozen modules.

This file isolates the architecture-level claims from the empirical
tournament search.  A path is an explicit finite set of modules at each
layer, and `pathUpdate` is supported on the active, unfrozen part of a path.
Consequently an arbitrary finite trace of later path updates preserves the
complete parameter view, and hence every extensional computation, of a
frozen source path.  Shared frozen modules remain available to a target path,
while target-only modules remain plastic.

The active-module bound is stated independently of the super-network width:
at most `N` active modules in each of `L` layers gives at most `L * N` active
modules.  This is a structural work bound, not a wall-clock or convergence
claim.

Two boundaries are executable.  Freezing every module exhausts plasticity,
and an overlapping later update without freezing can change the source
computation.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace PathNet

noncomputable section

universe u v w x

variable {Layer : Type u} {ModuleIndex : Type v}
variable {Input : Type w} {Output : Type x}

/-- A routed path selects a finite set of modules independently at each
layer. -/
abbrev Path (Layer ModuleIndex : Type*) :=
  Layer → Finset ModuleIndex

/-- Scalar parameters indexed by layer and module.  A real implementation may
replace each scalar with an arbitrary module parameter bundle; the support
theorems below are coordinatewise. -/
structure State (Layer ModuleIndex : Type*) where
  weight : Layer → ModuleIndex → ℝ

/-- The parameter view exposed by one path. -/
def selectedWeight
    [DecidableEq ModuleIndex]
    (state : State Layer ModuleIndex) (path : Path Layer ModuleIndex)
    (layer : Layer) (module : ModuleIndex) : ℝ :=
  if module ∈ path layer then state.weight layer module else 0

/-- A training displacement is applied exactly where the current path is
active and the persistent frozen path is inactive. -/
def pathUpdate
    [DecidableEq ModuleIndex]
    (state : State Layer ModuleIndex)
    (active frozen : Path Layer ModuleIndex)
    (displacement : Layer → ModuleIndex → ℝ) :
    State Layer ModuleIndex where
  weight layer module :=
    if module ∈ active layer ∧ module ∉ frozen layer then
      state.weight layer module + displacement layer module
    else
      state.weight layer module

/-- A frozen module is invariant under every active-path displacement. -/
@[simp] theorem weight_pathUpdate_of_mem_frozen
    [DecidableEq ModuleIndex]
    (state : State Layer ModuleIndex)
    (active frozen : Path Layer ModuleIndex)
    (displacement : Layer → ModuleIndex → ℝ)
    (layer : Layer) (module : ModuleIndex)
    (frozenMember : module ∈ frozen layer) :
    (pathUpdate state active frozen displacement).weight layer module =
      state.weight layer module := by
  simp [pathUpdate, frozenMember]

/-- A module outside the current path is likewise invariant. -/
@[simp] theorem weight_pathUpdate_of_not_mem_active
    [DecidableEq ModuleIndex]
    (state : State Layer ModuleIndex)
    (active frozen : Path Layer ModuleIndex)
    (displacement : Layer → ModuleIndex → ℝ)
    (layer : Layer) (module : ModuleIndex)
    (inactive : module ∉ active layer) :
    (pathUpdate state active frozen displacement).weight layer module =
      state.weight layer module := by
  simp [pathUpdate, inactive]

/-- The frozen source path's entire selected parameter view survives one
later routed update. -/
theorem selectedWeight_pathUpdate_of_subset_frozen
    [DecidableEq ModuleIndex]
    (state : State Layer ModuleIndex)
    (source active frozen : Path Layer ModuleIndex)
    (displacement : Layer → ModuleIndex → ℝ)
    (sourceFrozen : ∀ layer, source layer ⊆ frozen layer) :
    (fun layer module =>
        selectedWeight
          (pathUpdate state active frozen displacement)
          source layer module) =
      fun layer module => selectedWeight state source layer module := by
  funext layer module
  by_cases selected : module ∈ source layer
  · have frozenMember : module ∈ frozen layer :=
      sourceFrozen layer selected
    simp [selectedWeight, selected, pathUpdate, frozenMember]
  · simp [selectedWeight, selected]

/-- One later-task training record.  Paths may change from step to step while
the source-task frozen set remains fixed. -/
structure LaterUpdate (Layer ModuleIndex : Type*) where
  active : Path Layer ModuleIndex
  displacement : Layer → ModuleIndex → ℝ

def applyLaterUpdate
    [DecidableEq ModuleIndex]
    (frozen : Path Layer ModuleIndex)
    (state : State Layer ModuleIndex)
    (update : LaterUpdate Layer ModuleIndex) :
    State Layer ModuleIndex :=
  pathUpdate state update.active frozen update.displacement

def runLaterUpdates
    [DecidableEq ModuleIndex]
    (frozen : Path Layer ModuleIndex)
    (state : State Layer ModuleIndex)
    (updates : List (LaterUpdate Layer ModuleIndex)) :
    State Layer ModuleIndex :=
  updates.foldl (applyLaterUpdate frozen) state

/-- PathNet's no-forgetting core: every finite ordered trace of later path
updates preserves the complete parameter view of a source path contained in
the frozen set. -/
theorem selectedWeight_runLaterUpdates_of_subset_frozen
    [DecidableEq ModuleIndex]
    (state : State Layer ModuleIndex)
    (source frozen : Path Layer ModuleIndex)
    (updates : List (LaterUpdate Layer ModuleIndex))
    (sourceFrozen : ∀ layer, source layer ⊆ frozen layer) :
    (fun layer module =>
        selectedWeight
          (runLaterUpdates frozen state updates)
          source layer module) =
      fun layer module => selectedWeight state source layer module := by
  induction updates generalizing state with
  | nil =>
      rfl
  | cons update rest inductionHypothesis =>
      change
        (fun layer module =>
            selectedWeight
              (runLaterUpdates frozen
                (applyLaterUpdate frozen state update) rest)
              source layer module) =
          fun layer module => selectedWeight state source layer module
      rw [inductionHypothesis]
      exact
        selectedWeight_pathUpdate_of_subset_frozen
          state source update.active frozen update.displacement sourceFrozen

/-- Any computation that consumes only a path's selected parameter view is
preserved when that view is preserved.  This covers arbitrary nonlinear
module internals without pretending that PathNet's modules are scalar. -/
def evaluatePath
    [DecidableEq ModuleIndex]
    (evaluator : (Layer → ModuleIndex → ℝ) → Input → Output)
    (state : State Layer ModuleIndex)
    (path : Path Layer ModuleIndex)
    (input : Input) : Output :=
  evaluator
    (fun layer module => selectedWeight state path layer module)
    input

/-- Exact source-task behavioral preservation for every extensional
path evaluator and every input. -/
theorem evaluatePath_runLaterUpdates_of_subset_frozen
    [DecidableEq ModuleIndex]
    (evaluator : (Layer → ModuleIndex → ℝ) → Input → Output)
    (state : State Layer ModuleIndex)
    (source frozen : Path Layer ModuleIndex)
    (updates : List (LaterUpdate Layer ModuleIndex))
    (sourceFrozen : ∀ layer, source layer ⊆ frozen layer)
    (input : Input) :
    evaluatePath evaluator
        (runLaterUpdates frozen state updates) source input =
      evaluatePath evaluator state source input := by
  simp only [evaluatePath]
  rw [selectedWeight_runLaterUpdates_of_subset_frozen
    state source frozen updates sourceFrozen]

/-! ## Width-independent active work -/

/-- Number of routed module occurrences across all layers. -/
def activeModuleCount
    [Fintype Layer]
    (path : Path Layer ModuleIndex) : ℕ :=
  ∑ layer, (path layer).card

/-- The genotype-width invariant used by PathNet: no layer selects more than
`width` distinct modules. -/
def HasWidthAtMost
    (path : Path Layer ModuleIndex) (width : ℕ) : Prop :=
  ∀ layer, (path layer).card ≤ width

/-- Fixed path width bounds active module work independently of the number of
available modules in the super-network. -/
theorem activeModuleCount_le
    [Fintype Layer]
    (path : Path Layer ModuleIndex) (width : ℕ)
    (bounded : HasWidthAtMost path width) :
    activeModuleCount path ≤ Fintype.card Layer * width := by
  calc
    activeModuleCount path =
        ∑ layer : Layer, (path layer).card := rfl
    _ ≤ ∑ _layer : Layer, width :=
      Finset.sum_le_sum fun layer _ => bounded layer
    _ = Fintype.card Layer * width := by simp

/-! ## Plasticity and overlap boundaries -/

/-- If every module is frozen, every attempted path update is the identity. -/
theorem pathUpdate_eq_of_frozen_univ
    [Fintype ModuleIndex] [DecidableEq ModuleIndex]
    (state : State Layer ModuleIndex)
    (active : Path Layer ModuleIndex)
    (displacement : Layer → ModuleIndex → ℝ) :
    pathUpdate state active
        (fun _layer => Finset.univ)
        displacement =
      state := by
  cases state with
  | mk weight =>
      simp [pathUpdate]

abbrev OneLayer := Unit
abbrev TwoModules := Fin 2

def sourcePath : Path OneLayer TwoModules :=
  fun _ => {0}

def targetPath : Path OneLayer TwoModules :=
  fun _ => {0, 1}

def transferState : State OneLayer TwoModules where
  weight _ module := if module = 0 then 2 else 3

def targetDisplacement : OneLayer → TwoModules → ℝ :=
  fun _ module => if module = 0 then 7 else 5

/-- Reusing a frozen source module does not prevent a target path from
updating its own unfrozen module. -/
theorem frozen_overlap_reuses_source_and_trains_target :
    let updated :=
      pathUpdate transferState targetPath sourcePath targetDisplacement
    updated.weight () 0 = 2 ∧
      updated.weight () 1 = 8 ∧
      (fun module => selectedWeight updated sourcePath () module) =
        fun module => selectedWeight transferState sourcePath () module := by
  dsimp [pathUpdate, transferState, targetPath, sourcePath,
    targetDisplacement, selectedWeight]
  constructor
  · norm_num
  constructor
  · norm_num
  · funext module
    fin_cases module <;> norm_num

/-- Freezing is load-bearing.  If the later path updates an overlapping
source module, even the simplest source-path readout can change. -/
theorem unfrozen_overlap_changes_source :
    let updated :=
      pathUpdate transferState targetPath
        (fun _layer => ∅)
        targetDisplacement
    selectedWeight updated sourcePath () 0 = 9 ∧
      selectedWeight transferState sourcePath () 0 = 2 := by
  norm_num [pathUpdate, transferState, targetPath, sourcePath,
    targetDisplacement, selectedWeight]

#print axioms selectedWeight_runLaterUpdates_of_subset_frozen
#print axioms evaluatePath_runLaterUpdates_of_subset_frozen
#print axioms activeModuleCount_le
#print axioms frozen_overlap_reuses_source_and_trains_target
#print axioms unfrozen_overlap_changes_source

end

end PathNet

end Mettapedia.MachineLearning.ContinualLearning
