import Mettapedia.SetTheory.AntiFoundation.ReadingFixedPoints
import Mettapedia.SetTheory.AntiFoundation.ReadingLattice
import Mettapedia.SetTheory.AntiFoundation.ReadingKernels
import Mettapedia.SetTheory.AntiFoundation.ReadingFinite
import Mettapedia.SetTheory.Profiles.ProfileFiniteScottCollapse
import Mettapedia.SetTheory.Profiles.ProfileGraphReadoutFiniteBoolean

/-!
# Finite graphs: the computed kernels are readings

A reading of a graph is a fixed point of the child-class step on its setoids
(`AntiFoundation.step`). Three kernels of a finite graph are computed in this directory.
This module places each of them in the lattice of readings.

* Bisimilarity, computed by `ProfileGraphReadout.FiniteBoolean.equivalent`, is the greatest
  reading.
* The unfolding kernel, computed by `ProfileFiniteScottReadout.rawUnfoldingEquivalent`, is a
  bisimulation. It need not be a reading: on `AntiFoundation.ScottGap`, which has the shape
  of the control `ProfileFiniteScottCollapse.Controls.recount`, it keeps apart two nodes
  that have the same children up to it.
* The canonical kernel, computed by `FiniteGraph.canonicalEquivalent`, quotients by the
  unfolding kernel, recounts the children, and repeats. It is a reading of every finite
  graph, and it lies above the unfolding kernel.

The least reading above the unfolding kernel is its closure under the child-class step
(`AntiFoundation.stepClosure`). It lies below the canonical kernel, and the two differ. On
the fan, where one node has two children and each child has that node as its only child,
the unfolding kernel is already a reading, and the canonical kernel relates the node with
its children. On the recount control the closure and the canonical kernel both relate the
two roots.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileFiniteReadings

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.SetTheory.AntiFoundation
open ConstructiveFinite
open ProfileFiniteScottReadout
open ProfileFiniteScottCollapse
open UnfoldingIdentityComparison

universe u

/-! ## Bisimilarity -/

/-- The greatest reading of a finite graph is what the bisimulation refinement computes. -/
theorem gfp_iff_equivalent {α : Type u} [Enumeration α] [DecidableEq α] (edge : Edge α)
    [DecidableRel edge] (a b : α) :
    (step edge).gfp a b ↔ ProfileGraphReadout.FiniteBoolean.equivalent edge edge a b = true := by
  rw [gfp_eq_bisimilar]
  exact (bisimilarSetoid_iff edge).trans
    (ProfileGraphReadout.FiniteBoolean.equivalent_eq_true edge edge a b).symm

/-! ## The unfolding kernel -/

/-- The unfolding kernel of a finite graph is a bisimulation, so the child-class step only
adds pairs to it. -/
theorem scottKernel_le_step (graph : FiniteGraph.{u}) :
    scottKernel graph.edge ≤ step graph.edge (scottKernel graph.edge) := by
  apply (le_step_iff_isBisimulation graph.edge (scottKernel graph.edge)).mpr
  intro first second same
  have raw : graph.rawRelation first second :=
    (stable_kernel graph.edge graph.edge first second).mpr same
  obtain ⟨forward, backward⟩ := graph.rawRelation_regular raw
  constructor
  · intro child available
    obtain ⟨reply, replyAvailable, related⟩ := forward child available
    exact ⟨reply, replyAvailable, (stable_kernel graph.edge graph.edge child reply).mp related⟩
  · intro child available
    obtain ⟨reply, replyAvailable, related⟩ := backward child available
    exact ⟨reply, replyAvailable, (stable_kernel graph.edge graph.edge reply child).mp related⟩

/-! ## The canonical kernel -/

/-- The canonical kernel of a finite graph, as a setoid. -/
def canonicalSetoid (graph : FiniteGraph.{u}) : Setoid graph.Node where
  r first second := graph.canonicalEquivalent first second = true
  iseqv := graph.canonicalIdentification.equiv

/-- The canonical kernel is a reading of every finite graph. -/
theorem canonicalSetoid_reading (graph : FiniteGraph.{u}) :
    step graph.edge (canonicalSetoid graph) = canonicalSetoid graph :=
  reading_of_canonicalDecoration graph.edge (canonicalSetoid graph) graph.canonicalMember
    graph.canonicalProjection graph.canonicalDecoration graph.canonicalMember_extensional

/-- The unfolding kernel lies below the canonical kernel. -/
theorem scottKernel_le_canonicalSetoid (graph : FiniteGraph.{u}) :
    scottKernel graph.edge ≤ canonicalSetoid graph := by
  intro first second same
  exact graph.canonicalEquivalent_of_raw first second
    ((stable_kernel graph.edge graph.edge first second).mpr same)

/-- The canonical kernel lies below bisimilarity, as every reading does. -/
theorem canonicalSetoid_le_gfp (graph : FiniteGraph.{u}) :
    canonicalSetoid graph ≤ (step graph.edge).gfp :=
  (step graph.edge).le_gfp (canonicalSetoid_reading graph).symm.le

/-- The canonical kernel lies above the least reading that contains the unfolding kernel. -/
theorem stepClosure_scottKernel_le_canonicalSetoid {α : Type u} [Fintype α] [Enumeration α]
    [DecidableEq α] (edge : Edge α) [DecidableRel edge] :
    stepClosure edge (scottKernel edge) ≤ canonicalSetoid (FiniteGraph.ofEdges edge) :=
  stepClosure_le_of_reading edge (scottKernel_le_canonicalSetoid (FiniteGraph.ofEdges edge))
    (canonicalSetoid_reading (FiniteGraph.ofEdges edge)).le

/-- The closure of the unfolding kernel is a reading of every finite graph. -/
theorem stepClosure_scottKernel_reading {α : Type u} [Fintype α] [Enumeration α]
    [DecidableEq α] (edge : Edge α) [DecidableRel edge] :
    step edge (stepClosure edge (scottKernel edge)) = stepClosure edge (scottKernel edge) :=
  stepClosure_reading edge (scottKernel_le_step (FiniteGraph.ofEdges edge))

/-! ## The fan -/

/-- `0` has the children `1` and `2`. Each of them has `0` as its only child. -/
def fanEdge (source target : Fin 3) : Prop :=
  (source = 0 ∧ (target = 1 ∨ target = 2)) ∨ ((source = 1 ∨ source = 2) ∧ target = 0)

instance fanDecidable : DecidableRel fanEdge := by
  intro source target
  unfold fanEdge
  infer_instance

abbrev fan : FiniteGraph := FiniteGraph.ofEdges fanEdge

def fanElems : List (Fin 3) := [0, 1, 2]

theorem fan_complete (node : Fin 3) : node ∈ fanElems := by
  revert node
  decide

def fanEdgeB (source target : Fin 3) : Bool := decide (fanEdge source target)

theorem fanEdgeB_iff (source target : Fin 3) :
    fanEdgeB source target = true ↔ fanEdge source target := by
  simp only [fanEdgeB, decide_eq_true_eq]

/-- The unfolding kernel of the fan, as a Boolean table. -/
def fanScottB (first second : Fin 3) : Bool :=
  rawUnfoldingEquivalent fanEdge fanEdge first second

theorem fanScottB_iff (first second : Fin 3) :
    fanScottB first second = true ↔ scottKernel fanEdge first second :=
  rawUnfoldingEquivalent_eq_true fanEdge fanEdge first second

/-- The unfolding kernel of the fan pairs `1` with `2` and leaves `0` alone. -/
theorem fanScottB_table :
    (fanElems.map fun first => fanElems.map fun second => fanScottB first second) =
      [[true, false, false], [false, true, true], [false, true, true]] := by
  decide +kernel

/-- One child-class step leaves that table as it is. -/
theorem fan_step_table :
    ∀ first second : Fin 3,
      matrixStep fanElems fanEdgeB fanScottB first second = fanScottB first second := by
  decide +kernel

/-- On the fan the unfolding kernel is a reading. -/
theorem fan_scottKernel_reading :
    step fanEdge (scottKernel fanEdge) = scottKernel fanEdge := by
  apply Setoid.ext
  intro first second
  rw [step_apply,
    ← matrixStep_true_iff fanElems fan_complete fanEdge fanEdgeB fanEdgeB_iff fanScottB
      (⇑(scottKernel fanEdge)) fanScottB_iff first second,
    fan_step_table first second]
  exact fanScottB_iff first second

theorem fan_scottKernel_separates : ¬ scottKernel fanEdge 0 1 := by
  intro same
  have table : fanScottB 0 1 = false := by decide +kernel
  have accepted := (fanScottB_iff 0 1).mpr same
  rw [table] at accepted
  exact Bool.noConfusion accepted

theorem fan_second_pass_identifies :
    fan.quotient.projection (fan.projection 0) = fan.quotient.projection (fan.projection 1) := by
  decide +kernel

/-- The canonical kernel of the fan relates `0` with `1`. -/
theorem fan_canonical_identifies : canonicalSetoid fan 0 1 := by
  apply (FiniteGraph.canonicalEquivalent_kernel fan 0 1).mpr
  change fan.iterateProjection 3 0 = fan.iterateProjection 3 1
  exact FiniteGraph.iterateProjection_equal_persists fan 2 1 0 1 fan_second_pass_identifies

/-- On the fan the least reading above the unfolding kernel keeps `0` apart from `1`, and
the canonical kernel, a coarser reading, relates them. -/
theorem fan_closure_strictly_below_canonical :
    ¬ stepClosure fanEdge (scottKernel fanEdge) 0 1 ∧ canonicalSetoid fan 0 1 := by
  refine ⟨?_, fan_canonical_identifies⟩
  rw [stepClosure_of_reading fanEdge fan_scottKernel_reading]
  exact fan_scottKernel_separates

/-! ## The recount control -/

def recountElems : List (Fin 5) := [0, 1, 2, 3, 4]

theorem recount_complete (node : Fin 5) : node ∈ recountElems := by
  revert node
  decide

def recountEdgeB (source target : Fin 5) : Bool := decide (Controls.recountEdge source target)

theorem recountEdgeB_iff (source target : Fin 5) :
    recountEdgeB source target = true ↔ Controls.recountEdge source target := by
  simp only [recountEdgeB, decide_eq_true_eq]

/-- The unfolding kernel of the recount control, as a Boolean table. -/
def recountScottB (first second : Fin 5) : Bool :=
  rawUnfoldingEquivalent Controls.recountEdge Controls.recountEdge first second

theorem recountScottB_iff (first second : Fin 5) :
    recountScottB first second = true ↔ scottKernel Controls.recountEdge first second :=
  rawUnfoldingEquivalent_eq_true Controls.recountEdge Controls.recountEdge first second

theorem recount_scottKernel_separates : ¬ scottKernel Controls.recountEdge 0 3 := by
  intro same
  have accepted := (recountScottB_iff 0 3).mpr same
  rw [recountScottB, Controls.recount_initial_raw_different] at accepted
  exact Bool.noConfusion accepted

/-- The two roots have the same children up to the unfolding kernel. -/
theorem recount_step_identifies :
    step Controls.recountEdge (scottKernel Controls.recountEdge) 0 3 :=
  (step_apply Controls.recountEdge (scottKernel Controls.recountEdge) 0 3).mpr
    ((matrixStep_true_iff recountElems recount_complete Controls.recountEdge recountEdgeB
      recountEdgeB_iff recountScottB (⇑(scottKernel Controls.recountEdge)) recountScottB_iff
      0 3).mp (by decide +kernel))

/-- On the recount control the unfolding kernel keeps the two roots apart. Its closure under
the child-class step relates them, and so does the canonical kernel.
`AntiFoundation.ScottGap` is the same picture. -/
theorem recount_closure_and_canonical_identify :
    ¬ scottKernel Controls.recountEdge 0 3 ∧
      stepClosure Controls.recountEdge (scottKernel Controls.recountEdge) 0 3 ∧
        canonicalSetoid Controls.recount 0 3 :=
  ⟨recount_scottKernel_separates,
    step_le_stepClosure Controls.recountEdge (scottKernel_le_step Controls.recount)
      recount_step_identifies,
    Controls.recount_final_identifies⟩

/-! ## The Scott pair: the greatest reading, computed by the refinement -/

theorem scott_equivalent_table :
    ProfileGraphReadout.FiniteBoolean.equivalent scottEdge scottEdge .s0 .s1 = true := by
  decide +kernel

theorem scott_gfp_by_refinement : (step scottEdge).gfp .s0 .s1 :=
  (gfp_iff_equivalent scottEdge .s0 .s1).mpr scott_equivalent_table

end Mettapedia.SetTheory.Profiles.ProfileFiniteReadings
