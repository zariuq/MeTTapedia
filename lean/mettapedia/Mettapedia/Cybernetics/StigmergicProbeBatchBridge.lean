import Mettapedia.Cybernetics.StigmergicProbeRound
import Mettapedia.Machines.SnapshotBatch
import Mettapedia.ProbabilityTheory.IndependentFiniteSamplingMap

/-!
# Partitioned execution of supplied-choice stigmergic probe movement

The concrete bounded weighted-graph walker instantiates the generic
snapshot/private-write kernel. Every logical probe owns one indexed slot and
receives its own supplied edge choice. Its graph and direction are frozen
during the batch. Sequential indexed movement and independently partitioned
movement agree for every choice vector, hence under any law of choice vectors.

This result does not assert that a finite pseudorandom generator samples an
arbitrary real-valued probability law. The source movement law is linked to
supplied choices by `WeightedGraph.step_eq_map_advance`; implementing its sampler
is a separate numeric realization boundary.
-/

namespace Mettapedia.Cybernetics.StigmergicProbeBatchBridge

open Mettapedia.Machines.SnapshotBatch
open Mettapedia.Cybernetics.StigmergicProbeRound
open Mettapedia.ProbabilityTheory.IndependentFiniteSampling

variable {Id Vertex Edge : Type*} [DecidableEq Id]

/-- The graph is shared and read-only; the bounded probe slot is private.
Direction and edge choice are keyed by logical probe identity. -/
def probeKernel (side : Id → Side) (depthBound : ℕ) :
    Kernel (WeightedGraph Vertex Edge) Id (Option Edge) Id
      (Option (Position Vertex depthBound)) where
  destination := id
  compute graph probe choice position :=
    graph.advance (side probe) depthBound position choice

/-- A partition may change both worker assignment and publication order.
Its exact occurrence coverage and distinct private slots preserve movement. -/
theorem partitioned_movement_eq_sequential (graph : WeightedGraph Vertex Edge)
    (side : Id → Side) (depthBound : ℕ) (choices : Id → Option Edge)
    (initial : Id → Option (Position Vertex depthBound))
    (items : List Id) (parts : List (List Id))
    (unique : items.Nodup) (coverage : parts.flatten.Perm items) :
    (probeKernel side depthBound).partitioned graph choices initial parts =
      (probeKernel side depthBound).run graph choices initial items := by
  apply Kernel.partitioned_eq_run
  · exact coverage
  · simpa [Kernel.Disjoint, probeKernel] using unique

/-- Any end-of-movement observation, including a later nonconsuming endpoint
join, agrees when it reads the same complete moved population. -/
theorem movement_observation_eq {Observed : Type*}
    (graph : WeightedGraph Vertex Edge) (side : Id → Side) (depthBound : ℕ)
    (choices : Id → Option Edge) (initial : Id → Option (Position Vertex depthBound))
    (items : List Id) (parts : List (List Id))
    (unique : items.Nodup) (coverage : parts.flatten.Perm items)
    (observe : (Id → Option (Position Vertex depthBound)) → Observed) :
    observe ((probeKernel side depthBound).partitioned graph choices initial parts) =
      observe ((probeKernel side depthBound).run graph choices initial items) :=
  congrArg observe
    (partitioned_movement_eq_sequential graph side depthBound choices initial
      items parts unique coverage)

/-- Pointwise realization implies equality of the full joint output law. No
independence assumption is needed: even correlated choice vectors are kept.
The theorem does not identify a concrete PRNG with `choiceLaw`. -/
theorem partitioned_movement_law_eq_sequential (graph : WeightedGraph Vertex Edge)
    (side : Id → Side) (depthBound : ℕ)
    (choiceLaw : PMF (Id → Option Edge))
    (initial : Id → Option (Position Vertex depthBound))
    (items : List Id) (parts : List (List Id))
    (unique : items.Nodup) (coverage : parts.flatten.Perm items) :
    choiceLaw.map (fun choices =>
      (probeKernel side depthBound).partitioned graph choices initial parts) =
    choiceLaw.map (fun choices =>
      (probeKernel side depthBound).run graph choices initial items) := by
  apply congrArg (fun realize => choiceLaw.map realize)
  funext choices
  exact partitioned_movement_eq_sequential graph side depthBound choices initial
    items parts unique coverage

/-- A complete occurrence list produces the pointwise bounded move at every
identity. This is proved from the sequential evaluator's private-store law. -/
theorem complete_movement_pointwise (graph : WeightedGraph Vertex Edge)
    (side : Id → Side) (depthBound : ℕ) (choices : Id → Option Edge)
    (initial : Id → Option (Position Vertex depthBound))
    (items : List Id) (unique : items.Nodup) (complete : ∀ i, i ∈ items) :
    (probeKernel side depthBound).run graph choices initial items =
      fun i => graph.advance (side i) depthBound (initial i) (choices i) := by
  funext i
  apply Kernel.run_at_owned (probeKernel side depthBound) graph choices initial items
  · simpa [Kernel.Disjoint, probeKernel] using unique
  · exact complete i

/-- Each live probe draws its own eligible edge from the frozen graph. Dead
slots have a fixed `none` choice. Depth-limited live slots may draw an unused
edge; the bounded move still kills them, as the source transition specifies. -/
noncomputable def edgeChoiceLaw [Fintype Edge] [DecidableEq Vertex]
    (graph : WeightedGraph Vertex Edge) (side : Id → Side) (depthBound : ℕ)
    (initial : Id → Option (Position Vertex depthBound)) : Id → PMF (Option Edge) :=
  fun i => match initial i with
    | none => PMF.pure none
    | some (v, _) => graph.chooseEdge (side i) v

omit [DecidableEq Id] in
theorem edgeChoiceLaw_map [Fintype Edge] [DecidableEq Vertex]
    (graph : WeightedGraph Vertex Edge) (side : Id → Side) (depthBound : ℕ)
    (initial : Id → Option (Position Vertex depthBound)) (i : Id) :
    (edgeChoiceLaw graph side depthBound initial i).map
        (graph.advance (side i) depthBound (initial i)) =
      graph.step (side i) depthBound (initial i) := by
  cases position : initial i with
  | none => simp [edgeChoiceLaw, position, WeightedGraph.advance,
      WeightedGraph.step, boundedStep, PMF.pure_map]
  | some value =>
    rcases value with ⟨v, d⟩
    simpa only [edgeChoiceLaw, position] using
      (graph.step_eq_map_advance (side i) depthBound v d).symm

/-- Strong source-to-implementation law: independently sample eligible edges,
run the actual partitioned indexed-store implementation, and obtain exactly
the independently stated product of bounded weighted movement kernels. -/
theorem partitioned_movement_has_source_law [Fintype Id] [Fintype Vertex]
    [Fintype Edge] [DecidableEq Vertex]
    (graph : WeightedGraph Vertex Edge) (side : Id → Side) (depthBound : ℕ)
    (initial : Id → Option (Position Vertex depthBound))
    (items : List Id) (parts : List (List Id))
    (unique : items.Nodup) (complete : ∀ i, i ∈ items)
    (coverage : parts.flatten.Perm items) :
    (independent (edgeChoiceLaw graph side depthBound initial)).map
        (fun choices =>
          (probeKernel side depthBound).partitioned graph choices initial parts) =
      independent (fun i => graph.step (side i) depthBound (initial i)) := by
  rw [partitioned_movement_law_eq_sequential graph side depthBound
    (independent (edgeChoiceLaw graph side depthBound initial)) initial
    items parts unique coverage]
  have realizes : (fun choices =>
      (probeKernel side depthBound).run graph choices initial items) =
      (fun choices i => graph.advance (side i) depthBound (initial i) (choices i)) := by
    funext choices
    exact complete_movement_pointwise graph side depthBound choices initial items
      unique complete
  rw [realizes, independent_map]
  apply congrArg independent
  funext i
  exact edgeChoiceLaw_map graph side depthBound initial i

namespace Controls

def twoWayGraph : WeightedGraph Bool Bool where
  source := id
  target vertex := !vertex
  weight _ := 1

def directions : Fin 3 → Side
  | 1 => .backward
  | _ => .forward

def choices : Fin 3 → Option Bool
  | 0 => some false
  | 1 => some true
  | _ => none

def initial : Fin 3 → Option (Position Bool 2) := fun _ => some (false, 0)

/-- Two opposite-direction probes move to the same endpoint; the third dies.
All are separate occurrences and remain in separate indexed slots. -/
theorem three_partitions_move_and_retain_identity :
    (probeKernel directions 2).partitioned twoWayGraph choices initial [[2], [0], [1]] =
      ![some (true, 1), some (true, 1), none] := by
  funext probe
  fin_cases probe <;> decide

theorem three_partitions_match_reference :
    (probeKernel directions 2).partitioned twoWayGraph choices initial [[2], [0], [1]] =
      (probeKernel directions 2).run twoWayGraph choices initial [0, 1, 2] := by
  apply partitioned_movement_eq_sequential
  · decide
  · decide

theorem depth_limit_still_kills :
    (probeKernel directions 2).batch twoWayGraph (fun _ => some false)
      (fun _ => some (false, 2)) [0, 1, 2] = (fun _ => none) := by
  funext probe
  fin_cases probe <;> decide

end Controls

end Mettapedia.Cybernetics.StigmergicProbeBatchBridge
