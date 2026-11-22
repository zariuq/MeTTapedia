import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.Initial
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.InitialControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.Rearrangements
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.Interchange
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.InterchangeControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.Traces
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.Grades
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.GradeControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.Waves
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.WavesOnTheStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.Telescopes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.Fibred
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.FibredControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.BirthControls

/-!
# Proof-relevant runs

The runs of the two-zone calculus as the 1-cells of a free structure, and their interchanges as
2-cells that keep their events.

* **Witnessed runs and initiality** (`Initial`): a witnessed run records each firing's declaration,
  frame and admission. A proof-relevant model has the five operations of the calculus and exactly the
  structural equations of proof terms as laws. The witnessed runs are the initial such model: every
  model receives exactly one map (`paths_initial`). The relational initiality of
  `KnowledgeTensorInitial` is its truncation (`run_initial_of_relevant`); weights in a monoid are a
  model whose unique map is the product of the weights (`weights_unique`).
* **Over frames** (`Fibred`): in the frame-indexed calculus a witnessed run lies over a frame map, and
  framing or strengthening a cut acts on its second part through the atoms carried, or the knowledge
  transported, along the first part (`Path.frame_cut`, `Path.strengthen_cut`). The witnessed runs over
  frames are the initial model of the fibred structural equations (`Fibred.paths_initial`).
* **Interchange cells** (`Rearrangements`, `Interchange`): a cell is a derivation by swaps of
  adjacent firings, each justified at its state; it carries an event map that keeps every label, and
  the event maps are functorial for vertical composition and whiskering and satisfy the interchange
  law of cells (`events_interchange`). Where events are distinct, parallel cells move events alike
  (`events_eq_of_nodup`); with repeated events, symmetry cells survive (`symmetry_events`). Every cell
  of a two-zone system is natural in placements (`Cell.place`, `events_place`). The interchange cell of
  two runs side by side is built as data and moves events by the block exchange (`interchange`,
  `interchange_events`). The swap relation of traces is the truncation of the cells
  (`nonempty_cell_iff_swaps`). A model that respects the generating swaps is constant along every cell
  (`interp_cell`).
* **Grades** (`Grades`, `InterchangeControls`, `GradeControls`): takes and makes interchange at every
  frame; checks blind to the frame do too (`SemanticCell.beside`). Knowledge blocks an interchange
  exactly through a tell some guard waits for: a teller and its asker have a cell exactly where the
  teller is quiet (`teller_asker_cell_iff`, `quiet_iff_never_waited_on`). Counting and absence
  interchange only within their grade (`counting_cell_not_placed`, `absence_no_cell`), and the grade
  is a property of a run, not of its trace (`grade_not_trace_invariant`).
* **Waves** (`Waves`, `WavesOnTheStep`): pairwise compatibility gives a joint wave where the tells are
  median-convex (`helly`), and gluing works along consistent join trees (`ConsistentTree.glue`). The
  hollow cube is pairwise solvable, has acyclic scopes, and is neither convex nor consistent
  (`hollow_not_flag`, `hollow_not_consistent`); the step's cells are not flag
  (`firstOrder_cells_not_flag`); on the native step, convex shadows that meet two by two give every
  order (`every_order_admitted_of_convex`), and the three native tellers that admit no order have
  shadows that meet two by two and that no ternary operation makes convex (`tellers_not_convex`).
* **Helper swaps** (`Telescopes`): the block exchange is the unique comparison of composite frames
  that keeps event identity (`keepsProvenance_iff`), all such comparisons agree
  (`keepsProvenance_unique`), and at equal frames it is not the identity (`point_exchange_ne_id`), so
  strict commutation of helper firings is not available (`identity_not_keepsProvenance`). Frames
  ordered by inclusion have no automorphisms, and there two births of different kinds do not
  interchange even up to the frames (`BirthControls.births_not_interchanged`): the interchange of
  births needs the exchange as a vertical side.
-/

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns

#print axioms Path.eq_of_uses
#print axioms Path.exists_iff_run
#print axioms lift
#print axioms lift_unique
#print axioms paths_initial
#print axioms run_initial_of_relevant
#print axioms interp_weights
#print axioms weights_unique
#print axioms eqv_iff_ofTyped_eq

#print axioms Rearrangement.events_label
#print axioms Rearrangement.events_trans
#print axioms Rearrangement.events_whiskerLeft
#print axioms Rearrangement.events_whiskerRight
#print axioms Rearrangement.events_eq_of_nodup
#print axioms Rearrangement.symmetry_events
#print axioms Rearrangement.runs
#print axioms Rearrangement.events_mapAlong
#print axioms Rearrangement.events_interchange
#print axioms Rearrangement.first_swap

#print axioms runs_iff_run
#print axioms Cell.run
#print axioms Cell.place
#print axioms events_place
#print axioms movePast
#print axioms interchange
#print axioms interchange_events
#print axioms fourBlock
#print axioms fourBlock_events
#print axioms Cell.swaps
#print axioms nonempty_cell_iff_swaps
#print axioms nonempty_cell_iff_interchanges
#print axioms Cell.perm
#print axioms weights_invariant
#print axioms quiet_iff_never_waited_on
#print axioms independent_of_quiet

#print axioms interp_cell
#print axioms weights_respectSwaps

#print axioms SemanticCell.beside
#print axioms events_beside
#print axioms checked_blind

#print axioms helly
#print axioms ground_convex
#print axioms ground_joint
#print axioms diagonal_not_convex
#print axioms hollow_pairwise
#print axioms hollow_not_joint
#print axioms hollow_not_flag
#print axioms ConsistentTree.glue
#print axioms hollow_running
#print axioms hollow_not_consistent
#print axioms hollow_no_consistent_tree
#print axioms one_then_same_consistent
#print axioms triangle_pairwise_consistent
#print axioms triangle_not_joint

#print axioms firstOrder_cells_not_flag
#print axioms jointly_iff_shadows
#print axioms shadows_meet_iff
#print axioms jointly_of_convex_shadows
#print axioms every_order_admitted_of_convex
#print axioms tellers_shadows_not_convex
#print axioms tellers_shadows_meet
#print axioms tellers_not_convex

#print axioms keepsProvenance_iff
#print axioms endo_keeping_legs
#print axioms keepsProvenance_unique
#print axioms round_trip
#print axioms point_exchange_ne_id
#print axioms identity_not_keepsProvenance

#print axioms InitialControls.twins_two_runs
#print axioms InitialControls.twins_separated
#print axioms InitialControls.reachability_model
#print axioms InitialControls.twins_swap_respected

#print axioms InterchangeControls.teller_asker_cell_iff
#print axioms InterchangeControls.teller_asker_cell_known
#print axioms InterchangeControls.teller_asker_no_cell_unknown
#print axioms InterchangeControls.takers_interchange_events
#print axioms InterchangeControls.takers_interchange_placed
#print axioms InterchangeControls.cycle_square_one_token
#print axioms InterchangeControls.cycle_symmetry_two_tokens
#print axioms InterchangeControls.cycle_cells_one_token
#print axioms InterchangeControls.free_weights_separate

#print axioms GradeControls.counting_square
#print axioms GradeControls.counting_cell_not_placed
#print axioms GradeControls.counting_no_cell_beside
#print axioms GradeControls.grade_not_trace_invariant
#print axioms GradeControls.absence_left_runs
#print axioms GradeControls.absence_right_runs
#print axioms GradeControls.absence_no_cell

#print axioms Fibred.Path.run
#print axioms Fibred.Path.exists_iff_run
#print axioms Fibred.Path.route_eq
#print axioms Fibred.Path.eq_of_uses
#print axioms Fibred.Path.frame_cut
#print axioms Fibred.Path.strengthen_cut
#print axioms Fibred.paths
#print axioms Fibred.interp_cut
#print axioms Fibred.interp_frame
#print axioms Fibred.interp_strengthen
#print axioms Fibred.interp_leaf
#print axioms Fibred.lift
#print axioms Fibred.lift_unique
#print axioms Fibred.paths_initial
#print axioms Fibred.run_initial
#print axioms Fibred.runs_model
#print axioms Fibred.run_iff_every_model

#print axioms FibredControls.interp_counts
#print axioms FibredControls.counts_unique
#print axioms FibredControls.two_births
#print axioms FibredControls.two_births_counted
#print axioms FibredControls.carried_name
#print axioms FibredControls.born_not_carried

#print axioms BirthControls.left_then_right
#print axioms BirthControls.right_then_left
#print axioms BirthControls.orders_differ
#print axioms BirthControls.no_frame_automorphism
#print axioms BirthControls.births_not_interchanged

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns
