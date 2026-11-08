import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedCommutation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessInterference

/-!
# Actual aliased reads, independent consumption and the read-before-take boundary

The positive pair has unequal port counts, a nonempty incoming equation
store, two reads of a rigid schema at row 7 and a take of shared row 8. Both source executions return
at fuel one per event. The smallest asymmetric control reads and then takes
one occurrence; no source firing can perform the read after consumption.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualWorldScopeLedger ContextualScopeSupport
open ContextualSelectedExecution ContextualSelectedNormalization ContextualExecutionCommutationNames
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ContextualSelectionViews.Controls (base locals captures raw privateVariable pair)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)
local instance : Quiver (Endpoint locals Nat [] ()) := ContextualExecution.graph locals Nat

def a : Term base [] () := .op .constant .nil
def b : Term base [] () := .op .pair (.cons a (.cons a .nil))
def labels (occurrence : Nat) := if occurrence = 8 then b else a
def prior := [b]
def rows (occurrence : Nat) : ContextualStoredRows.Row locals captures [] () :=
  if occurrence = 7 then .schema (Rigid.includeTerm raw (labels occurrence))
  else .shared (Rigid.includeTerm captures (labels occurrence))
def inventory : Inventory locals captures (O := Nat) [] () :=
  ⟨⟨diagonals captures prior, {7, 8}⟩, rows,
    [observe (generator captures 0)], [observe privateVariable]⟩
def initial : Endpoint locals Nat [] () where
  Names := Nat
  equality := inferInstance
  declarations := captures
  scopes := fun _ => ∅
  occupied := {0, 2, 7}
  inventory := inventory
  covered := (coveredWorld_iff locals captures _ _ inventory).mpr (by decide +kernel)

theorem row_template (occurrence : Nat) :
    ContextualStoredRows.asTemplate locals captures (initial.inventory.rows occurrence) = Rigid.includeTerm raw (labels occurrence) := by
  change ContextualStoredRows.asTemplate locals captures (rows occurrence) = _
  unfold rows
  split_ifs
  · rfl
  · exact Rigid.instantiate_include _ (labels occurrence)

theorem inputs_include_a_stored_schema_and_a_shared_row :
    initial.inventory.rows 7 = .schema (Rigid.includeTerm raw a) ∧
      initial.inventory.rows 8 = .shared (Rigid.includeTerm captures b) := ⟨rfl, rfl⟩

def reader : Interaction initial where
  made := [99]
  distinct := by decide
  fresh := by decide
  value _ := privateVariable
  covered := by intro _ _; change (∅ : Finset Nat) ⊆ initial.occupied; exact Finset.empty_subset _
  taken := []
  read := [7, 7]
  take_distinct := by decide
  take_available := by decide
  read_available := by decide
  take_read_apart := by decide
  label := labels
  template := by intro occurrence _; exact row_template occurrence

def consumer : Interaction initial where
  made := [100]
  distinct := by decide
  fresh := by decide
  value _ := pair privateVariable (generator raw (.inr 0))
  covered := by intro _ _; change (∅ : Finset Nat) ⊆ initial.occupied; exact Finset.empty_subset _
  taken := [8]
  read := []
  take_distinct := by decide
  take_available := by decide
  read_available := by decide
  take_read_apart := by decide
  label := labels
  template := by intro occurrence _; exact row_template occurrence

theorem independent : reader.Independent consumer :=
  (Interaction.independent_iff_disjoint _ _).mpr (by decide)

def left := reader.twoTarget consumer prior rfl independent.orders.1
def right := consumer.twoTarget reader prior rfl independent.orders.2
def leftPath := reader.twoPath consumer prior rfl independent.orders.1
def rightPath := consumer.twoPath reader prior rfl independent.orders.2
def correspondence : EndpointPermutation left right := endpointPermutation reader consumer prior rfl independent

theorem both_actual_orders_keep_read_aliases_and_the_real_take :
    Nonempty (Quiver.Path initial left) ∧ Nonempty (Quiver.Path initial right) ∧
      Nonempty (EndpointPermutation left right) ∧
      selections leftPath = [⟨[], [7, 7], [99]⟩, ⟨[8], [], [100]⟩] ∧
      selections rightPath = [⟨[8], [], [100]⟩, ⟨[], [7, 7], [99]⟩] ∧
      fuels leftPath = [1, 1] ∧ fuels rightPath = [1, 1] ∧
      left.inventory.configuration.present = {7, 99, 100} ∧ right.inventory.configuration.present = {7, 99, 100} :=
  ⟨⟨leftPath⟩, ⟨rightPath⟩, ⟨correspondence⟩, rfl, rfl, rfl, rfl, by decide +kernel, by decide +kernel⟩

theorem both_aliased_read_equations_survive_in_the_joint_store :
    left.inventory.configuration.equations.length = 4 ∧ right.inventory.configuration.equations.length = 4 ∧
      reader.count = 3 ∧ consumer.count = 2 := ⟨rfl, rfl, rfl, rfl⟩

theorem joint_equations_change_order_but_are_not_erased :
    left.inventory.configuration.equations ≠ right.inventory.configuration.equations := by
  intro same
  have formula := (Interaction.two_target_equations reader consumer prior rfl independent.orders.1).symm.trans
    (same.trans (Interaction.two_target_equations consumer reader prior rfl independent.orders.2))
  have changed := congrArg (fun equations : EquationStore (Term (signature base (twiceDeclarations locals captures)) [] ()) =>
    (equations.drop 1).head?.map (fun equation => termSize equation.1)) formula
  change some 1 = some 3 at changed
  cases changed

theorem unequal_port_counts_require_different_scope_maps :
    correspondence.names (earlier (V := Nat) (Mettapedia.Logic.LP.ScopedVar.at 8 0)) =
        later (V := Nat) (Mettapedia.Logic.LP.ScopedVar.at 11 0) ∧
      correspondence.names (later (V := Nat) (Mettapedia.Logic.LP.ScopedVar.at 12 0)) =
        earlier (V := Nat) (Mettapedia.Logic.LP.ScopedVar.at 8 0) := by
  constructor
  · change later (V := Nat) (scopeMap (Equiv.swap 8 11) (Mettapedia.Logic.LP.ScopedVar.at 8 0)) = _
    rfl
  · change earlier (V := Nat) (scopeMap (Equiv.swap 12 8) (Mettapedia.Logic.LP.ScopedVar.at 12 0)) = _
    rfl

theorem initial_captures_remain_fixed (name : Nat) :
    correspondence.names (namesAlong leftPath name) = namesAlong rightPath name :=
  actual_original_captures_fixed reader consumer prior rfl independent name

def secondReader : Interaction initial :=
  { consumer with
    taken := []
    read := [7]
    take_distinct := by decide
    take_available := by decide
    read_available := by decide
    take_read_apart := by decide
    template := by intro occurrence _; exact row_template occurrence }

theorem two_events_may_share_the_same_read_occurrence :
    reader.Independent secondReader ∧
      Nonempty (Quiver.Path initial (reader.twoTarget secondReader prior rfl
        ((Interaction.independent_iff_disjoint reader secondReader).mpr (by decide)).orders.1)) := by
  refine ⟨(Interaction.independent_iff_disjoint _ _).mpr (by decide), ?_⟩
  exact ⟨reader.twoPath secondReader prior rfl _⟩

def readOne : Interaction initial :=
  { secondReader with
    made := []
    distinct := by decide
    fresh := by decide
    covered := by intro _ member; cases member }

def takeOne : Interaction initial :=
  { consumer with
    made := []
    distinct := by decide
    fresh := by decide
    covered := by intro _ member; cases member
    taken := [7]
    take_distinct := by decide
    take_available := by decide
    take_read_apart := by decide
    template := by intro occurrence _; exact row_template occurrence }

theorem read_then_take_is_allowed : readOne.CanFollow takeOne := by
  simp [Interaction.CanFollow, Clash, Spoils, WritesInto, Interaction.selection, Selection.commit,
    readOne, takeOne, secondReader, consumer]

def readTakePath := readOne.twoPath takeOne prior rfl read_then_take_is_allowed

theorem the_asymmetric_order_is_an_actual_source_execution :
    selections readTakePath = [⟨[], [7], []⟩, ⟨[7], [], []⟩] ∧ fuels readTakePath = [1, 1] := ⟨rfl, rfl⟩

theorem read_and_take_are_not_independent : ¬ readOne.Independent takeOne := by
  rw [Interaction.independent_iff_disjoint]
  decide

theorem no_source_firing_can_read_the_consumed_occurrence
    {target : Endpoint locals Nat [] ()} (edge : Firing locals (takeOne.target prior rfl) target) :
    7 ∉ edge.selection.read := by
  intro member
  have present := edge.admitted.occurrences.kept_subset (by simpa [Selection.commit] using member)
  exact (by decide +kernel : 7 ∉ (takeOne.target prior rfl).inventory.configuration.present) present

theorem physical_independence_does_not_justify_guard_transport :
    Independent (fun _ : Nat => ()) (ContextualPathSnapshotControls.tell.commit (T := Unit))
      ContextualPathSnapshotControls.tell.commit ∧
    ∃ target : Endpoint locals Nat [] (),
      ∃ edge : Firing locals ContextualProcessInterference.initial target,
        edge.selection = ContextualPathSnapshotControls.tell ∧
        ¬ (ContextualProcessInterference.beforeQuestion.map
          (pathAssignment (Quiver.Hom.toPath edge))).Holds locals ∧
        ContextualGuardSemantics.Ask locals target.inventory.configuration.equations target.inventory.rows
          target.inventory.configuration.present
          ((Check.count ContextualGuardSemantics.Controls.query 1).map
            (instantiate (pathAssignment (Quiver.Hom.toPath edge)))) := by
  constructor
  · simp [Independent, Clash, Spoils, WritesInto, Selection.commit, ContextualPathSnapshotControls.tell]
  · obtain ⟨target, edge, selected, _taken, _read, _made, _world, oldCut, current⟩ :=
      ContextualProcessInterference.an_actual_equation_only_firing_changes_the_current_count_but_not_the_old_cut
    exact ⟨target, edge, selected, oldCut, current⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedControls
