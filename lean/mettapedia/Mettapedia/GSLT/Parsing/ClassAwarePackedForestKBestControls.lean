import Mettapedia.GSLT.Parsing.ClassAwarePackedForestKBest

/-!
# Physical ambiguity and topology controls for shared packed k-best

Two lexical alternatives share one node cache. Each of two physical parent
rows reads that cache twice, with an EOF terminal between the reads. The
eight tied derivations remain distinct. The examples also separate acyclic
storage validation from semantic parser replay.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwarePackedForestKBest.Controls

open ClassAwarePackedForest
open Mettapedia.Algorithms
open ClassAwareParserPackCorrespondence ClassAwareParserPackCertificate
open ParserProfileSemantics PresentationExprSemantics

def leaf : NodeKey := ⟨"A", 0, 0⟩
def root : NodeKey := ⟨"Root", 0, 0⟩
def keys : List NodeKey := [leaf, root]

def lexical (position : Nat) : Family :=
  ⟨leaf, .lexical position, [.terminal .eof 0 0]⟩

def structural (position : Nat) : Family :=
  ⟨root, .structural position, [.node leaf, .terminal .eof 0 0, .node leaf]⟩

def forest : Forest := ⟨[root], [lexical 0, lexical 1, structural 0, structural 1]⟩

def charge (family : Family) : Nat := match family.production with
  | .lexical _ => 1
  | .structural _ => 0

theorem valid : ValidTopology forest keys := by decide

def answers (requested : Nat) : List SharedKBest.Derivation :=
  (solve forest keys valid charge requested ⟨1, by decide⟩).cache.values

theorem seven_retained : (answers 7).length = 7 := by decide
theorem exhausted_eight : (answers 9).length = 8 := by decide
theorem ties_retained : (answers 9).map SharedKBest.cost = [2, 2, 2, 2, 2, 2, 2, 2] := by decide
theorem zero_demand : answers 0 = [] := rfl

theorem answers_correct (requested : Nat) :
    DerivationPrefix.Correct requested SharedKBest.cost (Unfolding forest keys charge 1)
      (answers requested) := solve_correct forest keys valid charge requested ⟨1, by decide⟩

def rowOf : SharedKBest.Derivation → Nat
  | .node _ row _ _ => row

def childRows : SharedKBest.Derivation → List Nat
  | .node _ _ _ children => children.map rowOf

/-- Sharing does not conflate two uses with one correlated rank choice. -/
theorem mixed_choices_left : [0, 1] ∈ (answers 9).map childRows := by decide
theorem mixed_choices_right : [1, 0] ∈ (answers 9).map childRows := by decide
theorem first_physical_row_four : ((answers 9).filter (fun value => rowOf value == 0)).length = 4 := by decide
theorem second_physical_row_four : ((answers 9).filter (fun value => rowOf value == 1)).length = 4 := by decide

theorem original_production_rows :
    ((answers 9).filterMap (fun value =>
      (metadata forest keys value).map Family.production)).count (.structural 0) = 4 ∧
    ((answers 9).filterMap (fun value =>
      (metadata forest keys value).map Family.production)).count (.structural 1) = 4 := by decide

def leftChoice : SharedKBest.Derivation := .node 0 0 1 []
def rightChoice : SharedKBest.Derivation := .node 0 1 1 []

theorem ordered_terminal_restored :
    restoreChildren keys (structural 0).children [leftChoice, rightChoice] =
      some [.node leaf, .terminal .eof 0 0, .node leaf] := by decide

theorem missing_child_rejected :
    restoreChildren keys (structural 0).children [leftChoice] = none := by decide

theorem extra_child_rejected :
    restoreChildren keys (structural 0).children [leftChoice, rightChoice, leftChoice] = none := by decide

theorem wrong_topology_rejected : validate forest [root, leaf] = false := by decide
theorem missing_child_key_rejected : validate forest [root] = false := by decide
theorem duplicate_key_rejected : validate forest [leaf, root, leaf] = false := by decide
theorem missing_root_rejected : validate ⟨[⟨"Other", 0, 0⟩], forest.families⟩ keys = false := by decide
theorem duplicate_family_rejected :
    validate ⟨[root], lexical 0 :: forest.families⟩ keys = false := by decide

def selfCycle : Forest := ⟨[root], [⟨root, .structural 0, [.node root]⟩]⟩
def twoCycle : Forest :=
  ⟨[root], [⟨root, .structural 0, [.node leaf]⟩, ⟨leaf, .structural 1, [.node root]⟩]⟩

theorem self_cycle_rejected : validate selfCycle [root] = false := by decide
theorem two_cycle_rejected : validate twoCycle keys = false := by decide

/-- Neither an invented physical family row nor a target-only derivation
can pass the proved two-sided storage correspondence. -/
theorem spurious_row_refused : ¬ Unfolding forest keys charge 1 (.node 1 99 0 []) := by
  intro spurious
  obtain ⟨family, _, recovered⟩ := unfolding_metadata forest keys charge spurious
  have absent : metadata forest keys (.node 1 99 0 []) = none := by decide
  rw [absent] at recovered
  contradiction

theorem target_cannot_invent_row :
    ¬ SharedKBest.Source (compile forest keys valid charge) ⟨1, by decide⟩ (.node 1 99 0 []) := by
  intro target
  exact spurious_row_refused ((source_iff forest keys valid charge ⟨1, by decide⟩ _).mp target)

def emptyPlan : CompiledParserPackPlan := ⟨⟨"empty", "A", [], []⟩, []⟩

/-- Storage topology supplies no authority to use an absent grammar row. -/
theorem storage_is_not_replay (profile : ParserProfileLayer) (input : List Nat)
    (tree : CST) : ¬ Nonempty (Replays profile emptyPlan input (.lexical 0 .eof 0 0) "A" 0 0 tree) := by
  rintro ⟨replay⟩
  cases replay with
  | lexical _ valid _ _ _ _ => exact Nat.not_lt_zero _ valid

end Mettapedia.GSLT.Parsing.ClassAwarePackedForestKBest.Controls
