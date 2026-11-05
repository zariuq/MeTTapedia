import Mettapedia.GSLT.Parsing.ClassAwareNativeForestFamilyCompleteness
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

/-!
# Root closure by frontier rounds

`validateReachable` recomputes the successors of every reached node in each
round, scanning all choices for each node and removing duplicates by list
search. The rounds below compute the same closure from a successor table built
once: each round expands only the nodes first reached in the previous round,
and reached nodes live in a hash set. Whenever every choice names an in-range
parent, which array coherence guarantees, the two checks agree, so the
validators built on this one keep every soundness theorem of the originals.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareNativeForestReachabilityFrontier

open Mettapedia.GSLT.Parsing.ClassAwareNativeForestContract
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestReachabilityValidation
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestStructuralValidation
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestIdentityInventory
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestTerminalValidation
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestFamilyWitness
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestFamilyCompleteness
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.ParserProfileSemantics

/-! ## Successor table -/

def addChoice (table : Std.HashMap Nat (List Nat)) (choice : Choice) :
    Std.HashMap Nat (List Nat) :=
  table.insert choice.parent (choiceTargets choice ++ table.getD choice.parent [])

/-- Successors by parent, built in one pass over the choices. -/
def successorTable (view : ForestView) : Std.HashMap Nat (List Nat) :=
  view.choices.foldl addChoice {}

theorem mem_foldl_addChoice (choices : List Choice) (table : Std.HashMap Nat (List Nat))
    (parent child : Nat) :
    child ∈ (choices.foldl addChoice table).getD parent [] ↔
      child ∈ table.getD parent [] ∨
        child ∈ (choices.filter fun choice => choice.parent == parent).flatMap choiceTargets := by
  induction choices generalizing table with
  | nil => simp
  | cons first rest ih =>
    rw [List.foldl_cons, ih]
    by_cases same : first.parent = parent
    · subst same
      simp only [addChoice, Std.HashMap.getD_insert, beq_self_eq_true, if_true,
        List.mem_append, List.filter_cons, List.flatMap_cons]
      tauto
    · have different : (first.parent == parent) = false := by simpa using same
      simp only [addChoice, Std.HashMap.getD_insert, different, Bool.false_eq_true, if_false,
        List.filter_cons]

theorem mem_successorTable (view : ForestView) (parent child : Nat) :
    child ∈ (successorTable view).getD parent [] ↔ child ∈ nodeSuccessors view parent := by
  simp [successorTable, mem_foldl_addChoice, nodeSuccessors]

/-! ## Frontier rounds -/

structure Search where
  reached : Std.HashSet Nat
  frontier : List Nat

/-- Reach one candidate node if it is in range and not reached yet. -/
def visit (bound : Nat) (search : Search) (node : Nat) : Search :=
  if node < bound ∧ ¬ search.reached.contains node = true then
    ⟨search.reached.insert node, node :: search.frontier⟩
  else search

theorem visit_all (bound : Nat) (nodes : List Nat) (search : Search) (node : Nat) :
    ((nodes.foldl (visit bound) search).reached.contains node = true ↔
      search.reached.contains node = true ∨ (node < bound ∧ node ∈ nodes)) ∧
    (node ∈ (nodes.foldl (visit bound) search).frontier ↔
      node ∈ search.frontier ∨
        (node < bound ∧ node ∈ nodes ∧ ¬ search.reached.contains node = true)) := by
  induction nodes generalizing search with
  | nil => simp
  | cons first rest ih =>
    rw [List.foldl_cons]
    obtain ⟨reachedIh, frontierIh⟩ := ih (visit bound search first)
    rw [reachedIh, frontierIh]
    by_cases fresh : first < bound ∧ ¬ search.reached.contains first = true
    · have reached : (visit bound search first).reached = search.reached.insert first := by
        simp [visit, fresh]
      have frontier : (visit bound search first).frontier = first :: search.frontier := by
        simp [visit, fresh]
      rw [reached, frontier, Std.HashSet.contains_insert]
      by_cases equal : first = node
      · subst equal
        simp only [beq_self_eq_true, Bool.true_or, List.mem_cons, true_or]
        exact ⟨iff_of_true trivial (Or.inr ⟨fresh.1, trivial⟩),
          iff_of_true trivial (Or.inr ⟨fresh.1, trivial, fresh.2⟩)⟩
      · have different : (first == node) = false := by simpa using equal
        have different' : ¬ node = first := fun h => equal h.symm
        simp only [different, Bool.false_or, List.mem_cons, different', false_or]
        exact ⟨trivial, trivial⟩
    · have unchanged : visit bound search first = search := by
        unfold visit
        rw [if_neg fresh]
      rw [unchanged]
      by_cases equal : first = node
      · subst equal
        have decided : first < bound → search.reached.contains first = true := by
          intro bounded
          by_contra absent
          exact fresh ⟨bounded, absent⟩
        simp only [List.mem_cons, true_or, and_true]
        refine ⟨⟨fun h => h.elim Or.inl (fun h => Or.inr h.1),
            fun h => h.elim Or.inl (fun h => Or.inl (decided h))⟩,
          ⟨fun h => h.elim Or.inl (fun h => Or.inr ⟨h.1, trivial, h.2.2⟩),
            fun h => h.elim Or.inl (fun h => absurd (decided h.1) h.2.2)⟩⟩
      · have different' : ¬ node = first := fun h => equal h.symm
        simp only [List.mem_cons, different', false_or]
        exact ⟨trivial, trivial⟩

/-- One round: reach the in-range successors of the frontier. -/
def expandParent (table : Std.HashMap Nat (List Nat)) (bound : Nat) (search : Search)
    (parent : Nat) : Search :=
  (table.getD parent []).foldl (visit bound) search

def step (table : Std.HashMap Nat (List Nat)) (bound : Nat) (search : Search) : Search :=
  search.frontier.foldl (expandParent table bound) ⟨search.reached, []⟩

theorem expandParent_all (table : Std.HashMap Nat (List Nat)) (bound : Nat) (parents : List Nat)
    (search : Search) (node : Nat) :
    ((parents.foldl (expandParent table bound) search).reached.contains node = true ↔
      search.reached.contains node = true ∨
        (node < bound ∧ ∃ parent ∈ parents, node ∈ table.getD parent [])) ∧
    (node ∈ (parents.foldl (expandParent table bound) search).frontier ↔
      node ∈ search.frontier ∨
        (node < bound ∧ (∃ parent ∈ parents, node ∈ table.getD parent []) ∧
          ¬ search.reached.contains node = true)) := by
  induction parents generalizing search with
  | nil => simp
  | cons first rest ih =>
    rw [List.foldl_cons]
    obtain ⟨reachedIh, frontierIh⟩ := ih (expandParent table bound search first)
    obtain ⟨reachedOne, frontierOne⟩ := visit_all bound (table.getD first []) search node
    simp only [expandParent] at reachedIh frontierIh ⊢
    rw [reachedIh, frontierIh, reachedOne, frontierOne]
    simp only [List.mem_cons, exists_eq_or_imp]
    clear reachedIh frontierIh reachedOne frontierOne ih
    generalize (node ∈ table.getD first []) = here
    generalize (∃ parent ∈ rest, node ∈ table.getD parent []) = later
    generalize (search.reached.contains node) = known
    generalize (node ∈ search.frontier) = pending
    generalize (node < bound) = bounded
    tauto

theorem step_all (table : Std.HashMap Nat (List Nat)) (bound : Nat) (search : Search) (node : Nat) :
    ((step table bound search).reached.contains node = true ↔
      search.reached.contains node = true ∨
        (node < bound ∧ ∃ parent ∈ search.frontier, node ∈ table.getD parent [])) ∧
    (node ∈ (step table bound search).frontier ↔
      node < bound ∧ (∃ parent ∈ search.frontier, node ∈ table.getD parent []) ∧
        ¬ search.reached.contains node = true) := by
  have all := expandParent_all table bound search.frontier ⟨search.reached, []⟩ node
  simpa [step] using all

def rounds (table : Std.HashMap Nat (List Nat)) (bound : Nat) : Nat → Search → Search
  | 0, search => search
  | count + 1, search => rounds table bound count (step table bound search)

def start (view : ForestView) : Search :=
  view.roots.foldl (visit view.nodes.length) ⟨{}, []⟩

/-- Every in-range node lies in the root closure computed by frontier rounds. -/
def validateReachableFrontier (view : ForestView) : Bool :=
  let reached :=
    (rounds (successorTable view) view.nodes.length view.nodes.length (start view)).reached
  (List.range view.nodes.length).all fun index => reached.contains index

/-! ## Agreement with the original rounds -/

/-- After `count` rounds the search holds the in-range part of the original
closure after `count` rounds, and every reached node off the frontier already
has its in-range successors reached. -/
structure Tracks (view : ForestView) (count : Nat) (search : Search) : Prop where
  reached : ∀ node, search.reached.contains node = true ↔
    node < view.nodes.length ∧ node ∈ reachableWithin view count
  frontier : ∀ node, node ∈ search.frontier →
    node < view.nodes.length ∧ node ∈ reachableWithin view count
  settled : ∀ node, node < view.nodes.length → node ∈ reachableWithin view count →
    node ∉ search.frontier → ∀ child, child ∈ nodeSuccessors view node →
      child < view.nodes.length → child ∈ reachableWithin view count

theorem mem_reachableWithin_succ (view : ForestView) (count node : Nat) :
    node ∈ reachableWithin view (count + 1) ↔
      node ∈ reachableWithin view count ∨
        ∃ parent ∈ reachableWithin view count, node ∈ nodeSuccessors view parent := by
  simp [reachableWithin, expand, List.mem_eraseDups, List.mem_append, List.mem_flatMap]

theorem tracks_start (view : ForestView) : Tracks view 0 (start view) := by
  have all := fun node => visit_all view.nodes.length view.roots ⟨{}, []⟩ node
  refine ⟨?_, ?_, ?_⟩
  · intro node
    rw [start, (all node).1]
    simp [reachableWithin, List.mem_eraseDups]
  · intro node member
    rw [start, (all node).2] at member
    simp only [Std.HashSet.contains_empty, List.not_mem_nil, false_or] at member
    exact ⟨member.1, by simp [reachableWithin, List.mem_eraseDups, member.2.1]⟩
  · intro node bounded member absent
    exfalso
    apply absent
    rw [start, (all node).2]
    simp only [Std.HashSet.contains_empty, List.not_mem_nil, false_or]
    exact ⟨bounded, by simpa [reachableWithin, List.mem_eraseDups] using member, by simp⟩

theorem parent_in_range {view : ForestView}
    (parents : ∀ choice ∈ view.choices, choice.parent < view.nodes.length)
    {parent child : Nat} (successor : child ∈ nodeSuccessors view parent) :
    parent < view.nodes.length := by
  simp only [nodeSuccessors, List.mem_flatMap, List.mem_filter, beq_iff_eq] at successor
  obtain ⟨choice, ⟨member, exact⟩, -⟩ := successor
  exact exact ▸ parents choice member

theorem tracks_step {view : ForestView}
    (parents : ∀ choice ∈ view.choices, choice.parent < view.nodes.length)
    {count : Nat} {search : Search} (tracks : Tracks view count search) :
    Tracks view (count + 1) (step (successorTable view) view.nodes.length search) := by
  have stepAll := fun node => step_all (successorTable view) view.nodes.length search node
  have reachedStep : ∀ node,
      (step (successorTable view) view.nodes.length search).reached.contains node = true ↔
        node < view.nodes.length ∧ node ∈ reachableWithin view (count + 1) := by
    intro node
    rw [(stepAll node).1, tracks.reached node, mem_reachableWithin_succ]
    simp only [mem_successorTable]
    constructor
    · rintro (⟨bounded, member⟩ | ⟨bounded, parent, frontierMember, successor⟩)
      · exact ⟨bounded, Or.inl member⟩
      · exact ⟨bounded, Or.inr ⟨parent, (tracks.frontier parent frontierMember).2, successor⟩⟩
    · rintro ⟨bounded, member | ⟨parent, parentMember, successor⟩⟩
      · exact Or.inl ⟨bounded, member⟩
      · by_cases onFrontier : parent ∈ search.frontier
        · exact Or.inr ⟨bounded, parent, onFrontier, successor⟩
        · exact Or.inl ⟨bounded, tracks.settled parent (parent_in_range parents successor)
            parentMember onFrontier node successor bounded⟩
  refine ⟨reachedStep, ?_, ?_⟩
  · intro node member
    rw [(stepAll node).2] at member
    obtain ⟨bounded, ⟨parent, frontierMember, successor⟩, -⟩ := member
    rw [mem_successorTable] at successor
    exact ⟨bounded, (mem_reachableWithin_succ view count node).2
      (Or.inr ⟨parent, (tracks.frontier parent frontierMember).2, successor⟩)⟩
  · intro node bounded member absent child successor childBounded
    by_cases old : node ∈ reachableWithin view count
    · by_cases onFrontier : node ∈ search.frontier
      · have reachedChild :
            (step (successorTable view) view.nodes.length search).reached.contains child = true := by
          rw [(stepAll child).1]
          exact Or.inr ⟨childBounded, node, onFrontier, (mem_successorTable view node child).2 successor⟩
        exact ((reachedStep child).1 reachedChild).2
      · exact (mem_reachableWithin_succ view count child).2
          (Or.inl (tracks.settled node bounded old onFrontier child successor childBounded))
    · exfalso
      apply absent
      have reachedNode := (reachedStep node).2 ⟨bounded, member⟩
      rw [(stepAll node).1] at reachedNode
      rcases reachedNode with present | ⟨-, parent, frontierMember, successorNode⟩
      · exact absurd ((tracks.reached node).1 present).2 old
      · rw [(stepAll node).2]
        exact ⟨bounded, ⟨parent, frontierMember, successorNode⟩,
          fun present => old ((tracks.reached node).1 present).2⟩

theorem tracks_rounds {view : ForestView}
    (parents : ∀ choice ∈ view.choices, choice.parent < view.nodes.length) :
    ∀ (extra count : Nat) (search : Search), Tracks view count search →
      Tracks view (count + extra) (rounds (successorTable view) view.nodes.length extra search)
  | 0, count, search, tracks => by simpa [rounds] using tracks
  | extra + 1, count, search, tracks => by
      have next := tracks_rounds parents extra (count + 1) _ (tracks_step parents tracks)
      rw [show count + (extra + 1) = count + 1 + extra by omega]
      simpa [rounds] using next

theorem all_congr {α : Type} {xs : List α} {f g : α → Bool}
    (same : ∀ x ∈ xs, f x = g x) : xs.all f = xs.all g := by
  induction xs with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.all_cons]
    rw [same first (by simp), ih (fun x member => same x (by simp [member]))]

/-- The frontier check agrees with the original whenever every choice names an
in-range parent. -/
theorem validateReachableFrontier_eq (view : ForestView)
    (parents : ∀ choice ∈ view.choices, choice.parent < view.nodes.length) :
    validateReachableFrontier view = validateReachable view := by
  have tracks := tracks_rounds parents view.nodes.length 0 (start view) (tracks_start view)
  rw [Nat.zero_add] at tracks
  unfold validateReachableFrontier validateReachable
  simp only [(reachableCached_exact view view.nodes.length).1]
  apply all_congr
  intro index member
  have bounded : index < view.nodes.length := List.mem_range.mp member
  rw [Bool.eq_iff_iff, tracks.reached index, decide_eq_true_iff]
  exact ⟨fun h => h.2, fun h => ⟨bounded, h⟩⟩

theorem parents_in_range_of_arrays {view : ForestView} (accepted : validateArrays view = true) :
    ∀ choice ∈ view.choices, choice.parent < view.nodes.length := by
  intro choice member
  obtain ⟨index, choiceAt⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨parent, localIndex, parentAt, -, -, -⟩ :=
    (validateArrays_sound accepted).choicesOwned index choice choiceAt
  exact (List.getElem?_eq_some_iff.mp parentAt).1

/-! ## The validators over frontier rounds -/

def validateStructureFrontier (view : ForestView) : Bool :=
  validateArrays view && validateReachableFrontier view

theorem validateStructureFrontier_eq (view : ForestView) :
    validateStructureFrontier view = validateStructure view := by
  unfold validateStructureFrontier validateStructure
  cases arrays : validateArrays view with
  | false => rfl
  | true =>
    simp only [Bool.true_and]
    exact validateReachableFrontier_eq view (parents_in_range_of_arrays arrays)

def validateFamilyDecodingInputsFrontier (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) : Bool :=
  validateStructureFrontier view && validateForPlan view inventory plan &&
    validateTerminals view inventory profile

theorem validateFamilyDecodingInputsFrontier_eq (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) :
    validateFamilyDecodingInputsFrontier view inventory profile plan =
      validateFamilyDecodingInputs view inventory profile plan := by
  simp only [validateFamilyDecodingInputsFrontier, validateFamilyDecodingInputs,
    validateStructureFrontier_eq]

def validateRootedFamilyDecodingInputsFrontier (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) : Bool :=
  validateFamilyDecodingInputsFrontier view inventory profile plan &&
    validateRootKeys view inventory

theorem validateRootedFamilyDecodingInputsFrontier_eq (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) :
    validateRootedFamilyDecodingInputsFrontier view inventory profile plan =
      validateRootedFamilyDecodingInputs view inventory profile plan := by
  simp only [validateRootedFamilyDecodingInputsFrontier, validateRootedFamilyDecodingInputs,
    validateFamilyDecodingInputsFrontier_eq]

def validateExactFamilyRepresentationFrontier (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) : Bool :=
  validateRootedFamilyDecodingInputsFrontier view inventory profile plan &&
    (validatePrefixIndexOrder view && validateChoiceCoverage view inventory profile)

theorem validateExactFamilyRepresentationFrontier_eq (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) :
    validateExactFamilyRepresentationFrontier view inventory profile plan =
      validateExactFamilyRepresentation view inventory profile plan := by
  simp only [validateExactFamilyRepresentationFrontier, validateExactFamilyRepresentation,
    validateRootedFamilyDecodingInputsFrontier_eq]

/-! ## Controls -/

private def chainNode (choiceBegin choiceCount : Nat) : Node :=
  { kind := .epsilon, scalarStart := 0, scalarStop := 0, byteStart := 0, byteStop := 0,
    choiceBegin, choiceCount }

private def chainChoice (parent child : Nat) : Choice :=
  { parent, prefixNode := none, childNode := child, productionIndex := 0,
    scalarPivot := 0, bytePivot := 0 }

/-- A three-node chain: every node is reached in two rounds. -/
private def chainView : ForestView :=
  { nodes := [chainNode 0 1, chainNode 1 1, chainNode 2 0]
    choices := [chainChoice 0 1, chainChoice 1 2], roots := [0], codepoints := [],
    byteOffsets := [0] }

theorem chain_reached : validateReachableFrontier chainView = true := by
  rw [validateReachableFrontier_eq chainView (by decide)]
  decide

/-- The same chain with an unreachable fourth node. -/
theorem shadow_rejected :
    validateReachableFrontier { chainView with nodes := chainView.nodes ++ [chainNode 2 0] } =
      false := by
  rw [validateReachableFrontier_eq _ (by decide)]
  decide

#print axioms validateReachableFrontier_eq
#print axioms validateExactFamilyRepresentationFrontier_eq

end Mettapedia.GSLT.Parsing.ClassAwareNativeForestReachabilityFrontier
