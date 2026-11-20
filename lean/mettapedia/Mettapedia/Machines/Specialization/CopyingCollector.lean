import Mettapedia.Machines.RationalTermGraph
import Mettapedia.Machines.GraphInspection
import Mathlib.Data.List.Dedup

/-!
# Copying the reachable portion of an ordered term graph

The collector discovers each node once and scans its children in a queue.
Copying uses the existing finite graph admission and position maps. Rows
retain their labels and exact child lists. Keys are abstract, so cycles
and sharing require no particular word encoding or slot layout.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Specialization.CopyingCollector

open RationalTermGraph

variable {Address Label : Type} [DecidableEq Address]

def Live (graph : Graph Address Label) (roots : List Address) (address : Address) : Prop :=
  ∃ root ∈ roots, GraphInspection.Reached graph.children (fun _ => false) root address

omit [DecidableEq Address] in
private theorem root_live (graph : Graph Address Label) {roots : List Address}
    {root : Address} (present : root ∈ roots) : Live graph roots root :=
  ⟨root, present, .root⟩

omit [DecidableEq Address] in
private theorem child_live {graph : Graph Address Label} {roots : List Address} {node child : Address}
    (live : Live graph roots node) (linked : child ∈ graph.children node) : Live graph roots child := by
  obtain ⟨root, atRoot, reached⟩ := live
  exact ⟨root, atRoot, .child reached rfl linked⟩

structure Inventory (graph : Graph Address Label) (roots : List Address) where
  order : List Address
  once : order.Nodup
  exactLive : ∀ address, address ∈ order ↔ Live graph roots address

private structure Scanning (graph : Graph Address Label) (roots seen todo : List Address) : Prop where
  once : (seen ++ todo).Nodup
  rootsKept : roots ⊆ seen ++ todo
  reached : ∀ node ∈ seen ++ todo, Live graph roots node
  scanned : ∀ node ∈ seen, graph.children node ⊆ seen ++ todo

private def newChildren (graph : Graph Address Label) (node : Address) (known : List Address) : List Address :=
  (graph.children node).dedup.filter fun child => decide (child ∉ known)

private theorem visit {graph : Graph Address Label} {roots seen todo : List Address} {node : Address}
    (scan : Scanning graph roots seen (node :: todo)) :
    Scanning graph roots (seen ++ [node]) (todo ++ newChildren graph node (seen ++ node :: todo)) := by
  let known := seen ++ node :: todo
  let children := newChildren graph node known
  have exactList : (seen ++ [node]) ++ (todo ++ children) = known ++ children := by
    simp [known, List.append_assoc]
  have reachedNode : Live graph roots node := scan.reached node (by simp)
  have newMem (child : Address) : child ∈ children ↔ child ∈ graph.children node ∧ child ∉ known := by
    simp [children, newChildren]
  have carried (address : Address) (inside : address ∈ known) : address ∈ known ++ children :=
    List.mem_append_left _ inside
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [exactList]
    apply List.Nodup.append scan.once ((List.nodup_dedup _).filter _)
    intro address listed added
    exact (newMem address).mp added |>.2 listed
  · rw [exactList]
    exact fun address present => carried address (scan.rootsKept present)
  · rw [exactList]
    intro address present
    rcases List.mem_append.mp present with seen | added
    · exact scan.reached _ seen
    · exact child_live reachedNode ((newMem address).mp added).1
  · rw [exactList]
    intro address processed child linked
    rcases List.mem_append.mp processed with earlier | here
    · exact carried child (scan.scanned address earlier linked)
    · have same : address = node := List.mem_singleton.mp here
      subst address
      by_cases knownChild : child ∈ known
      · exact carried child knownChild
      · exact List.mem_append_right _ ((newMem child).mpr ⟨linked, knownChild⟩)

omit [DecidableEq Address] in
private def finish {graph : Graph Address Label} {roots seen : List Address}
    (scan : Scanning graph roots seen []) : Inventory graph roots where
  order := seen
  once := by simpa using scan.once
  exactLive address := by
    constructor
    · intro present
      exact scan.reached address (by simpa using present)
    · rintro ⟨root, present, along⟩
      induction along with
      | root => simpa using scan.rootsKept present
      | child _ _ edge parent =>
        have kept := scan.scanned _ parent edge
        simpa using kept

private def scanQueue (graph : Graph Address Label) (roots : List Address) :
    Nat → (seen todo : List Address) → Scanning graph roots seen todo → Option (Inventory graph roots)
  | _, _, [], scan => some (finish scan)
  | 0, _, _ :: _, _ => none
  | limit + 1, seen, node :: todo, scan =>
    scanQueue graph roots limit (seen ++ [node]) (todo ++ newChildren graph node (seen ++ node :: todo)) (visit scan)

private theorem scan_has_room (graph : Graph Address Label) (roots : List Address)
    (carrier : Finset Address) (finite : ∀ node, Live graph roots node → node ∈ carrier)
    (capacity : Nat) (seen todo : List Address) (scanning : Scanning graph roots seen todo)
    (enough : carrier.card ≤ seen.length + capacity) :
    (scanQueue graph roots capacity seen todo scanning).isSome = true := by
  induction capacity generalizing seen todo with
  | zero =>
    cases todo with
    | nil => rfl
    | cons next later =>
      have contained : (seen ++ next :: later).toFinset ⊆ carrier := by
        intro node included
        exact finite node (scanning.reached node (List.mem_toFinset.mp included))
      have bound := Finset.card_le_card contained
      rw [List.toFinset_card_of_nodup scanning.once, List.length_append, List.length_cons] at bound
      omega
  | succ capacity rest =>
    cases todo with
    | nil => rfl
    | cons next later =>
      rw [scanQueue]
      apply rest
      simp only [List.length_append, List.length_singleton]
      omega

private theorem start (graph : Graph Address Label) (roots : List Address) :
    Scanning graph roots [] roots.dedup :=
  ⟨by simpa using List.nodup_dedup roots, by simp [List.subset_def],
    by simpa using (fun node present => root_live graph (List.mem_dedup.mp present)), by simp⟩

def discover (graph : Graph Address Label) (roots : List Address) (capacity : Nat) :
    Option (Inventory graph roots) :=
  scanQueue graph roots capacity [] roots.dedup (start graph roots)

theorem discover_with_room (graph : Graph Address Label) (roots : List Address)
    (carrier : Finset Address) (finite : ∀ node, Live graph roots node → node ∈ carrier)
    (capacity : Nat) (enough : carrier.card ≤ capacity) :
    (discover graph roots capacity).isSome = true :=
  scan_has_room graph roots carrier finite capacity [] roots.dedup (start graph roots) (by simpa using enough)

def row (graph : Graph Address Label) (node : Address) : KeyedRow Address Label :=
  ⟨node, graph.label node, graph.children node⟩

def Inventory.table {graph : Graph Address Label} {roots : List Address} (inventory : Inventory graph roots) :
    KeyedTable Address Label where
  rows := inventory.order.map (row graph)
  valid := by
    have keys : (inventory.order.map (row graph)).map KeyedRow.key = inventory.order := by
      simp [row, List.map_map, Function.comp_def]
    rw [KeyedInventoryValid, keys]
    refine ⟨inventory.once, ?_⟩
    intro copied member node linked
    obtain ⟨source, included, rfl⟩ := List.mem_map.mp member
    exact (inventory.exactLive node).mpr (child_live ((inventory.exactLive _).mp included) linked)

def collect (graph : Graph Address Label) (roots : List Address) (capacity : Nat) :
    Option (KeyedTable Address Label) :=
  (discover graph roots capacity).map Inventory.table

omit [DecidableEq Address] in
theorem Inventory.has_exact_keys {graph : Graph Address Label} {roots : List Address}
    (inventory : Inventory graph roots) (address : Address) :
    address ∈ inventory.table.rows.map KeyedRow.key ↔ Live graph roots address := by
  simpa [Inventory.table, List.map_map, Function.comp_def, row] using inventory.exactLive address

/-- The copied table retains the label and every outgoing occurrence of
each live node. Repeated edges can resolve to the same finite position. -/
theorem Inventory.reads_copy {graph : Graph Address Label} {roots : List Address}
    (inventory : Inventory graph roots) (address : Address) (live : Live graph roots address) :
    ∃ node, inventory.table.node? address = some node ∧
      inventory.table.graph.label node = graph.label address ∧
      (inventory.table.graph.children node).map inventory.table.key = graph.children address := by
  obtain ⟨node, found⟩ := inventory.table.node?_complete address ((inventory.has_exact_keys address).mpr live)
  have rowPresent : row graph address ∈ inventory.table.rows :=
    List.mem_map.mpr ⟨address, (inventory.exactLive address).mpr live, rfl⟩
  have read := lookupKeyed_of_member inventory.table.valid.1 _ rowPresent
  exact ⟨node, found, inventory.table.node?_graph_readback address node _ found read⟩

theorem Inventory.relocates_terms {graph : Graph Address Label} {roots : List Address}
    (inventory : Inventory graph roots) {address : Address} {node : inventory.table.Node}
    (found : inventory.table.node? address = some node) : Bisimilar graph inventory.table.graph address node := by
  have key := (inventory.table.node?_eq_some_iff address node).mp found
  refine ⟨fun prior copied => prior = inventory.table.key copied, ?_, key.symm⟩
  intro prior copied attached
  subst prior
  have live := (inventory.has_exact_keys _).mp (inventory.table.key_mem copied)
  obtain ⟨recovered, lookup, label, children⟩ := inventory.reads_copy _ live
  have same := Option.some.inj ((inventory.table.node?_key copied).symm.trans lookup)
  subst recovered
  refine ⟨label.symm, ?_⟩
  rw [← children, List.forall₂_map_left_iff]
  exact List.forall₂_same.mpr fun _ _ => rfl

namespace Controls

private def sharedCycle : Graph Nat String where
  label node := if node = 0 then "branch" else "leaf"
  children node := if node = 0 then [1, 1] else [0]

theorem a_cycle_copies_each_node_once :
    (collect sharedCycle [0, 0] 2).map (fun table => table.rows.map KeyedRow.key) = some [0, 1] := by
  decide +kernel

theorem refusal_does_not_publish_a_partial_table :
    (collect sharedCycle [0, 0] 1).isNone = true := by decide +kernel

theorem repeated_children_keep_their_alias :
    (collect sharedCycle [0, 0] 2).map (fun table =>
      table.rows.map KeyedRow.children) = some [[1, 1], [0]] := by decide +kernel

end Controls

end Mettapedia.Machines.Specialization.CopyingCollector
