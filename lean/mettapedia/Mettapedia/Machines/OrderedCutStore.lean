import Mettapedia.Machines.FiniteCutCatalogue
import Mettapedia.GSLT.Dynamics.PartialRegionPlan

/-!
# Ordered occurrence stores with checked cut transfer and finite planning

Rows retain both occurrence identity and authored sequence order. Re-cutting
validates every old row before constructing a completed transfer; malformed
input refuses with the exact old rows, rather than silently dropping it.

The cell model shares each skeleton once and charges every occurrence's ID,
hole slots and materialized payload tree. It is an explicit abstract layout
model, not a claim about interned native IDs, allocator bytes or runtime cost.
Selection is minimal only within the bounded structural-cut catalogue.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedCutStore

open ShapeStore FiniteCutCatalogue
open Mettapedia.GSLT.Dynamics.PartialRegionPlan

variable {Id Atom : Type}

abbrev Facts (Id Atom : Type) := List (Id × Tm Atom)
abbrev Rows (Id Atom : Type) := List (Id × Row Atom)

def encode (mask : Mask) (facts : Facts Id Atom) : Rows Id Atom :=
  facts.map fun fact => (fact.1, mask.cut.d fact.2)

def decode : Rows Id Atom → Option (Facts Id Atom)
  | [] => some []
  | (id, row) :: rest => do
      let term ← reassemble row
      let later ← decode rest
      return (id, term) :: later

theorem decode_encode (mask : Mask) (facts : Facts Id Atom) : decode (encode mask facts) = some facts := by
  induction facts with
  | nil => rfl
  | cons fact rest ih =>
      simp only [encode, List.map_cons, decode, mask.cut.sec]
      change (decode (encode mask rest)).bind (fun later => some (fact :: later)) = _
      rw [ih]
      rfl

theorem normalize_encode (mask : Mask) (facts : Facts Id Atom) : encode (normalize mask) facts = encode mask facts := by
  unfold encode
  apply congrArg (fun f : (Id × Tm Atom) → Id × Row Atom => facts.map f)
  funext fact
  rw [normalize_cut]

def transfer (destination : Mask) (rows : Rows Id Atom) : Attempt (Rows Id Atom) (Rows Id Atom) :=
  match decode rows with
  | none => .declined rows
  | some facts => .committed (encode destination facts)

theorem transfer_restores (destination : Mask) : RestoresOnDecline (transfer (Id := Id) (Atom := Atom) destination) := by
  intro rows restored declined
  cases decoded : decode rows with
  | none =>
      have same : rows = restored := by simpa [transfer, decoded] using declined
      exact same.symm
  | some facts => simp [transfer, decoded] at declined

theorem completed_transfer_exact (destination : Mask) (before after : Rows Id Atom)
    (completed : transfer destination before = .committed after) : decode after = decode before := by
  cases decoded : decode before with
  | none => simp [transfer, decoded] at completed
  | some facts =>
      have same : encode destination facts = after := by simpa [transfer, decoded] using completed
      rw [← same, decode_encode]

theorem transfer_encoded (source destination : Mask) (facts : Facts Id Atom) :
    transfer destination (encode source facts) = .committed (encode destination facts) := by
  simp [transfer, decode_encode]

theorem ids_preserved (mask : Mask) (facts : Facts Id Atom) : (encode mask facts).map Prod.fst = facts.map Prod.fst := by
  simp [encode, List.map_map, Function.comp_def]

theorem occurrence_count_preserved (mask : Mask) (facts : Facts Id Atom) : (encode mask facts).length = facts.length := by
  simp [encode]

def matchFrom [DecidableEq Atom] (pattern : Pat Atom) (captured : Subst Atom) (row : Row Atom) : Option (Subst Atom) :=
  match matchSk pattern row.1 row.2 captured with
  | some (bindings, []) => some bindings
  | _ => none

theorem matchFrom_reassembled [DecidableEq Atom] (pattern : Pat Atom) (captured : Subst Atom)
    (row : Row Atom) (term : Tm Atom) (decoded : reassemble row = some term) :
    matchFrom pattern captured row = matchTm pattern term captured := by
  have filled : fill row.1 row.2 = some (term, []) := by
    unfold reassemble at decoded
    split at decoded
    next result found =>
      simp only [Option.some.injEq] at decoded
      subst result
      exact found
    next => cases decoded
  simp only [matchFrom, matchSk_of_fill pattern row.1 row.2 captured filled]
  cases matchTm pattern term captured <;> rfl

def queryRows [DecidableEq Atom] (pattern : Pat Atom) (captured : Subst Atom) (rows : Rows Id Atom) :
    List (Id × Subst Atom) :=
  rows.filterMap fun row => (matchFrom pattern captured row.2).map (row.1, ·)

def queryFacts [DecidableEq Atom] (pattern : Pat Atom) (captured : Subst Atom) (facts : Facts Id Atom) :
    List (Id × Subst Atom) :=
  facts.filterMap fun fact => (matchTm pattern fact.2 captured).map (fact.1, ·)

theorem query_encoded_exact [DecidableEq Atom] (mask : Mask) (pattern : Pat Atom)
    (captured : Subst Atom) (facts : Facts Id Atom) :
    queryRows pattern captured (encode mask facts) = queryFacts pattern captured facts := by
  simp only [queryRows, queryFacts, encode, List.filterMap_map, Function.comp_def,
    matchFrom_reassembled pattern captured _ _ (mask.cut.sec _)]

theorem query_decoded_exact [DecidableEq Atom] (pattern : Pat Atom) (captured : Subst Atom)
    (rows : Rows Id Atom) (facts : Facts Id Atom) (decoded : decode rows = some facts) :
    queryRows pattern captured rows = queryFacts pattern captured facts := by
  induction rows generalizing facts with
  | nil => cases decoded; rfl
  | cons row rest ih =>
      rcases row with ⟨id, row⟩
      cases reconstructed : reassemble row with
      | none => simp [decode, reconstructed] at decoded
      | some term =>
          cases later : decode rest with
          | none => simp [decode, reconstructed, later] at decoded
          | some remaining =>
              have same : (id, term) :: remaining = facts := by simpa [decode, reconstructed, later] using decoded
              subst facts
              simp only [queryRows, queryFacts, List.filterMap_cons,
                matchFrom_reassembled pattern captured row term reconstructed]
              have tail := ih remaining later
              unfold queryRows queryFacts at tail
              rw [tail]

theorem transfer_matches_exactly [DecidableEq Atom] (destination : Mask) (pattern : Pat Atom)
    (captured : Subst Atom) (before after : Rows Id Atom)
    (completed : transfer destination before = .committed after) :
    queryRows pattern captured after = queryRows pattern captured before := by
  cases decoded : decode before with
  | none => simp [transfer, decoded] at completed
  | some facts =>
      have same : encode destination facts = after := by simpa [transfer, decoded] using completed
      rw [← same, query_encoded_exact, query_decoded_exact pattern captured before facts decoded]

def treeCells : Tm Atom → Nat
  | .atom _ => 1
  | .node left right => 1 + treeCells left + treeCells right

def skeletonCells : Skel Atom → Nat
  | .hole | .atom _ => 1
  | .node left right => 1 + skeletonCells left + skeletonCells right

def rowCells (row : Id × Row Atom) : Nat := 1 + row.2.2.length + (row.2.2.map treeCells).sum

def cells [DecidableEq Atom] (rows : Rows Id Atom) : Nat :=
  ((rows.map fun row => row.2.1).dedup.map skeletonCells).sum + (rows.map rowCells).sum

def cost [DecidableEq Atom] (facts : Facts Id Atom) (mask : Mask) : Nat := cells (encode mask facts)

theorem normalized_cost [DecidableEq Atom] (facts : Facts Id Atom) (mask : Mask) :
    cost facts (normalize mask) = cost facts mask := by rw [cost, normalize_encode]; rfl

def select [DecidableEq Atom] (depth : Nat) (facts : Facts Id Atom) : Mask :=
  (choose depth (cost facts)).getD .keep

theorem selected_minimal [DecidableEq Atom] (depth : Nat) (facts : Facts Id Atom)
    (other : Mask) (bounded : other.depth ≤ depth) : cost facts (select depth facts) ≤ cost facts other := by
  obtain ⟨best, chosen⟩ := choice_exists depth (cost facts)
  have optimal := chosen_minimal depth (cost facts) best other chosen bounded
  simpa [select, chosen, normalized_cost] using optimal

theorem selected_depth [DecidableEq Atom] (depth : Nat) (facts : Facts Id Atom) : (select depth facts).depth ≤ depth := by
  obtain ⟨best, chosen⟩ := choice_exists depth (cost facts)
  obtain ⟨mask, present, rfl⟩ := List.mem_map.mp (chosen_member depth (cost facts) best chosen)
  have bound := (mem_catalogue depth mask).mp present
  simpa [select, chosen] using (normalize_depth mask).trans bound

theorem selected_canonical [DecidableEq Atom] (depth : Nat) (facts : Facts Id Atom) :
    normalize (select depth facts) = select depth facts := by
  obtain ⟨best, chosen⟩ := choice_exists depth (cost facts)
  simpa [select, chosen] using chosen_canonical depth (cost facts) best chosen

theorem selected_store_exact [DecidableEq Atom] (depth : Nat) (facts : Facts Id Atom) :
    decode (encode (select depth facts) facts) = some facts := decode_encode _ _

namespace Controls

def deep (leaf : Nat) : Tm Nat := .node (.atom 0) (.node (.atom 0) (.atom leaf))
def facts : Facts Nat Nat := [(10, deep 1), (20, deep 2), (30, deep 3)]
def spine : Mask := .branch .keep (.branch .keep .hole)

theorem deep_spine_saves_declared_cells :
    cost facts .hole = 22 ∧ cost facts .keep = 18 ∧ cost facts spine = 14 := by decide +kernel

theorem bounded_catalogue_finds_spine_cost : cost facts (select 2 facts) = 14 := by decide +kernel

theorem deep_layout_still_returns_every_occurrence :
    decode (encode (select 2 facts) facts) = some facts := selected_store_exact 2 facts

def duplicates : Facts Nat Nat := [(10, .atom 7), (20, .atom 7), (20, .atom 7)]

theorem duplicate_values_and_ids_keep_their_positions :
    (encode spine duplicates).map Prod.fst = [10, 20, 20] ∧
      decode (encode spine duplicates) = some duplicates := ⟨ids_preserved _ _, decode_encode _ _⟩

def malformed : Rows Nat Nat := [(10, (.hole, [])), (20, (.atom 7, []))]

theorem malformed_prefix_refuses_instead_of_dropping_it :
    transfer .keep malformed = .declined malformed := rfl

theorem swapped_payloads_change_the_fact :
    reassemble (Skel.node .hole .hole, [Tm.atom (1 : Nat), .atom 2]) ≠
      reassemble (Skel.node .hole .hole, [Tm.atom 2, .atom 1]) := by decide

theorem repeated_variables_keep_one_frame_across_holes :
    queryRows (Pat.node (.var 0) (.var 0)) []
      (encode (.branch .hole .hole) ([(10, Tm.node (.atom 1) (.atom 2))] : Facts Nat Nat)) = [] := by decide

theorem captured_binding_is_not_reset_by_recut :
    queryRows (.var 0) [(0, Tm.atom (1 : Nat))]
      (encode .hole ([(10, .atom 2)] : Facts Nat Nat)) = [] := by decide

end Controls

end Mettapedia.Machines.OrderedCutStore
