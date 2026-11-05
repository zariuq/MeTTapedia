import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLPreimageSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryScanStability
import Mettapedia.Machines.CTLUntilCandidateBag

/-!
# Ordered EU row enumeration through the source matcher

Frontier, reverse-edge and satisfaction rows are ordinary ground source
atoms. The scans keep physical row positions, including duplicate literal
satisfaction witnesses which introduce no new binding. Projection to the
candidate bag is separate from source-body execution and fresh insertion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceRows

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open SpaceSemantics
open FlatQueryRelationCompilation (sourceScan)

def number (value : Nat) : Atom := .grounded (.int value)
def frontier (label : String) (round : Nat) (node : Atom) : Atom :=
  .expression [.symbol "fr", .symbol label, number round, node]
def reversePattern (next prior : String) : Atom :=
  .expression [.symbol "rt", .var next, .var prior]
def satPattern (label prior : String) : Atom :=
  .expression [.symbol "sat", .symbol label, .var prior]

def frontierRows (rows : List (String × Nat × Nat)) : List Atom :=
  rows.map fun row => frontier row.1 row.2.1 (number row.2.2)
def edgeRows (rows : List (Nat × Nat)) : List Atom :=
  rows.map (CTLPreimageSource.reverseEdge "rt")
def satisfactionRows (rows : List (String × Nat)) : List Atom :=
  rows.map fun row => CTLPreimageSource.satisfaction "sat" row.1 row.2

def frontierNodes (label : String) (round : Nat) (rows : List (String × Nat × Nat)) : List Nat :=
  rows.filterMap fun row => if row.1 = label ∧ row.2.1 = round then some row.2.2 else none

/-- The ordinal is the position in the original relation, not in its
filtered list. This operation does not identify equal row values. -/
def located {Row Value : Type} (select : Row → Option Value) (offset : Nat) (rows : List Row) : List (Nat × Value) :=
  (rows.zipIdx offset).filterMap fun entry => (select entry.1).map (entry.2, ·)

theorem located_values {Row Value : Type} (select : Row → Option Value) (offset : Nat) (rows : List Row) :
    (located select offset rows).map Prod.snd = rows.filterMap select := by
  induction rows generalizing offset with
  | nil => rfl
  | cons row rows ih =>
      simp only [located] at ih
      simp only [located, List.zipIdx_cons, List.filterMap_cons]
      cases found : select row <;> simpa [found] using ih (offset + 1)

theorem scan_encoded {Row Value : Type} (render : Row → Atom) (select : Row → Option Value)
    (bindings : Value → Subst) (caller : Subst) (pattern : Atom)
    (matching : ∀ row, matchValue caller pattern (render row) = (select row).map bindings)
    (offset : Nat) (rows : List Row) :
    sourceScan caller pattern offset (rows.map render) =
      (located select offset rows).map (fun entry => (entry.1, bindings entry.2)) := by
  induction rows generalizing offset with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.map_cons, sourceScan, matching, ih, located, List.zipIdx_cons, List.filterMap_cons]
      cases select row <;> simp

theorem frontier_match (label : String) (round : Nat) (slot : String) (stored : String × Nat × Nat) :
    matchValue [] (frontier label round (.var slot))
      (frontier stored.1 stored.2.1 (number stored.2.2)) =
      if stored.1 = label ∧ stored.2.1 = round then some [(slot, number stored.2.2)] else none := by
  unfold frontier
  rw [matchValue_expression_of_not_cons [] _ _ (by simp)]
  by_cases sameLabel : stored.1 = label
  · rw [sameLabel]
    by_cases sameRound : stored.2.1 = round
    · simp [number, matchValue.matchValues, matchValue, Subst.lookup,
        Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, sameRound]
    · simp [number, matchValue.matchValues, matchValue, Subst.lookup,
        Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, sameRound, Ne.symm sameRound]
  · simp [number, matchValue.matchValues, matchValue, Subst.lookup,
      Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, sameLabel, Ne.symm sameLabel]

theorem edge_match (nextSlot priorSlot : String) (apart : priorSlot ≠ nextSlot)
    (next : Nat) (edge : Nat × Nat) :
    matchValue [(nextSlot, number next)] (reversePattern nextSlot priorSlot)
      (CTLPreimageSource.reverseEdge "rt" edge) =
      if edge.2 = next then some [(priorSlot, number edge.1), (nextSlot, number next)] else none := by
  unfold reversePattern CTLPreimageSource.reverseEdge CTLPreimageSource.row
  rw [matchValue_expression_of_not_cons _ _ _ (by simp)]
  change matchValue.matchValues [(nextSlot, number next)] [.symbol "rt", .var nextSlot, .var priorSlot]
    [.symbol "rt", number edge.2, number edge.1] = _
  by_cases same : edge.2 = next <;>
    simp [number, matchValue.matchValues, matchValue, Subst.lookup,
      Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, Ne.symm apart, same]

theorem satisfaction_match (label nextSlot priorSlot : String) (next prior : Nat)
    (stored : String × Nat) :
    matchValue [(priorSlot, number prior), (nextSlot, number next)] (satPattern label priorSlot)
      (CTLPreimageSource.satisfaction "sat" stored.1 stored.2) =
      if stored.1 = label ∧ stored.2 = prior then
        some [(priorSlot, number prior), (nextSlot, number next)] else none := by
  unfold satPattern CTLPreimageSource.satisfaction CTLPreimageSource.row
  rw [matchValue_expression_of_not_cons _ _ _ (by simp)]
  by_cases sameLabel : stored.1 = label
  · rw [sameLabel]
    by_cases sameNode : stored.2 = prior <;>
      simp [number, matchValue.matchValues, matchValue, Subst.lookup,
        Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, sameNode]
  · simp [number, matchValue.matchValues, matchValue, Subst.lookup,
      Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, sameLabel, Ne.symm sameLabel]

def frontierSelect (label : String) (round : Nat) (row : String × Nat × Nat) : Option Nat :=
  if row.1 = label ∧ row.2.1 = round then some row.2.2 else none
def edgeSelect (next : Nat) (row : Nat × Nat) : Option Nat :=
  if row.2 = next then some row.1 else none
def satisfactionSelect (label : String) (prior : Nat) (row : String × Nat) : Option Unit :=
  if row.1 = label ∧ row.2 = prior then some () else none

theorem frontier_scan (label : String) (round : Nat) (slot : String)
    (offset : Nat) (rows : List (String × Nat × Nat)) :
    sourceScan [] (frontier label round (.var slot)) offset (frontierRows rows) =
      (located (frontierSelect label round) offset rows).map
        (fun entry => (entry.1, [(slot, number entry.2)])) := by
  unfold frontierRows
  apply scan_encoded (bindings := fun value => [(slot, number value)])
  intro row
  rw [frontier_match]
  unfold frontierSelect
  split <;> rfl

theorem edge_scan (nextSlot priorSlot : String) (apart : priorSlot ≠ nextSlot) (next : Nat)
    (offset : Nat) (rows : List (Nat × Nat)) :
    sourceScan [(nextSlot, number next)] (reversePattern nextSlot priorSlot) offset (edgeRows rows) =
      (located (edgeSelect next) offset rows).map
        (fun entry => (entry.1, [(priorSlot, number entry.2), (nextSlot, number next)])) := by
  unfold edgeRows
  apply scan_encoded (bindings := fun value => [(priorSlot, number value), (nextSlot, number next)])
  intro row
  rw [edge_match nextSlot priorSlot apart]
  unfold edgeSelect
  split <;> rfl

theorem satisfaction_scan (label nextSlot priorSlot : String) (next prior : Nat)
    (offset : Nat) (rows : List (String × Nat)) :
    sourceScan [(priorSlot, number prior), (nextSlot, number next)] (satPattern label priorSlot)
      offset (satisfactionRows rows) =
      (located (satisfactionSelect label prior) offset rows).map
        (fun entry => (entry.1, [(priorSlot, number prior), (nextSlot, number next)])) := by
  unfold satisfactionRows
  apply scan_encoded (bindings := fun (_ : Unit) => [(priorSlot, number prior), (nextSlot, number next)])
  intro row
  rw [satisfaction_match]
  unfold satisfactionSelect
  split <;> rfl

structure Candidate where
  frontierOccurrence : Nat
  edgeOccurrence : Nat
  predicateOccurrence : Nat
  bindings : Subst
  deriving BEq, Repr

/-- Three authored source scans. Each inner query receives the outer
matcher's bindings; all physical row coordinates remain attached. -/
def sourceCandidates (label : String) (round : Nat) (holds nextSlot priorSlot : String)
    (fronts : List (String × Nat × Nat)) (edges : List (Nat × Nat))
    (satisfaction : List (String × Nat)) : List Candidate :=
  (sourceScan [] (frontier label round (.var nextSlot)) 0 (frontierRows fronts)).flatMap fun outer =>
    (sourceScan outer.2 (reversePattern nextSlot priorSlot) 0 (edgeRows edges)).flatMap fun middle =>
      (sourceScan middle.2 (satPattern holds priorSlot) 0 (satisfactionRows satisfaction)).map fun inner =>
        ⟨outer.1, middle.1, inner.1, inner.2⟩

def locatedCandidates (label : String) (round : Nat) (holds nextSlot priorSlot : String)
    (fronts : List (String × Nat × Nat)) (edges : List (Nat × Nat))
    (satisfaction : List (String × Nat)) : List Candidate :=
  (located (frontierSelect label round) 0 fronts).flatMap fun outer =>
    (located (edgeSelect outer.2) 0 edges).flatMap fun middle =>
      (located (satisfactionSelect holds middle.2) 0 satisfaction).map fun inner =>
        ⟨outer.1, middle.1, inner.1, [(priorSlot, number middle.2), (nextSlot, number outer.2)]⟩

theorem source_candidates_exact (label : String) (round : Nat) (holds nextSlot priorSlot : String)
    (apart : priorSlot ≠ nextSlot) (fronts : List (String × Nat × Nat))
    (edges : List (Nat × Nat)) (satisfaction : List (String × Nat)) :
    sourceCandidates label round holds nextSlot priorSlot fronts edges satisfaction =
      locatedCandidates label round holds nextSlot priorSlot fronts edges satisfaction := by
  simp only [sourceCandidates, frontier_scan, List.flatMap_map, Function.comp_def,
    edge_scan nextSlot priorSlot apart, satisfaction_scan, List.map_map, locatedCandidates]

theorem located_flatMap {Row Value Result : Type} (select : Row → Option Value)
    (offset : Nat) (rows : List Row) (body : Value → List Result) :
    (located select offset rows).flatMap (fun entry => body entry.2) =
      (rows.filterMap select).flatMap body := by
  simpa only [List.flatMap_map] using
    congrArg (fun values => values.flatMap body) (located_values select offset rows)

theorem located_map {Row Value Result : Type} (select : Row → Option Value)
    (offset : Nat) (rows : List Row) (body : Value → Result) :
    (located select offset rows).map (fun entry => body entry.2) =
      (rows.filterMap select).map body := by
  simpa only [List.map_map, Function.comp_def] using
    congrArg (List.map body) (located_values select offset rows)

theorem satisfaction_values (label : String) (prior : Nat) (rows : List (String × Nat)) :
    (rows.filterMap (satisfactionSelect label prior)).map (fun _ => prior) =
      (CTLPreimageSource.operand label rows).filter (fun node => node == prior) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      by_cases sameLabel : row.1 = label <;> by_cases sameNode : row.2 = prior <;>
        simp [satisfactionSelect, CTLPreimageSource.operand, sameLabel, sameNode, ih]

theorem edge_values (next : Nat) (edges : List (Nat × Nat)) (holds : List Nat) :
    (edges.filterMap (edgeSelect next)).flatMap (fun prior => holds.filter (fun node => node == prior)) =
      edges.flatMap (fun edge => if edge.2 = next then holds.filter (fun node => node == edge.1) else []) := by
  induction edges with
  | nil => rfl
  | cons edge edges ih =>
      by_cases same : edge.2 = next <;> simp [edgeSelect, same, ih]

/-- Forgetting the three occurrence coordinates yields exactly the ordered
candidate bag, not its support or distinct count. No source match is dropped. -/
theorem candidate_values (label : String) (round : Nat) (holds nextSlot priorSlot : String)
    (apart : priorSlot ≠ nextSlot) (fronts : List (String × Nat × Nat))
    (edges : List (Nat × Nat)) (satisfaction : List (String × Nat)) :
    (sourceCandidates label round holds nextSlot priorSlot fronts edges satisfaction).map
      (fun candidate => applySubst candidate.bindings (.var priorSlot)) =
      (Mettapedia.Machines.CTLUntilCandidateBag.candidates edges
        (CTLPreimageSource.operand holds satisfaction) (frontierNodes label round fronts)).map number := by
  rw [source_candidates_exact label round holds nextSlot priorSlot apart]
  have captured : ∀ prior next,
      applySubst [(priorSlot, number prior), (nextSlot, number next)] (.var priorSlot) = number prior := by
    intro prior next
    simp [applySubst, Subst.lookup]
  simp only [locatedCandidates, List.map_flatMap, List.map_map, Function.comp_def,
    captured]
  rw [located_flatMap (frontierSelect label round) 0 fronts
    (fun next => (located (edgeSelect next) 0 edges).flatMap
      (fun edge => (located (satisfactionSelect holds edge.2) 0 satisfaction).map (fun _ => number edge.2)))]
  unfold Mettapedia.Machines.CTLUntilCandidateBag.candidates frontierNodes
  rw [List.map_flatMap]
  apply congrArg (fun body : Nat → List Atom => (fronts.filterMap (frontierSelect label round)).flatMap body)
  funext next
  rw [located_flatMap (edgeSelect next) 0 edges
    (fun prior => (located (satisfactionSelect holds prior) 0 satisfaction).map (fun _ => number prior))]
  have witnesses : ∀ prior,
      (located (satisfactionSelect holds prior) 0 satisfaction).map (fun _ => number prior) =
        ((CTLPreimageSource.operand holds satisfaction).filter (fun node => node == prior)).map number := by
    intro prior
    rw [located_map (satisfactionSelect holds prior) 0 satisfaction (fun _ => number prior)]
    rw [← satisfaction_values holds prior satisfaction, List.map_map]
    rfl
  simp only [witnesses, ← List.map_flatMap]
  rw [edge_values]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceRows
