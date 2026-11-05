import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilMixedStore

/-!
# Captured query entry over decoded mixed stores

Row views retain original physical positions. Frame installation uses actual
principal unifiers and complete matched-row coverage. Unrelated rows stay in
the shared world; view formation neither copies nor mutates that world.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilMixedCapture

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS (World)
open EagerDFS.Destination
open CTLUntilSourceRows (number located)
open CTLUntilMixedStore
open FlatQueryRowCodec (Codec)
open ScopedQuerySource (capture bodyControl)

variable {Label : Type} [DecidableEq Label]

omit [DecidableEq Label] in
theorem single_capture (codec : Codec Label) (select : Row Label → Option Nat) (pattern : Atom)
    (slot : String)
    (matching : ∀ row, row.admitted → SpaceSemantics.matchValue [] pattern (render codec row) =
      (select row).map (fun value => [(slot, number value)]))
    (caller : Control) (principal : Environment) (representative : String)
    (body destination : Atom) (older : List Goal) (offset : Nat) (rows : List (Row Label))
    (admitted : ∀ row ∈ rows, row.admitted)
    (resolved : resolve caller.bindings = some principal)
    (unbound : read principal (.var slot) = .var representative) :
    capture caller pattern body destination older offset (rows.map (render codec)) =
      some ((located select offset rows).map
        (fun entry => (entry.1, bodyControl caller [(slot, number entry.2)] body destination older))) := by
  have frames : ∀ atom ∈ rows.map (render codec), ∀ bindings,
      SpaceSemantics.ValueMatch [] pattern atom bindings →
      ∃ environment, Solves environment (ScopedQuerySource.extend caller.bindings bindings) := by
    intro atom member bindings matched
    obtain ⟨row, storedMember, rfl⟩ := List.mem_map.mp member
    have actual := SpaceSemantics.matchValue_complete matched
    rw [matching row (admitted row storedMember)] at actual
    obtain ⟨value, _selected, rfl⟩ := Option.map_eq_some_iff.mp actual
    exact CTLUntilSourceCapture.unbound_capture_consistent caller.bindings principal slot representative _
      resolved unbound (CTLUntilSourceCapture.number_closed value)
  rw [ScopedQuerySource.capture_of_consistent_matches _ _ _ _ _ _ _ frames,
    scan_admitted codec select _ [] pattern matching offset rows admitted]
  simp only [List.map_map, Function.comp_def]

omit [DecidableEq Label] in
theorem prepared_edge_match (codec : Codec Label) (next : Nat) (slot : String)
    (row : Row Label) (admitted : row.admitted) :
    SpaceSemantics.matchValue [] (CTLUntilSourceCapture.preparedEdge next slot) (render codec row) =
      (edgeSelect next row).map (fun value => [(slot, number value)]) := by
  cases row with
  | frontier label round node => exact different_head [] "rt" "fr" _ _ (by decide) (by decide)
  | edge prior target =>
      change SpaceSemantics.matchValue [] (CTLUntilSourceCapture.preparedEdge next slot)
        (CTLPreimageSource.reverseEdge "rt" (prior, target)) = _
      rw [CTLUntilSourceCapture.prepared_edge_match]
      by_cases same : target = next <;> simp [edgeSelect, same]
  | satisfaction label node => exact different_head [] "rt" "sat" _ _ (by decide) (by decide)
  | other head children => exact different_head [] "rt" head _ _ (by decide) (Ne.symm admitted.2.1)

def preparedSatisfaction (codec : Codec Label) (label : Label) (node : Nat) : Atom :=
  .expression [.symbol "sat", codec.encode label, number node]

theorem prepared_satisfaction_match (codec : Codec Label) (label : Label) (node : Nat)
    (row : Row Label) (admitted : row.admitted) :
    SpaceSemantics.matchValue [] (preparedSatisfaction codec label node) (render codec row) =
      (satSelect label node row).map (fun _ => []) := by
  cases row with
  | frontier other round value => exact different_head [] "sat" "fr" _ _ (by decide) (by decide)
  | edge prior next => exact different_head [] "sat" "rt" _ _ (by decide) (by decide)
  | satisfaction other value =>
      unfold preparedSatisfaction render
      rw [SpaceSemantics.matchValue_expression_of_not_cons _ _ _ (by simp)]
      by_cases sameLabel : other = label
      · subst other
        by_cases sameNode : value = node
        · simp [SpaceSemantics.matchValue.matchValues, SpaceSemantics.matchValue_literal (codec.literal label),
            SpaceSemantics.matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, number, satSelect, sameNode]
        · simp [SpaceSemantics.matchValue.matchValues, SpaceSemantics.matchValue_literal (codec.literal label),
            SpaceSemantics.matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, number, satSelect, sameNode, Ne.symm sameNode]
      · simp [SpaceSemantics.matchValue.matchValues, SpaceSemantics.matchValue_literal (codec.literal label), codec.injective.eq_iff,
          SpaceSemantics.matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, satSelect, sameLabel, Ne.symm sameLabel]
  | other head children => exact different_head [] "sat" head _ _ (by decide) (Ne.symm admitted.2.2)

theorem satisfaction_capture (codec : Codec Label) (label : Label) (node : Nat) (caller : Control)
    (body destination : Atom) (older : List Goal) (offset : Nat) (rows : List (Row Label))
    (admitted : ∀ row ∈ rows, row.admitted) (consistent : ∃ environment, Solves environment caller.bindings) :
    capture caller (preparedSatisfaction codec label node) body destination older offset (rows.map (render codec)) =
      some ((located (satSelect label node) offset rows).map
        (fun entry => (entry.1, bodyControl caller [] body destination older))) := by
  have frames : ∀ atom ∈ rows.map (render codec), ∀ bindings,
      SpaceSemantics.ValueMatch [] (preparedSatisfaction codec label node) atom bindings →
      ∃ environment, Solves environment (ScopedQuerySource.extend caller.bindings bindings) := by
    intro atom member bindings matched
    obtain ⟨row, storedMember, rfl⟩ := List.mem_map.mp member
    have actual := SpaceSemantics.matchValue_complete matched
    rw [prepared_satisfaction_match codec label node row (admitted row storedMember)] at actual
    obtain ⟨value, _selected, rfl⟩ := Option.map_eq_some_iff.mp actual
    simpa [ScopedQuerySource.extend] using consistent
  rw [ScopedQuerySource.capture_of_consistent_matches _ _ _ _ _ _ _ frames,
    scan_admitted codec (satSelect label node) (fun (_ : Unit) => []) [] _
      (prepared_satisfaction_match codec label node) offset rows admitted]
  simp only [List.map_map, Function.comp_def]

/-- A successful decoder supplies both the exact snapshot and its admission
evidence. This entry retains every skipped row in the original world. -/
theorem frontier_entry {Context : Type} (codec : Codec Label) (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (spaceCode patternCode body destination : Atom) (older : List Goal)
    (principal : Environment) (slot representative : String) (label : Label) (round : Nat)
    (atoms : List Atom) (rows : List (Row Label))
    (front : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "match" [spaceCode, patternCode, body] destination :: older)
    (resolved : resolve control.bindings = some principal)
    (unbound : read principal (.var slot) = .var representative)
    (patternRead : read principal patternCode = frontierPattern codec label round slot)
    (snapshot : (Effects.readHandle (read principal spaceCode) >>= world.state.read) = some atoms)
    (decoded : decodeRows codec atoms = some rows) :
    (ScopedQuerySource.machine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (.silent (allocator, ⟨world, {scope with
        frontier := ScopedQuerySource.work context origins
          ((located (frontSelect label round) 0 rows).map
            (fun entry => (entry.1, bodyControl control [(slot, number entry.2)] body destination older))) ++ pending}
          :: parents⟩)) := by
  obtain ⟨actual, admitted⟩ := decode_rows_sound codec atoms rows decoded
  subst atoms
  apply ScopedQuerySource.captured_step policy program allocator world scope parents control context origins pending
    spaceCode patternCode body destination older principal (rows.map (render codec)) _ front atCall resolved
  · rw [patternRead]
    simp [ScopedQuerySource.fused, frontierPattern, LiteralQuerySource.checkLiteral]
  · exact snapshot
  · rw [patternRead]
    exact rows_ready codec "fr" _ (by simp) rows admitted
  · apply ScopedQuerySource.capture_has_source
    rw [patternRead]
    exact single_capture codec (frontSelect label round) _ slot (frontier_match codec label round slot)
      control principal representative body destination older 0 rows admitted resolved unbound

omit [DecidableEq Label] in
theorem edge_entry {Context : Type} (codec : Codec Label) (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (spaceCode patternCode body destination : Atom) (older : List Goal)
    (principal : Environment) (slot representative : String) (next : Nat)
    (atoms : List Atom) (rows : List (Row Label))
    (front : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "match" [spaceCode, patternCode, body] destination :: older)
    (resolved : resolve control.bindings = some principal)
    (unbound : read principal (.var slot) = .var representative)
    (patternRead : read principal patternCode = CTLUntilSourceCapture.preparedEdge next slot)
    (snapshot : (Effects.readHandle (read principal spaceCode) >>= world.state.read) = some atoms)
    (decoded : decodeRows codec atoms = some rows) :
    (ScopedQuerySource.machine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (.silent (allocator, ⟨world, {scope with
        frontier := ScopedQuerySource.work context origins
          ((located (edgeSelect next) 0 rows).map
            (fun entry => (entry.1, bodyControl control [(slot, number entry.2)] body destination older))) ++ pending}
          :: parents⟩)) := by
  obtain ⟨actual, admitted⟩ := decode_rows_sound codec atoms rows decoded
  subst atoms
  apply ScopedQuerySource.captured_step policy program allocator world scope parents control context origins pending
    spaceCode patternCode body destination older principal (rows.map (render codec)) _ front atCall resolved
  · rw [patternRead]
    simp [ScopedQuerySource.fused, CTLUntilSourceCapture.preparedEdge, LiteralQuerySource.checkLiteral]
  · exact snapshot
  · rw [patternRead]
    exact rows_ready codec "rt" _ (by simp) rows admitted
  · apply ScopedQuerySource.capture_has_source
    rw [patternRead]
    exact single_capture codec (edgeSelect next) _ slot (prepared_edge_match codec next slot)
      control principal representative body destination older 0 rows admitted resolved unbound

theorem satisfaction_entry {Context : Type} (codec : Codec Label) (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (spaceCode patternCode body destination : Atom) (older : List Goal)
    (principal : Environment) (label : Label) (node : Nat) (atoms : List Atom) (rows : List (Row Label))
    (front : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "match" [spaceCode, patternCode, body] destination :: older)
    (resolved : resolve control.bindings = some principal)
    (patternRead : read principal patternCode = preparedSatisfaction codec label node)
    (bodyCode : ConstantQuerySource.isScalar body = false)
    (snapshot : (Effects.readHandle (read principal spaceCode) >>= world.state.read) = some atoms)
    (decoded : decodeRows codec atoms = some rows) :
    (ScopedQuerySource.machine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (.silent (allocator, ⟨world, {scope with
        frontier := ScopedQuerySource.work context origins
          ((located (satSelect label node) 0 rows).map
            (fun entry => (entry.1, bodyControl control [] body destination older))) ++ pending} :: parents⟩)) := by
  obtain ⟨actual, admitted⟩ := decode_rows_sound codec atoms rows decoded
  subst atoms
  apply ScopedQuerySource.captured_step policy program allocator world scope parents control context origins pending
    spaceCode patternCode body destination older principal (rows.map (render codec)) _ front atCall resolved
  · simp [ScopedQuerySource.fused, bodyCode]
  · exact snapshot
  · rw [patternRead]
    exact rows_ready codec "sat" _ (by simp) rows admitted
  · apply ScopedQuerySource.capture_has_source
    rw [patternRead]
    exact satisfaction_capture codec label node control body destination older 0 rows admitted ⟨principal, resolve_sound resolved⟩

def publication (label : Label) (round node : Nat) : List (Row Label) :=
  [.satisfaction label node, .frontier label (round + 1) node]

omit [DecidableEq Label] in
theorem publication_readmitted (codec : Codec Label) (label : Label) (round node : Nat)
    (atoms : List Atom) (rows : List (Row Label)) (decoded : decodeRows codec atoms = some rows) :
    decodeRows codec (atoms ++ (publication label round node).map (render codec)) =
      some (rows ++ publication label round node) := by
  obtain ⟨actual, admitted⟩ := decode_rows_sound codec atoms rows decoded
  rw [← actual, ← List.map_append]
  apply decode_rows_complete
  intro row member
  rcases List.mem_append.mp member with old | added
  · exact admitted row old
  · simp only [publication, List.mem_cons, List.not_mem_nil, or_false] at added
    rcases added with rfl | rfl <;> trivial

theorem publication_frontier_unmatched (codec : Codec Label) (label : Label) (round node : Nat) (slot : String)
    (atom : Atom) (member : atom ∈ (publication label round node).map (render codec)) :
    SpaceSemantics.matchValue [] (frontierPattern codec label round slot) atom = none := by
  simp only [publication, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rw [frontier_match codec label round slot (.satisfaction label node) trivial]
    rfl
  · rw [frontier_match codec label round slot (.frontier label (round + 1) node) trivial]
    simp [frontSelect]

omit [DecidableEq Label] in
theorem publication_edge_unmatched (codec : Codec Label) (label : Label) (round node next : Nat) (slot : String)
    (atom : Atom) (member : atom ∈ (publication label round node).map (render codec)) :
    SpaceSemantics.matchValue [] (CTLUntilSourceCapture.preparedEdge next slot) atom = none := by
  simp only [publication, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact different_head [] "rt" "sat" _ _ (by decide) (by decide)
  · exact different_head [] "rt" "fr" _ _ (by decide) (by decide)

theorem publication_operand_unmatched (codec : Codec Label) (label holds : Label) (apart : label ≠ holds)
    (round node prior : Nat) (atom : Atom) (member : atom ∈ (publication label round node).map (render codec)) :
    SpaceSemantics.matchValue [] (preparedSatisfaction codec holds prior) atom = none := by
  simp only [publication, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rw [prepared_satisfaction_match codec holds prior (.satisfaction label node) trivial]
    simp [satSelect, apart]
  · exact different_head [] "sat" "fr" _ _ (by decide) (by decide)

/-- Sequential publication does not change the current-round frontier scan.
The full updated world still belongs to the body and later membership guard. -/
theorem frontier_capture_after_publication (codec : Codec Label) (label : Label) (round node : Nat)
    (slot : String) (caller : Control) (body destination : Atom) (older : List Goal)
    (offset : Nat) (rows : List Atom) :
    capture caller (frontierPattern codec label round slot) body destination older offset
      (rows ++ (publication label round node).map (render codec)) =
    capture caller (frontierPattern codec label round slot) body destination older offset rows :=
  ScopedQueryScanStability.capture_append_unmatched _ _ _ _ _ _ _ _
    (publication_frontier_unmatched codec label round node slot)

omit [DecidableEq Label] in
theorem edge_capture_after_publication (codec : Codec Label) (label : Label) (round node next : Nat)
    (slot : String) (caller : Control) (body destination : Atom) (older : List Goal)
    (offset : Nat) (rows : List Atom) :
    capture caller (CTLUntilSourceCapture.preparedEdge next slot) body destination older offset
      (rows ++ (publication label round node).map (render codec)) =
    capture caller (CTLUntilSourceCapture.preparedEdge next slot) body destination older offset rows :=
  ScopedQueryScanStability.capture_append_unmatched _ _ _ _ _ _ _ _
    (publication_edge_unmatched codec label round node next slot)

theorem operand_capture_after_publication (codec : Codec Label) (label holds : Label) (apart : label ≠ holds)
    (round node prior : Nat) (caller : Control) (body destination : Atom) (older : List Goal)
    (offset : Nat) (rows : List Atom) :
    capture caller (preparedSatisfaction codec holds prior) body destination older offset
      (rows ++ (publication label round node).map (render codec)) =
    capture caller (preparedSatisfaction codec holds prior) body destination older offset rows :=
  ScopedQueryScanStability.capture_append_unmatched _ _ _ _ _ _ _ _
    (publication_operand_unmatched codec label holds apart round node prior)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilMixedCapture
