import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceRows
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedMutationSource

/-!
# EU query rows enter the reached binding frame

An actually unbound principal representative admits every closed row value,
even when its written variable is an alias. Captures retain original body
syntax and caller equations. Literal satisfaction hits preserve duplicate
occurrences without adding an equation. These are prepared query boundaries,
not a complete round or an allocation-credit theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceCapture

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS (World)
open EagerDFS.Destination
open CTLUntilSourceRows
open ScopedQuerySource (capture bodyControl)

theorem unbound_capture_consistent (bindings : Equations) (principal : Environment)
    (slot representative : String) (value : Atom)
    (resolved : resolve bindings = some principal)
    (unbound : read principal (.var slot) = .var representative)
    (closed : ∀ environment, read environment value = value) :
    ∃ environment, Solves environment (ScopedQuerySource.extend bindings [(slot, value)]) := by
  have refined := ScopedMutationSource.refine_unbound bindings principal (.var slot) value
    representative resolved unbound closed
  obtain ⟨environment, solved⟩ := ClosedOnceQueryFrame.refined_consistent _ _ _ refined
  obtain ⟨old, result⟩ := (solves_append_equation _ _ _ _).mp solved
  refine ⟨environment, ?_⟩
  simpa only [ScopedQuerySource.extend, List.map_cons, List.map_nil] using
    (solves_append_equation environment bindings (.var slot) value).mpr ⟨old, result.symm⟩

theorem number_closed (value : Nat) (environment : Environment) :
    read environment (number value) = number value :=
  ConstantQuerySource.Scalar.read (.grounded _) environment

/-- The principal solver of a captured frame reads the assigned row value;
this is obtained from the actual appended equation, not a selected model. -/
theorem captured_number_read (bindings : Equations) (slot : String) (value : Nat)
    (principal : Environment)
    (resolved : resolve (ScopedQuerySource.extend bindings [(slot, number value)]) = some principal) :
    read principal (.var slot) = number value := by
  have solved := resolve_sound resolved
  change Solves principal (bindings ++ [(.var slot, number value)]) at solved
  exact ((solves_append_equation _ _ _ _).mp solved).2.trans (number_closed value principal)

theorem fresh_after_capture (bindings : Equations) (slot other : String) (value : Nat)
    (fresh : ClosedOnceQueryFrame.FreshFor other bindings) (apart : other ≠ slot) :
    ClosedOnceQueryFrame.FreshFor other (ScopedQuerySource.extend bindings [(slot, number value)]) := by
  intro pair member
  change pair ∈ bindings ++ [(.var slot, number value)] at member
  rcases List.mem_append.mp member with old | added
  · exact fresh pair old
  · cases List.mem_singleton.mp added
    simp [encode, number, Mettapedia.Logic.LP.Term.freeVars, apart]

/-- After the outer frontier capture, the actual reverse-edge source pattern
has a fixed successor and a still-fresh predecessor slot. -/
theorem edge_pattern_after_frontier (bindings : Equations) (nextSlot priorSlot : String)
    (next : Nat) (principal : Environment)
    (resolved : resolve (ScopedQuerySource.extend bindings [(nextSlot, number next)]) = some principal)
    (fresh : ClosedOnceQueryFrame.FreshFor priorSlot bindings) (apart : priorSlot ≠ nextSlot) :
    read principal (reversePattern nextSlot priorSlot) =
      .expression [.symbol "rt", number next, .var priorSlot] := by
  have nextRead := captured_number_read bindings nextSlot next principal resolved
  have priorRead := ClosedOnceQueryFrame.fresh_read _ priorSlot principal
    (fresh_after_capture bindings nextSlot priorSlot next fresh apart) resolved
  simp only [read_eq_applyTypeValuation, HE.Spec.Type.RuntimeRefinement.applyTypeValuation] at nextRead priorRead
  simp only [reversePattern, read_eq_applyTypeValuation, HE.Spec.Type.RuntimeRefinement.applyTypeValuation,
    List.map_cons, List.map_nil, nextRead, priorRead]

/-- The inner satisfaction test uses the predecessor from the reached edge
frame. Earlier captured equations are kept alongside this new binding. -/
theorem satisfaction_pattern_after_edge (bindings : Equations) (priorSlot label : String)
    (prior : Nat) (principal : Environment)
    (resolved : resolve (ScopedQuerySource.extend bindings [(priorSlot, number prior)]) = some principal) :
    read principal (satPattern label priorSlot) = CTLPreimageSource.satisfaction "sat" label prior := by
  have priorRead := captured_number_read bindings priorSlot prior principal resolved
  simp only [read_eq_applyTypeValuation, HE.Spec.Type.RuntimeRefinement.applyTypeValuation] at priorRead
  simp only [satPattern, read_eq_applyTypeValuation, HE.Spec.Type.RuntimeRefinement.applyTypeValuation,
    List.map_cons, List.map_nil, priorRead, CTLPreimageSource.satisfaction, CTLPreimageSource.row]
  rfl

theorem frontier_capture (caller : Control) (principal : Environment) (slot representative : String)
    (label : String) (round : Nat) (body destination : Atom) (older : List Goal)
    (offset : Nat) (rows : List (String × Nat × Nat))
    (resolved : resolve caller.bindings = some principal)
    (unbound : read principal (.var slot) = .var representative) :
    capture caller (frontier label round (.var slot)) body destination older offset (frontierRows rows) =
      some ((located (frontierSelect label round) offset rows).map
        (fun entry => (entry.1, bodyControl caller [(slot, number entry.2)] body destination older))) := by
  have consistent : ∀ row ∈ frontierRows rows, ∀ bindings,
      SpaceSemantics.ValueMatch [] (frontier label round (.var slot)) row bindings →
      ∃ environment, Solves environment (ScopedQuerySource.extend caller.bindings bindings) := by
    intro row member bindings matched
    obtain ⟨stored, _member, rfl⟩ := List.mem_map.mp member
    have actual := SpaceSemantics.matchValue_complete matched
    rw [frontier_match] at actual
    split at actual
    · cases Option.some.inj actual
      exact unbound_capture_consistent caller.bindings principal slot representative _ resolved unbound
        (number_closed stored.2.2)
    · cases actual
  rw [ScopedQuerySource.capture_of_consistent_matches _ _ _ _ _ _ _ consistent, frontier_scan]
  simp only [List.map_map, Function.comp_def]

def preparedEdge (next : Nat) (slot : String) : Atom :=
  .expression [.symbol "rt", number next, .var slot]

theorem prepared_edge_match (next : Nat) (slot : String) (edge : Nat × Nat) :
    SpaceSemantics.matchValue [] (preparedEdge next slot) (CTLPreimageSource.reverseEdge "rt" edge) =
      if edge.2 = next then some [(slot, number edge.1)] else none := by
  unfold preparedEdge CTLPreimageSource.reverseEdge CTLPreimageSource.row
  rw [SpaceSemantics.matchValue_expression_of_not_cons _ _ _ (by simp)]
  change SpaceSemantics.matchValue.matchValues [] [.symbol "rt", number next, .var slot]
    [.symbol "rt", number edge.2, number edge.1] = _
  by_cases same : edge.2 = next
  · simp [number, SpaceSemantics.matchValue.matchValues, SpaceSemantics.matchValue, Subst.lookup,
      Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, same]
  · simp [number, SpaceSemantics.matchValue.matchValues, SpaceSemantics.matchValue, Subst.lookup,
      Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, same, Ne.symm same]

theorem prepared_edge_scan (next : Nat) (slot : String) (offset : Nat) (rows : List (Nat × Nat)) :
    FlatQueryRelationCompilation.sourceScan [] (preparedEdge next slot) offset (edgeRows rows) =
      (located (edgeSelect next) offset rows).map (fun entry => (entry.1, [(slot, number entry.2)])) := by
  unfold edgeRows
  apply scan_encoded (bindings := fun value => [(slot, number value)])
  intro row
  rw [prepared_edge_match]
  unfold edgeSelect
  split <;> rfl

theorem edge_capture (caller : Control) (principal : Environment) (slot representative : String)
    (next : Nat) (body destination : Atom) (older : List Goal) (offset : Nat) (rows : List (Nat × Nat))
    (resolved : resolve caller.bindings = some principal)
    (unbound : read principal (.var slot) = .var representative) :
    capture caller (preparedEdge next slot) body destination older offset (edgeRows rows) =
      some ((located (edgeSelect next) offset rows).map
        (fun entry => (entry.1, bodyControl caller [(slot, number entry.2)] body destination older))) := by
  have consistent : ∀ row ∈ edgeRows rows, ∀ bindings,
      SpaceSemantics.ValueMatch [] (preparedEdge next slot) row bindings →
      ∃ environment, Solves environment (ScopedQuerySource.extend caller.bindings bindings) := by
    intro row member bindings matched
    obtain ⟨stored, _member, rfl⟩ := List.mem_map.mp member
    have actual := SpaceSemantics.matchValue_complete matched
    rw [prepared_edge_match] at actual
    split at actual
    · cases Option.some.inj actual
      exact unbound_capture_consistent caller.bindings principal slot representative _ resolved unbound
        (number_closed stored.1)
    · cases actual
  rw [ScopedQuerySource.capture_of_consistent_matches _ _ _ _ _ _ _ consistent, prepared_edge_scan]
  simp only [List.map_map, Function.comp_def]

def preparedSatisfaction (label : String) (prior : Nat) : Atom :=
  CTLPreimageSource.satisfaction "sat" label prior

theorem prepared_satisfaction_match (label : String) (prior : Nat) (stored : String × Nat) :
    SpaceSemantics.matchValue [] (preparedSatisfaction label prior)
      (CTLPreimageSource.satisfaction "sat" stored.1 stored.2) =
      if stored.1 = label ∧ stored.2 = prior then some [] else none := by
  unfold preparedSatisfaction CTLPreimageSource.satisfaction CTLPreimageSource.row
  rw [SpaceSemantics.matchValue_expression_of_not_cons _ _ _ (by simp)]
  by_cases sameLabel : stored.1 = label
  · rw [sameLabel]
    by_cases sameNode : stored.2 = prior
    · simp [SpaceSemantics.matchValue.matchValues, SpaceSemantics.matchValue,
        Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, sameNode]
    · simp [SpaceSemantics.matchValue.matchValues, SpaceSemantics.matchValue,
        Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, sameNode, Ne.symm sameNode]
  · simp [SpaceSemantics.matchValue.matchValues, SpaceSemantics.matchValue,
      Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, sameLabel, Ne.symm sameLabel]

theorem prepared_satisfaction_scan (label : String) (prior : Nat) (offset : Nat)
    (rows : List (String × Nat)) :
    FlatQueryRelationCompilation.sourceScan [] (preparedSatisfaction label prior) offset (satisfactionRows rows) =
      (located (satisfactionSelect label prior) offset rows).map (fun entry => (entry.1, [])) := by
  unfold satisfactionRows
  apply scan_encoded (bindings := fun (_ : Unit) => [])
  intro row
  rw [prepared_satisfaction_match]
  unfold satisfactionSelect
  split <;> rfl

theorem satisfaction_capture (caller : Control) (label : String) (prior : Nat)
    (body destination : Atom) (older : List Goal) (offset : Nat) (rows : List (String × Nat))
    (consistent : ∃ environment, Solves environment caller.bindings) :
    capture caller (preparedSatisfaction label prior) body destination older offset (satisfactionRows rows) =
      some ((located (satisfactionSelect label prior) offset rows).map
        (fun entry => (entry.1, bodyControl caller [] body destination older))) := by
  have frames : ∀ row ∈ satisfactionRows rows, ∀ bindings,
      SpaceSemantics.ValueMatch [] (preparedSatisfaction label prior) row bindings →
      ∃ environment, Solves environment (ScopedQuerySource.extend caller.bindings bindings) := by
    intro row member bindings matched
    obtain ⟨stored, _member, rfl⟩ := List.mem_map.mp member
    have actual := SpaceSemantics.matchValue_complete matched
    rw [prepared_satisfaction_match] at actual
    split at actual
    · cases Option.some.inj actual
      simpa [ScopedQuerySource.extend] using consistent
    · cases actual
  rw [ScopedQuerySource.capture_of_consistent_matches _ _ _ _ _ _ _ frames, prepared_satisfaction_scan]
  simp only [List.map_map, Function.comp_def]

theorem frontier_rows_ready (pattern : Atom) (rows : List (String × Nat × Nat)) :
    ClosedQueryAdmission.rowsReady pattern (frontierRows rows) = true := by
  apply ClosedQueryAdmission.ground_rows_are_ready
  intro row member
  obtain ⟨stored, _member, rfl⟩ := List.mem_map.mp member
  simp [CTLUntilSourceRows.frontier, number, Mettapedia.Languages.ProcessCalculi.MORK.isGroundAtom,
    Mettapedia.Languages.ProcessCalculi.MORK.isGroundAtom.isGroundList]

theorem edge_rows_ready (pattern : Atom) (rows : List (Nat × Nat)) :
    ClosedQueryAdmission.rowsReady pattern (edgeRows rows) = true := by
  apply ClosedQueryAdmission.ground_rows_are_ready
  intro row member
  obtain ⟨stored, _member, rfl⟩ := List.mem_map.mp member
  change Mettapedia.Languages.ProcessCalculi.MORK.isGroundAtom
    (.expression [.symbol "rt", number stored.2, number stored.1]) = true
  simp [number, Mettapedia.Languages.ProcessCalculi.MORK.isGroundAtom,
    Mettapedia.Languages.ProcessCalculi.MORK.isGroundAtom.isGroundList]

theorem satisfaction_rows_ready (pattern : Atom) (rows : List (String × Nat)) :
    ClosedQueryAdmission.rowsReady pattern (satisfactionRows rows) = true := by
  apply ClosedQueryAdmission.ground_rows_are_ready
  intro row member
  obtain ⟨stored, _member, rfl⟩ := List.mem_map.mp member
  change Mettapedia.Languages.ProcessCalculi.MORK.isGroundAtom
    (.expression [.symbol "sat", .symbol stored.1, number stored.2]) = true
  simp [number, Mettapedia.Languages.ProcessCalculi.MORK.isGroundAtom,
    Mettapedia.Languages.ProcessCalculi.MORK.isGroundAtom.isGroundList]

/-- The actual prepared frontier invocation installs all row-specific frames.
The world, allocator, original body and older caller goals are retained. -/
theorem frontier_entry {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (spaceCode patternCode body destination : Atom) (older : List Goal)
    (principal : Environment) (slot representative label : String) (round : Nat)
    (rows : List (String × Nat × Nat))
    (front : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "match" [spaceCode, patternCode, body] destination :: older)
    (resolved : resolve control.bindings = some principal)
    (unbound : read principal (.var slot) = .var representative)
    (patternRead : read principal patternCode = frontier label round (.var slot))
    (snapshot : (Effects.readHandle (read principal spaceCode) >>= world.state.read) = some (frontierRows rows)) :
    (ScopedQuerySource.machine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (.silent (allocator, ⟨world, {scope with
        frontier := ScopedQuerySource.work context origins
          ((located (frontierSelect label round) 0 rows).map
            (fun entry => (entry.1, bodyControl control [(slot, number entry.2)] body destination older))) ++ pending}
          :: parents⟩)) := by
  apply ScopedQuerySource.captured_step policy program allocator world scope parents control context origins pending
    spaceCode patternCode body destination older principal (frontierRows rows) _ front atCall resolved
  · rw [patternRead]
    simp [ScopedQuerySource.fused, CTLUntilSourceRows.frontier, LiteralQuerySource.checkLiteral]
  · exact snapshot
  · exact frontier_rows_ready _ rows
  · apply ScopedQuerySource.capture_has_source
    rw [patternRead]
    exact frontier_capture control principal slot representative label round body destination older 0 rows resolved unbound

theorem edge_entry {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (spaceCode patternCode body destination : Atom) (older : List Goal)
    (principal : Environment) (slot representative : String) (next : Nat)
    (rows : List (Nat × Nat))
    (front : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "match" [spaceCode, patternCode, body] destination :: older)
    (resolved : resolve control.bindings = some principal)
    (unbound : read principal (.var slot) = .var representative)
    (patternRead : read principal patternCode = preparedEdge next slot)
    (snapshot : (Effects.readHandle (read principal spaceCode) >>= world.state.read) = some (edgeRows rows)) :
    (ScopedQuerySource.machine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (.silent (allocator, ⟨world, {scope with
        frontier := ScopedQuerySource.work context origins
          ((located (edgeSelect next) 0 rows).map
            (fun entry => (entry.1, bodyControl control [(slot, number entry.2)] body destination older))) ++ pending}
          :: parents⟩)) := by
  apply ScopedQuerySource.captured_step policy program allocator world scope parents control context origins pending
    spaceCode patternCode body destination older principal (edgeRows rows) _ front atCall resolved
  · rw [patternRead]
    simp [ScopedQuerySource.fused, preparedEdge, LiteralQuerySource.checkLiteral]
  · exact snapshot
  · exact edge_rows_ready _ rows
  · apply ScopedQuerySource.capture_has_source
    rw [patternRead]
    exact edge_capture control principal slot representative next body destination older 0 rows resolved unbound

theorem satisfaction_entry {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (spaceCode patternCode body destination : Atom) (older : List Goal)
    (principal : Environment) (label : String) (prior : Nat) (rows : List (String × Nat))
    (front : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "match" [spaceCode, patternCode, body] destination :: older)
    (resolved : resolve control.bindings = some principal)
    (patternRead : read principal patternCode = preparedSatisfaction label prior)
    (bodyCode : ConstantQuerySource.isScalar body = false)
    (snapshot : (Effects.readHandle (read principal spaceCode) >>= world.state.read) = some (satisfactionRows rows)) :
    (ScopedQuerySource.machine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (.silent (allocator, ⟨world, {scope with
        frontier := ScopedQuerySource.work context origins
          ((located (satisfactionSelect label prior) 0 rows).map
            (fun entry => (entry.1, bodyControl control [] body destination older))) ++ pending} :: parents⟩)) := by
  apply ScopedQuerySource.captured_step policy program allocator world scope parents control context origins pending
    spaceCode patternCode body destination older principal (satisfactionRows rows) _ front atCall resolved
  · simp [ScopedQuerySource.fused, bodyCode]
  · exact snapshot
  · exact satisfaction_rows_ready _ rows
  · apply ScopedQuerySource.capture_has_source
    rw [patternRead]
    exact satisfaction_capture control label prior body destination older 0 rows ⟨principal, resolve_sound resolved⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceCapture
