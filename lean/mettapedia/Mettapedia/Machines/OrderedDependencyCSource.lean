import Mettapedia.GSLT.LanguageDef.NativeOpsCStatement
import Mettapedia.Machines.OrderedDependencyCArray

/-!
# Source-linked dependency publisher boundary

The complete quoted function is admitted by the existing C lexer and parser.
Its AST preserves the loop, readonly reservation, local dependency load, both
post-increment indices and both pointer RHS operands. The linked slot-array
execution below interprets the two field-store statements, in source order,
through the shared primitive rather than replacing them with a store theorem.

This is an operational interpretation of this admitted fragment over logical
field-separated arrays, not a claim of ISO C compiler correctness. Connecting
physical layout, pending-array lifetime, reservation results, lock exclusion
and revision updates remains necessary for a whole-function C refinement.
-/

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.OrderedDependencyCSource

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.PostIndex
open OrderedDependencyCArray

def publisherSource : String := r#"static void space_publish_dependency_links(
        Space *importer, const SpaceDependencyReservation *reservation) {
    for (uint32_t i = 0u; i < reservation->added; i++) {
        Space *dependency = reservation->pending[i];
        importer->deps[importer->dep_count++] = dependency;
        dependency->importers[dependency->importer_count++] = importer;
    }
}"#

def publisherTypeNames : TypeNames :=
  ["void".toList, "Space".toList, "SpaceDependencyReservation".toList, "uint32_t".toList]

def forwardSite : StoreSyntax :=
  ⟨"importer".toList, "deps".toList, "dep_count".toList, "dependency".toList⟩

def reverseSite : StoreSyntax :=
  ⟨"dependency".toList, "importers".toList, "importer_count".toList, "importer".toList⟩

def iterationBody : List CStatement :=
  [.declare ⟨"Space".toList, 1⟩ "dependency".toList
    (.index (.field (.identifier "reservation".toList) "pending".toList true)
      (.identifier "i".toList)), forwardSite.statement, reverseSite.statement]

def publisherBody : List CStatement :=
  [.forLoop ⟨"uint32_t".toList, 0⟩ "i".toList (.unsignedInteger 0)
    (.binary .lt (.identifier "i".toList)
      (.field (.identifier "reservation".toList) "added".toList true))
    (.postIncrement (.identifier "i".toList))
    iterationBody]

def publisherFunction : CQualifiedFunction :=
  ⟨⟨"void".toList, 0⟩, "space_publish_dependency_links".toList,
    [⟨⟨⟨"Space".toList, 1⟩, "importer".toList⟩, false⟩,
      ⟨⟨⟨"SpaceDependencyReservation".toList, 1⟩, "reservation".toList⟩, true⟩],
    publisherBody⟩

def publisherTokens : List Token := [
    .identifier "static".toList,
    .identifier "void".toList,
    .identifier "space_publish_dependency_links".toList,
    .punctuation "(".toList,
    .identifier "Space".toList,
    .punctuation "*".toList,
    .identifier "importer".toList,
    .punctuation ",".toList,
    .identifier "const".toList,
    .identifier "SpaceDependencyReservation".toList,
    .punctuation "*".toList,
    .identifier "reservation".toList,
    .punctuation ")".toList,
    .punctuation "{".toList,
    .identifier "for".toList,
    .punctuation "(".toList,
    .identifier "uint32_t".toList,
    .identifier "i".toList,
    .punctuation "=".toList,
    .number "0u".toList,
    .punctuation ";".toList,
    .identifier "i".toList,
    .punctuation "<".toList,
    .identifier "reservation".toList,
    .punctuation "->".toList,
    .identifier "added".toList,
    .punctuation ";".toList,
    .identifier "i".toList,
    .punctuation "++".toList,
    .punctuation ")".toList,
    .punctuation "{".toList,
    .identifier "Space".toList,
    .punctuation "*".toList,
    .identifier "dependency".toList,
    .punctuation "=".toList,
    .identifier "reservation".toList,
    .punctuation "->".toList,
    .identifier "pending".toList,
    .punctuation "[".toList,
    .identifier "i".toList,
    .punctuation "]".toList,
    .punctuation ";".toList,
    .identifier "importer".toList,
    .punctuation "->".toList,
    .identifier "deps".toList,
    .punctuation "[".toList,
    .identifier "importer".toList,
    .punctuation "->".toList,
    .identifier "dep_count".toList,
    .punctuation "++".toList,
    .punctuation "]".toList,
    .punctuation "=".toList,
    .identifier "dependency".toList,
    .punctuation ";".toList,
    .identifier "dependency".toList,
    .punctuation "->".toList,
    .identifier "importers".toList,
    .punctuation "[".toList,
    .identifier "dependency".toList,
    .punctuation "->".toList,
    .identifier "importer_count".toList,
    .punctuation "++".toList,
    .punctuation "]".toList,
    .punctuation "=".toList,
    .identifier "importer".toList,
    .punctuation ";".toList,
    .punctuation "}".toList,
    .punctuation "}".toList]

theorem publisher_lexer_exact : lex publisherSource.toList = .ok publisherTokens := by
  decide +kernel

theorem complete_source_admitted :
    qualifiedFunctionText? publisherTypeNames publisherSource.toList = some publisherFunction := by
  exact function_text_using_of_parts (qualifiedParameter? publisherTypeNames)
    publisherTypeNames publisherSource.toList publisherTokens publisherFunction
    publisher_lexer_exact (by rfl)

inductive ArrayField where
  | forward | reverse
  deriving DecidableEq, Repr

def spaceArrayField? (arrayField countField : Name) : Option ArrayField :=
  if arrayField = "deps".toList ∧ countField = "dep_count".toList then some .forward
  else if arrayField = "importers".toList ∧ countField = "importer_count".toList
    then some .reverse
  else none

variable {Ptr : Type} [DecidableEq Ptr]

abbrev Environment (Ptr : Type) := Name → Option Ptr

def executeAssignment (environment : Environment Ptr) (heap : Heap Ptr)
    (statement : CStatement) : Option (Heap Ptr) := do
  let site ← storeSyntax? statement
  let owner ← environment site.owner
  let value ← environment site.value
  let field ← spaceArrayField? site.arrayField site.countField
  match field with
  | .forward => do
    let written ← store (heap.forward owner) value
    some { heap with forward := Function.update heap.forward owner written }
  | .reverse => do
    let written ← store (heap.reverse owner) value
    some { heap with reverse := Function.update heap.reverse owner written }

def executeAssignments (environment : Environment Ptr) (heap : Heap Ptr) :
    List CStatement → Option (Heap Ptr)
  | [] => some heap
  | statement :: rest => (executeAssignment environment heap statement).bind fun next =>
    executeAssignments environment next rest

def iterationEnvironment (reader source : Ptr) : Environment Ptr :=
  fun name => if name = "importer".toList then some reader
    else if name = "dependency".toList then some source else none

theorem forward_statement_execution (heap : Heap Ptr) (reader source : Ptr) :
    executeAssignment (iterationEnvironment reader source) heap forwardSite.statement =
      (store (heap.forward reader) source).map fun written =>
        (⟨Function.update heap.forward reader written, heap.reverse⟩ : Heap Ptr) := by
  change (store (heap.forward reader) source).bind (fun written =>
    some (⟨Function.update heap.forward reader written, heap.reverse⟩ : Heap Ptr)) = _
  cases store (heap.forward reader) source <;> rfl

theorem reverse_statement_execution (heap : Heap Ptr) (reader source : Ptr) :
    executeAssignment (iterationEnvironment reader source) heap reverseSite.statement =
      (store (heap.reverse source) reader).map fun written =>
        (⟨heap.forward, Function.update heap.reverse source written⟩ : Heap Ptr) := by
  change (store (heap.reverse source) reader).bind (fun written =>
    some (⟨heap.forward, Function.update heap.reverse source written⟩ : Heap Ptr)) = _
  cases store (heap.reverse source) reader <;> rfl

theorem actual_stores_execute_link (heap : Heap Ptr) (reader source : Ptr) :
    executeAssignments (iterationEnvironment reader source) heap
      [forwardSite.statement, reverseSite.statement] = writeLink heap reader source := by
  simp only [executeAssignments, forward_statement_execution]
  cases first : store (heap.forward reader) source with
  | none => simp [first, writeLink]
  | some forward =>
    simp only [Option.map_some, Option.bind]
    rw [reverse_statement_execution]
    cases second : store (heap.reverse source) reader <;> simp [writeLink, first, second]

/-- This boundary admits the actual pointer declaration and evaluates its
returned continuation. It does not replace the remaining AST with known stores. -/
def executeIndexedBody (heap : Heap Ptr) (reader : Ptr) (pending : List Ptr)
    (index : UInt32) : List CStatement → Option (Heap Ptr)
  | .declare type name
      (.index (.field (.identifier reservation) field true) (.identifier counter)) :: rest =>
    if type = ⟨"Space".toList, 1⟩ ∧ name = "dependency".toList ∧
        reservation = "reservation".toList ∧ field = "pending".toList ∧ counter = "i".toList then
      pending[index.toNat]?.bind fun source =>
        executeAssignments (iterationEnvironment reader source) heap rest
    else none
  | _ => none

/-- The load uses the actual index; it neither snapshots a different order nor
deduplicates the pending list. An out-of-range load has no defined transition. -/
def executeIndexedIteration (heap : Heap Ptr) (reader : Ptr) (pending : List Ptr)
    (index : UInt32) : Option (Heap Ptr) :=
  executeIndexedBody heap reader pending index iterationBody

theorem loaded_iteration_executes_link (heap : Heap Ptr) (reader : Ptr)
    (pending : List Ptr) (index : UInt32) (source : Ptr)
    (loaded : pending[index.toNat]? = some source) :
    executeIndexedIteration heap reader pending index = writeLink heap reader source := by
  simp [executeIndexedIteration, executeIndexedBody, iterationBody, loaded, actual_stores_execute_link]

inductive LoopResult (Ptr : Type) where
  | finished (result : Option (Heap Ptr))
  | exhausted

/-- The admitted header tests before each body, increments after each body,
and discards the postfix result. Proof fuel is not a C failure or no-op. -/
def executeLoop (fuel : Nat) (heap : Heap Ptr) (reader : Ptr) (pending : List Ptr)
    (index limit : UInt32) (body : List CStatement := iterationBody) : LoopResult Ptr :=
  if index < limit then
    match fuel with
    | 0 => .exhausted
    | fuel + 1 =>
      match executeIndexedBody heap reader pending index body with
      | none => .finished none
      | some next => executeLoop fuel next reader pending (index + 1) limit body
  else .finished (some heap)

theorem loop_refines_remaining (heap : Heap Ptr) (reader : Ptr) (remaining : List Ptr)
    (prior : List Ptr) (index limit : UInt32) (fuel : Nat)
    (position : index.toNat = prior.length)
    (extent : limit.toNat = (prior ++ remaining).length)
    (enough : remaining.length ≤ fuel) :
    executeLoop fuel heap reader (prior ++ remaining) index limit =
      .finished (writeBatch heap reader remaining) := by
  induction remaining generalizing heap prior index fuel with
  | nil =>
    have stopped : ¬ index < limit := by
      rw [UInt32.lt_iff_toNat_lt]
      simpa [position] using extent.le
    rw [executeLoop.eq_def, if_neg stopped]
    rfl
  | cons source rest ih =>
    have pending : index < limit := by
      rw [UInt32.lt_iff_toNat_lt]
      simp only [List.length_append, List.length_cons] at extent
      omega
    have increment : (index + 1).toNat = index.toNat + 1 := by
      rw [UInt32.toNat_add]
      apply Nat.mod_eq_of_lt
      have upper := limit.toNat_lt
      have before := UInt32.lt_iff_toNat_lt.mp pending
      change index.toNat + 1 < 2 ^ 32
      omega
    have loaded : (prior ++ source :: rest)[index.toNat]? = some source := by
      rw [position, List.getElem?_append_right (Nat.le_refl _)]
      simp
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      rw [executeLoop, if_pos pending]
      have iteration := loaded_iteration_executes_link heap reader _ index source loaded
      change executeIndexedBody heap reader (prior ++ source :: rest) index iterationBody =
        writeLink heap reader source at iteration
      rw [iteration]
      cases first : writeLink heap reader source with
      | none => simp [writeBatch, first]
      | some next =>
        have nextPosition : (index + 1).toNat = (prior ++ [source]).length := by
          simp [increment, position]
        have nextExtent : limit.toNat = ((prior ++ [source]) ++ rest).length := by
          simpa [List.append_assoc] using extent
        have nextEnough : rest.length ≤ fuel := by simpa using enough
        have following := ih next (prior ++ [source]) (index + 1) fuel
          nextPosition nextExtent nextEnough
        simpa [List.append_assoc, writeBatch, first] using following

theorem publisher_loop_refines_batch (heap : Heap Ptr) (reader : Ptr)
    (pending : List Ptr) (added : UInt32) (exactExtent : added.toNat = pending.length) :
    executeLoop pending.length heap reader pending 0 added =
      .finished (writeBatch heap reader pending) := by
  simpa using loop_refines_remaining heap reader pending [] 0 added pending.length
    rfl exactExtent (Nat.le_refl _)

/-- The admitted header returns its actual body. No equality-to-template check
is used to authorize that body's stores. Parameter liveness remains external. -/
def publisherLoopBody? (function : CQualifiedFunction) : Option (List CStatement) :=
  if function.result = publisherFunction.result ∧
      function.parameters = publisherFunction.parameters then
    match function.body with
    | [.forLoop type counter (.unsignedInteger 0)
        (.binary .lt (.identifier compared)
          (.field (.identifier reservation) countField true))
        (.postIncrement (.identifier incremented)) body] =>
      if type = ⟨"uint32_t".toList, 0⟩ ∧ counter = "i".toList ∧
          compared = counter ∧ incremented = counter ∧
          reservation = "reservation".toList ∧ countField = "added".toList then
        some body
      else none
    | _ => none
  else none

def executeFunction (function : CQualifiedFunction) (fuel : Nat) (heap : Heap Ptr)
    (reader : Ptr) (pending : List Ptr) (added : UInt32) : Option (LoopResult Ptr) :=
  (publisherLoopBody? function).map fun body =>
    executeLoop fuel heap reader pending 0 added body

def executeQuotedFunction (fuel : Nat) (heap : Heap Ptr) (reader : Ptr)
    (pending : List Ptr) (added : UInt32) : Option (LoopResult Ptr) :=
  (qualifiedFunctionText? publisherTypeNames publisherSource.toList).bind fun function =>
    executeFunction function fuel heap reader pending added

theorem quoted_function_executes_admitted_loop (fuel : Nat) (heap : Heap Ptr)
    (reader : Ptr) (pending : List Ptr) (added : UInt32) :
    executeQuotedFunction fuel heap reader pending added =
      some (executeLoop fuel heap reader pending 0 added) := by
  rw [executeQuotedFunction, complete_source_admitted]
  rfl

theorem prepared_source_loop_represents_topology {Entry : Type*} {size : Nat}
    (state : OrderedDependencyStore.Store Entry size) (heap : Heap (Fin size))
    (reader : Fin size) (sources : List (Fin size)) (added : UInt32)
    (represented : Represents heap state)
    (observers : OrderedDependencyStore.ObserverInvariant state)
    (ready : Ready heap reader (OrderedDependencyBatch.collectMissing
      (state.members reader).deps [] sources))
    (exactExtent : added.toNat =
      (OrderedDependencyBatch.collectMissing (state.members reader).deps [] sources).length) :
    ∃ after, executeLoop added.toNat heap reader (OrderedDependencyBatch.collectMissing
        (state.members reader).deps [] sources) 0 added = .finished (some after) ∧
      Represents after (OrderedDependencyBatch.publish state reader sources) := by
  obtain ⟨after, written, related⟩ := prepared_publication_represents_topology
    state heap reader sources represented observers ready
  refine ⟨after, ?_, related⟩
  rw [exactExtent, publisher_loop_refines_batch _ _ _ _ exactExtent, written]

theorem prepared_quoted_function_represents_topology {Entry : Type*} {size : Nat}
    (state : OrderedDependencyStore.Store Entry size) (heap : Heap (Fin size))
    (reader : Fin size) (sources : List (Fin size)) (added : UInt32)
    (represented : Represents heap state)
    (observers : OrderedDependencyStore.ObserverInvariant state)
    (ready : Ready heap reader (OrderedDependencyBatch.collectMissing
      (state.members reader).deps [] sources))
    (exactExtent : added.toNat =
      (OrderedDependencyBatch.collectMissing (state.members reader).deps [] sources).length) :
    ∃ after, executeQuotedFunction added.toNat heap reader (OrderedDependencyBatch.collectMissing
        (state.members reader).deps [] sources) added = some (.finished (some after)) ∧
      Represents after (OrderedDependencyBatch.publish state reader sources) := by
  obtain ⟨after, completed, representedAfter⟩ := prepared_source_loop_represents_topology
    state heap reader sources added represented observers ready exactExtent
  exact ⟨after, by rw [quoted_function_executes_admitted_loop, completed], representedAfter⟩

namespace Controls

def withoutReverse : CQualifiedFunction :=
  { publisherFunction with body :=
    [.forLoop ⟨"uint32_t".toList, 0⟩ "i".toList (.unsignedInteger 0)
      (.binary .lt (.identifier "i".toList)
        (.field (.identifier "reservation".toList) "added".toList true))
      (.postIncrement (.identifier "i".toList)) (iterationBody.take 2)] }

def completedTopology : LoopResult (Fin 3) → Option (List (Fin 3) × List (Fin 3))
  | .finished (some heap) => some ((observe heap).forward 0, (observe heap).reverse 1)
  | _ => none

/-- Keeping the header but dropping an AST store does not silently restore it. -/
theorem omitted_reverse_in_actual_body_is_observable :
    (executeFunction withoutReverse 1 OrderedDependencyCArray.Controls.base 0 [1] 1).bind
      completedTopology = some ([1], []) := by decide

theorem both_actual_body_stores_are_observed :
    (executeFunction publisherFunction 1 OrderedDependencyCArray.Controls.base 0 [1] 1).bind
      completedTopology = some ([1], [0]) := by decide

theorem both_rhs_identities_retained :
    storeSyntax? forwardSite.statement = some forwardSite ∧
      storeSyntax? reverseSite.statement = some reverseSite :=
  ⟨recognizes_authored_store _, recognizes_authored_store _⟩

theorem wrong_count_field_is_not_resolved :
    spaceArrayField? "deps".toList "importer_count".toList = none := by decide

theorem absent_pointer_binding_has_no_execution :
    executeAssignment (fun _ => none) OrderedDependencyCArray.Controls.base
      forwardSite.statement = none := by decide

theorem absent_pending_slot_has_no_execution :
    executeIndexedIteration OrderedDependencyCArray.Controls.base 0 [] 0 = none := by decide

theorem empty_store_continuation_does_not_invent_links :
    executeIndexedBody OrderedDependencyCArray.Controls.base 0 [1] 0
      [.declare ⟨"Space".toList, 1⟩ "dependency".toList
        (.index (.field (.identifier "reservation".toList) "pending".toList true)
          (.identifier "i".toList))] = some OrderedDependencyCArray.Controls.base := rfl

theorem changed_rhs_is_observed :
    (executeAssignments (iterationEnvironment (0 : Fin 3) 1) OrderedDependencyCArray.Controls.base
      [(⟨"importer".toList, "deps".toList, "dep_count".toList,
        "importer".toList⟩ : StoreSyntax).statement, reverseSite.statement]).map
      (fun heap => (observe heap).forward 0) = some [0] := by decide

theorem exhausted_is_not_undefined_access :
    executeLoop 0 OrderedDependencyCArray.Controls.base 0 [1] 0 1 = .exhausted ∧
    executeLoop 1 OrderedDependencyCArray.Controls.base 0 [] 0 1 = .finished none := by
  constructor <;> rfl

theorem empty_reservation_needs_no_body_fuel :
    executeLoop 0 OrderedDependencyCArray.Controls.base 0 [] 0 0 =
      .finished (some OrderedDependencyCArray.Controls.base) := rfl

end Controls

#print axioms complete_source_admitted
#print axioms publisher_lexer_exact
#print axioms actual_stores_execute_link
#print axioms loaded_iteration_executes_link
#print axioms forward_statement_execution
#print axioms reverse_statement_execution
#print axioms loop_refines_remaining
#print axioms publisher_loop_refines_batch
#print axioms prepared_source_loop_represents_topology
#print axioms quoted_function_executes_admitted_loop
#print axioms prepared_quoted_function_represents_topology
#print axioms Controls.both_rhs_identities_retained
#print axioms Controls.wrong_count_field_is_not_resolved
#print axioms Controls.absent_pointer_binding_has_no_execution
#print axioms Controls.absent_pending_slot_has_no_execution
#print axioms Controls.empty_store_continuation_does_not_invent_links
#print axioms Controls.changed_rhs_is_observed
#print axioms Controls.exhausted_is_not_undefined_access
#print axioms Controls.empty_reservation_needs_no_body_fuel
#print axioms Controls.omitted_reverse_in_actual_body_is_observable
#print axioms Controls.both_actual_body_stores_are_observed

end Mettapedia.Machines.OrderedDependencyCSource
