import Mettapedia.GSLT.Parsing.PlainBnfWakeContextualExecution
import Mettapedia.GSLT.Parsing.PlainBnfWakeFrontierExactness
import Mettapedia.GSLT.Parsing.PlainBnfWakeGraphInitialization

/-!
# Authored Wake execution and the exact pending frontier

The source-execution theorem determines the complete returned queue packet.
Its occurrence-preserving observation then supplies the finite pending-set
and mark-provenance laws. These are conditional controller interfaces: the
caller must establish index consistency, heap order, and mark provenance.
They do not prove the enclosing Run/Closure loop or generated native code.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfWakeOperationalFrontier

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (Step engineBasePremises rewriteAt)
open PlainBnfStructuredDenotation (LexicalDeclaration)
open PlainBnfSourceRank (Rank)
open PlainBnfReverseIndexSourceExecution (Item key)
open PlainBnfKnownNamesSourceExecution (Valid)
open PlainBnfTrieSourceExecution (result)
open PlainBnfLexicalMatcherSourceExecution (relations)
open PlainBnfWakeSourceExecution
  (Queues HeapItem heapItem encodeQueues Ordered contents pending selected)
open PlainBnfWakeFrontierExactness
  (ExactMarks readyCandidatePositions)
open PlainBnfWakeContextualExecution (NameIndex meaning wakeCall wake_queues_step_iff)

variable {size : Nat}

/-- The finite frontier is an observation of actual authored execution,
not a replacement for its ordered occurrence ledger or full queue packet. -/
theorem execution_frontier (productive : Bool) (input : List Item) (origin : Option Rank)
    (index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (before after : Queues) (valid : Valid index history)
    (coordinate : HeapItem → Fin size) (nameAt : Fin size → List Nat)
    (namesInjective : Function.Injective nameAt) (completed : Finset (Fin size))
    (ordered : Ordered before) (marks : ExactMarks coordinate nameAt completed before)
    (keyCoordinates : ∀ item ∈ input, nameAt (coordinate (heapItem item)) = key item.2.name)
    (executed : Step (engineBasePremises relations) PlainBnfWakeSourceFamily.language
      (wakeCall productive input origin index history lexicals before) (result (encodeQueues after))) :
    pending coordinate after = pending coordinate before ∪
        (readyCandidatePositions coordinate (meaning productive history lexicals) input \ completed) ∧
      ExactMarks coordinate nameAt completed after := by
  have actual := (wake_queues_step_iff productive input origin index history lexicals before valid after).mp executed
  subst after
  exact ⟨PlainBnfWakeFrontierExactness.wake_pending_unpublished coordinate nameAt namesInjective
    (meaning productive history lexicals) origin input before completed ordered marks keyCoordinates,
    PlainBnfWakeFrontierExactness.wake_exact_marks coordinate nameAt namesInjective
      (meaning productive history lexicals) origin input before completed ordered marks keyCoordinates⟩

/-- Full heap payload multiplicity is retained independently of the finite
pending-set observer. No body, span, or selected occurrence is erased here. -/
theorem execution_contents (productive : Bool) (input : List Item) (origin : Option Rank)
    (index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (before after : Queues) (valid : Valid index history) (ordered : Ordered before)
    (executed : Step (engineBasePremises relations) PlainBnfWakeSourceFamily.language
      (wakeCall productive input origin index history lexicals before) (result (encodeQueues after))) :
    contents after =
      (↑((selected (meaning productive history lexicals) input before.2.2).map heapItem) :
        Multiset HeapItem) + contents before := by
  have actual := (wake_queues_step_iff productive input origin index history lexicals before valid after).mp executed
  subst after
  exact PlainBnfWakeSourceExecution.wake_contents (meaning productive history lexicals)
    origin input before ordered

open PlainBnfStructuredDiscoveryGraph
  (definitionsFromDocument nameAt expressionAt productiveGrammar nullableGrammar graphKnown)

/-- The actual productive Wake result initializes exactly the graph queue.
Source enumeration must still supply complete candidate coverage and agreement
with admitted definition names and bodies. Those obligations are not inferred
from merely running Wake successfully. -/
theorem execution_productive_initialQueue (admitted : PlainBnfSemanticAdmission.AdmittedInput)
    (coordinate : HeapItem → Fin (definitionsFromDocument admitted.document).length)
    (origin : Option Rank) (input : List Item) (after : Queues)
    (nameCoordinates : ∀ item ∈ input,
      nameAt (definitionsFromDocument admitted.document) (coordinate (heapItem item)) = item.2.name)
    (expressionCoordinates : ∀ item ∈ input,
      expressionAt (definitionsFromDocument admitted.document) (coordinate (heapItem item)) = item.2.expression)
    (covers : ∀ position, ∃ item ∈ input, coordinate (heapItem item) = position)
    (executed : Step (engineBasePremises relations) PlainBnfWakeSourceFamily.language
      (wakeCall true input origin .empty [] admitted.authority.lexicalDeclarations (.nil, .nil, .empty))
      (result (encodeQueues after))) :
    pending coordinate after =
      PlainBnfDependencyWorklist.initialQueue
        (productiveGrammar (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations)
        (graphKnown (definitionsFromDocument admitted.document) []) := by
  have actual := (wake_queues_step_iff true input origin .empty []
    admitted.authority.lexicalDeclarations (.nil, .nil, .empty)
    PlainBnfKnownNamesSourceExecution.valid_empty after).mp executed
  subst after
  have agrees : meaning true [] admitted.authority.lexicalDeclarations =
      PlainBnfProductiveSourceExecution.expressionMeaning [] admitted.authority.lexicalDeclarations := by
    funext expression
    rfl
  rw [agrees]
  exact PlainBnfWakeGraphInitialization.admitted_productive_empty_wake
    admitted coordinate origin input nameCoordinates expressionCoordinates covers

theorem execution_nullable_initialQueue (admitted : PlainBnfSemanticAdmission.AdmittedInput)
    (coordinate : HeapItem → Fin (definitionsFromDocument admitted.document).length)
    (origin : Option Rank) (input : List Item) (after : Queues)
    (nameCoordinates : ∀ item ∈ input,
      nameAt (definitionsFromDocument admitted.document) (coordinate (heapItem item)) = item.2.name)
    (expressionCoordinates : ∀ item ∈ input,
      expressionAt (definitionsFromDocument admitted.document) (coordinate (heapItem item)) = item.2.expression)
    (covers : ∀ position, ∃ item ∈ input, coordinate (heapItem item) = position)
    (executed : Step (engineBasePremises relations) PlainBnfWakeSourceFamily.language
      (wakeCall false input origin .empty [] admitted.authority.lexicalDeclarations (.nil, .nil, .empty))
      (result (encodeQueues after))) :
    pending coordinate after =
      PlainBnfDependencyWorklist.initialQueue (nullableGrammar (definitionsFromDocument admitted.document))
        (graphKnown (definitionsFromDocument admitted.document) []) := by
  have actual := (wake_queues_step_iff false input origin .empty []
    admitted.authority.lexicalDeclarations (.nil, .nil, .empty)
    PlainBnfKnownNamesSourceExecution.valid_empty after).mp executed
  subst after
  have agrees : meaning false [] admitted.authority.lexicalDeclarations =
      PlainBnfNullableSourceExecution.expressionMeaning [] := by
    funext expression
    rfl
  rw [agrees]
  exact PlainBnfWakeGraphInitialization.admitted_nullable_empty_wake
    admitted coordinate origin input nameCoordinates expressionCoordinates covers

theorem empty_input_preserves_packet (productive : Bool) (origin : Option Rank)
    (index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (queues : Queues) (valid : Valid index history) :
    Step (engineBasePremises relations) PlainBnfWakeSourceFamily.language
      (wakeCall productive [] origin index history lexicals queues) (result (encodeQueues queues)) := by
  apply (wake_queues_step_iff productive [] origin index history lexicals queues valid queues).mpr
  simp [PlainBnfWakeSourceExecution.wake_nil]

/-- The authored rule skips any found mark payload, including a stale one.
Successful source execution therefore cannot itself justify exact provenance. -/
theorem stale_mark_is_not_repaired (productive : Bool) (item : Item) (payload : SExpr)
    (index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (valid : Valid index history) :
    let queues : Queues := (.nil, .nil, PlainBnfGraphNameTrie.insertFirst (key item.2.name) payload .empty)
    Step (engineBasePremises relations) PlainBnfWakeSourceFamily.language
      (wakeCall productive [item] none index history lexicals queues) (result (encodeQueues queues)) := by
  dsimp only
  apply (wake_queues_step_iff productive [item] none index history lexicals _ valid _).mpr
  exact (PlainBnfWakeSourceExecution.stale_mark_can_suppress
    (meaning productive history lexicals) item payload).symm

theorem insufficient_depth_returns_no_answer (productive : Bool) (fuel : Nat)
    (input : List Item) (origin : Option Rank) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (queues : Queues) (valid : Valid index history)
    (insufficient : fuel ≤ PlainBnfWakeContextualExecution.wakeHeight
      productive origin index history lexicals input queues) :
    rewriteAt (engineBasePremises relations) PlainBnfWakeSourceFamily.language fuel
      (wakeCall productive input origin index history lexicals queues) = [] := by
  rw [PlainBnfWakeContextualExecution.wake_answers productive fuel input origin index history lexicals queues valid,
    if_neg (Nat.not_lt.mpr insufficient)]

#print axioms execution_frontier
#print axioms execution_contents
#print axioms execution_productive_initialQueue
#print axioms execution_nullable_initialQueue
#print axioms stale_mark_is_not_repaired
#print axioms insufficient_depth_returns_no_answer

end Mettapedia.GSLT.Parsing.PlainBnfWakeOperationalFrontier
