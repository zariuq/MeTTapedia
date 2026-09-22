import Mettapedia.GSLT.Parsing.PlainBnfControllerPublicationFrontier
import Mettapedia.GSLT.Parsing.PlainBnfRunSourceExecution

/-!
# Actual controller initialization and its structural invariants

The source's existing initial Wake produces ordered, correctly partitioned
heaps with unique pending positions and exact scheduled marks. Actual source
enumeration supplies candidate coverage and complete payload alignment. Both
discovery modes initialize exactly their existing graph ready frontiers.

The Closure equivalence below factors its actual initial Wake and recursive
Run calls; it does not establish that Run terminates. Coordinates remain an
explicit interpretation of the actual live ranks. No default decoding for
invalid ranks, new invariant carrier, queue algorithm, or runtime is added.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfControllerInitialization

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (Step engineBasePremises)
open PlainBnfStructuredDenotation (LexicalDeclaration)
open PlainBnfLexicalMatcherSourceExecution (relations)
open PlainBnfTrieSourceExecution (scalarRelations result)
open PlainBnfReverseIndexSourceExecution (Item key nodes)
open PlainBnfStructuredDiscoveryGraph
open PlainBnfStructuredEnumeration (wireDefinition candidates)
open PlainBnfSourceRank (value)
open PlainBnfWakeSourceExecution
  (HeapItem heapItem Queues Ordered WellPlaced MarkedPositions pending encodeQueues)
open PlainBnfTwoHeapWorklist (UniquePositions)
open PlainBnfWakeFrontierExactness (ExactMarks)
open PlainBnfWakeContextualExecution (NameIndex meaning wakeCall)
open PlainBnfRunSourceExecution (initialQueues closureCall runCall)
open PlainBnfControllerPublicationFrontier (graph)

/-- Arbitrary targets reflect to the complete initial queue packet of the
actual Run-family Wake call. The known-name index starts genuinely empty. -/
theorem initial_wake_step_iff (productive : Bool) (input : List Item)
    (lexicals : List LexicalDeclaration) (output : Pattern) :
    Step (engineBasePremises relations) PlainBnfRunSourceFamily.language
      (wakeCall productive input none .empty [] lexicals (.nil, .nil, .empty)) output ↔
      output = result (encodeQueues (initialQueues productive input lexicals)) := by
  rw [PlainBnfRunSourceFamily.wake_step_iff _ _ (by rfl)]
  exact PlainBnfWakeContextualExecution.wake_step_iff productive input none .empty [] lexicals
    (.nil, .nil, .empty) PlainBnfKnownNamesSourceExecution.valid_empty output

theorem initial_wake_executes (productive : Bool) (input : List Item)
    (lexicals : List LexicalDeclaration) :
    Step (engineBasePremises relations) PlainBnfRunSourceFamily.language
      (wakeCall productive input none .empty [] lexicals (.nil, .nil, .empty))
      (result (encodeQueues (initialQueues productive input lexicals))) :=
  (initial_wake_step_iff productive input lexicals _).mpr rfl

/-- Actual enumeration and its live rank observation establish every stated
initial structural invariant. Source payloads and their occurrences remain
in the existing candidate list and heaps, not a replacement finite set. -/
theorem initialQueues_invariants
    (productive : Bool) (admitted : PlainBnfSemanticAdmission.AdmittedInput) (input : List Item)
    (enumerated : Step (engineBasePremises scalarRelations) PlainBnfEnumerationSourceExecution.language
      (PlainBnfEnumerationSourceExecution.enumerationCall
        ((definitionsFromDocument admitted.document).map wireDefinition) .zero) (result (nodes input)))
    (coordinate : HeapItem → Fin (definitionsFromDocument admitted.document).length)
    (liveRanks : ∀ item ∈ input, (coordinate (heapItem item)).val = value item.1) :
    let queues := initialQueues productive input admitted.authority.lexicalDeclarations
    Ordered queues ∧ WellPlaced coordinate none queues ∧
      UniquePositions coordinate queues.1 queues.2.1 ∧
      ExactMarks coordinate (fun p => key (nameAt (definitionsFromDocument admitted.document) p)) ∅ queues ∧
      pending coordinate queues = PlainBnfDependencyWorklist.initialQueue
        (graph productive (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations)
        (graphKnown (definitionsFromDocument admitted.document) []) ∧
      PlainBnfKnownNamesSourceExecution.Valid (.empty : NameIndex) [] ∧
      HistoryScoped (definitionsFromDocument admitted.document) [] := by
  have actualInput := (PlainBnfStructuredEnumeration.source_decoded_step_iff
    scalarRelations _ input).mp enumerated
  subst input
  have nameCoordinates := PlainBnfStructuredEnumeration.coordinate_names
    (definitionsFromDocument admitted.document) coordinate liveRanks
  have keys : ∀ item ∈ candidates (definitionsFromDocument admitted.document),
      key (nameAt (definitionsFromDocument admitted.document) (coordinate (heapItem item))) = key item.2.name :=
    fun item member => congrArg key (nameCoordinates item member)
  have namesInjective : Function.Injective
      (fun p => key (nameAt (definitionsFromDocument admitted.document) p)) :=
    PlainBnfReverseIndexSourceExecution.key_injective.comp
      (nameAt_injective _ (admitted_definition_names_unique admitted))
  have emptyPlaced : WellPlaced coordinate none (.nil, .nil, .empty) := by
    simpa only [WellPlaced, pending, PlainBnfTwoHeapWorklist.positions_nil,
      Finset.empty_union] using PlainBnfTwoHeapWorklist.empty_partition coordinate
        (PlainBnfScheduleWorklistBridge.cursor none)
  have emptyMarked : MarkedPositions coordinate
      (fun p => key (nameAt (definitionsFromDocument admitted.document) p)) (.nil, .nil, .empty) := by
    intro position member
    simp [pending, PlainBnfTwoHeapWorklist.positions_nil] at member
  have structural := PlainBnfWakeSourceExecution.wake_invariants
    (meaning productive [] admitted.authority.lexicalDeclarations) coordinate
    (fun p => key (nameAt (definitionsFromDocument admitted.document) p)) none
    (candidates _) (.nil, .nil, .empty) ⟨.nil, .nil⟩ emptyPlaced
    (PlainBnfTwoHeapWorklist.unique_empty coordinate) emptyMarked
    (fun item member => (liveRanks item member).symm) keys
  have exactMarks := PlainBnfWakeFrontierExactness.wake_exact_marks coordinate
    (fun p => key (nameAt (definitionsFromDocument admitted.document) p)) namesInjective
    (meaning productive [] admitted.authority.lexicalDeclarations) none (candidates _)
    (.nil, .nil, .empty) ∅ ⟨.nil, .nil⟩
    (PlainBnfWakeFrontierExactness.empty_exact_marks coordinate _) keys
  refine ⟨structural.1, structural.2.1, structural.2.2.1, exactMarks, ?_,
    PlainBnfKnownNamesSourceExecution.valid_empty, empty_history_scoped _⟩
  have actualWake := initial_wake_executes productive (candidates (definitionsFromDocument admitted.document))
    admitted.authority.lexicalDeclarations
  cases productive with
  | false =>
      exact PlainBnfControllerInputExecution.enumerated_nullable_initialQueue admitted
        (candidates _) enumerated coordinate liveRanks none _ actualWake
  | true =>
      exact PlainBnfControllerInputExecution.enumerated_productive_initialQueue admitted
        (candidates _) enumerated coordinate liveRanks none _ actualWake

/-- The same invariants concern the actual returned source packet, not only
the independent queue observation that defines `initialQueues`. -/
theorem execution_initialization
    (productive : Bool) (admitted : PlainBnfSemanticAdmission.AdmittedInput) (input : List Item)
    (enumerated : Step (engineBasePremises scalarRelations) PlainBnfEnumerationSourceExecution.language
      (PlainBnfEnumerationSourceExecution.enumerationCall
        ((definitionsFromDocument admitted.document).map wireDefinition) .zero) (result (nodes input)))
    (coordinate : HeapItem → Fin (definitionsFromDocument admitted.document).length)
    (liveRanks : ∀ item ∈ input, (coordinate (heapItem item)).val = value item.1)
    (queues : Queues)
    (executed : Step (engineBasePremises relations) PlainBnfRunSourceFamily.language
      (wakeCall productive input none .empty [] admitted.authority.lexicalDeclarations (.nil, .nil, .empty))
      (result (encodeQueues queues))) :
    queues = initialQueues productive input admitted.authority.lexicalDeclarations ∧
      Ordered queues ∧ WellPlaced coordinate none queues ∧
      UniquePositions coordinate queues.1 queues.2.1 ∧
      ExactMarks coordinate (fun p => key (nameAt (definitionsFromDocument admitted.document) p)) ∅ queues ∧
      pending coordinate queues = PlainBnfDependencyWorklist.initialQueue
        (graph productive (definitionsFromDocument admitted.document) admitted.authority.lexicalDeclarations)
        (graphKnown (definitionsFromDocument admitted.document) []) ∧
      PlainBnfKnownNamesSourceExecution.Valid (.empty : NameIndex) [] ∧
      HistoryScoped (definitionsFromDocument admitted.document) [] := by
  have actualQueues := PlainBnfWakeContextualExecution.result_queues_injective
    ((initial_wake_step_iff productive input admitted.authority.lexicalDeclarations _).mp executed)
  subst queues
  exact ⟨rfl, initialQueues_invariants productive admitted input enumerated coordinate liveRanks⟩

/-- Exact factorization of the authored Closure call through its initial
Wake and recursive Run. This does not posit a final Run result or fuel. -/
theorem closure_initialization_iff (productive : Bool) (input : List Item) (reverse : NameIndex)
    (lexicals : List LexicalDeclaration) (output : Pattern) :
    Step (engineBasePremises relations) PlainBnfRunSourceFamily.language
      (closureCall productive input reverse lexicals) output ↔
    ∃ queues : Queues,
      Step (engineBasePremises relations) PlainBnfRunSourceFamily.language
        (wakeCall productive input none .empty [] lexicals (.nil, .nil, .empty))
        (result (encodeQueues queues)) ∧
      Step (engineBasePremises relations) PlainBnfRunSourceFamily.language
        (runCall productive reverse lexicals .empty [] queues) output := by
  rw [PlainBnfRunSourceExecution.closure_iff]
  constructor
  · intro executed
    exact ⟨initialQueues productive input lexicals, initial_wake_executes productive input lexicals, executed⟩
  · rintro ⟨queues, wakeExecuted, runExecuted⟩
    have actualQueues := PlainBnfWakeContextualExecution.result_queues_injective
      ((initial_wake_step_iff productive input lexicals _).mp wakeExecuted)
    rwa [actualQueues] at runExecuted

theorem empty_published_positions (definitions : Definitions) :
    Finset.univ.filter (fun p => graphKnown definitions [] p) = ∅ := by
  simp [graphKnown, PlainBnfProductiveSourceExecution.member]

theorem empty_input_initialization (productive : Bool) (lexicals : List LexicalDeclaration) :
    Step (engineBasePremises relations) PlainBnfRunSourceFamily.language
      (wakeCall productive [] none .empty [] lexicals (.nil, .nil, .empty))
      (result (encodeQueues (.nil, .nil, .empty))) :=
  initial_wake_executes productive [] lexicals

private def controlSpan : PlainBnfStructuredDenotation.SourceSpan := { start := 0, stop := 1 }

private def literalItem (rank : PlainBnfSourceRank.Rank) : Item :=
  (rank, ⟨"literal",
    { alternatives := [{ elements := [.literal "x" controlSpan], span := controlSpan }],
      span := controlSpan }, controlSpan⟩)

private theorem literal_initialQueues (rank : PlainBnfSourceRank.Rank) :
    initialQueues true [literalItem rank] [] =
      PlainBnfWakeSourceExecution.enqueue none (literalItem rank) (.nil, .nil, .empty) ∧
    initialQueues false [literalItem rank] [] = (.nil, .nil, .empty) := by
  have productiveReady : meaning true [] [] (literalItem rank).2.expression = true := rfl
  have nullableReady : meaning false [] [] (literalItem rank).2.expression = false := rfl
  simp [initialQueues, PlainBnfWakeSourceExecution.wake_cons,
    PlainBnfWakeSourceExecution.wakeStep, PlainBnfWakeSourceExecution.wake_nil,
    productiveReady, nullableReady]

/-- The same source-spanned literal is a productive seed but not a nullable
seed. These are actual source executions, independent of a coordinate map. -/
theorem literal_initialization_modes (rank : PlainBnfSourceRank.Rank) :
    Step (engineBasePremises relations) PlainBnfRunSourceFamily.language
      (wakeCall true [literalItem rank] none .empty [] [] (.nil, .nil, .empty))
      (result (encodeQueues
        (PlainBnfWakeSourceExecution.enqueue none (literalItem rank) (.nil, .nil, .empty)))) ∧
    Step (engineBasePremises relations) PlainBnfRunSourceFamily.language
      (wakeCall false [literalItem rank] none .empty [] [] (.nil, .nil, .empty))
      (result (encodeQueues (.nil, .nil, .empty))) := by
  constructor
  · apply (initial_wake_step_iff true [literalItem rank] [] _).mpr
    rw [(literal_initialQueues rank).1]
  · apply (initial_wake_step_iff false [literalItem rank] [] _).mpr
    rw [(literal_initialQueues rank).2]

theorem nullable_literal_cannot_return_productive_packet (rank : PlainBnfSourceRank.Rank) :
    ¬ Step (engineBasePremises relations) PlainBnfRunSourceFamily.language
      (wakeCall false [literalItem rank] none .empty [] [] (.nil, .nil, .empty))
      (result (encodeQueues
        (PlainBnfWakeSourceExecution.enqueue none (literalItem rank) (.nil, .nil, .empty)))) := by
  intro executed
  have actual := PlainBnfWakeContextualExecution.result_queues_injective
    ((initial_wake_step_iff false [literalItem rank] [] _).mp executed)
  rw [(literal_initialQueues rank).2] at actual
  have first := congrArg Prod.fst actual
  cases first

end Mettapedia.GSLT.Parsing.PlainBnfControllerInitialization
