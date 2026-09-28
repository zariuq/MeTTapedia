import Mettapedia.GSLT.Parsing.PlainBnfRunSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfControllerPublicationFrontier

/-!
# Indexed source inputs through the actual Run/Closure rules

Actual reverse-index execution discharges the publication rule's dependent
bucket premise. Actual enumeration supplies the closure's complete ordered
candidate input. These are compositions of proved source executions, not
whole-loop convergence or generated/native correctness theorems.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfRunIndexedInputs

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (Step engineBasePremises)
open PlainBnfLexicalMatcherSourceExecution (relations)
open PlainBnfTrieSourceExecution (scalarRelations result trie)
open PlainBnfReverseIndexSourceExecution (Item nodes)
open PlainBnfStructuredDenotation (LexicalDeclaration)
open PlainBnfWakeContextualExecution (NameIndex)
open PlainBnfWakeSourceExecution (heapItem)
open PlainBnfRunSourceFamily (language)
open PlainBnfRunSourceExecution
  (runCall closureCall publishedIndex publishedHistory publishedQueues initialQueues)
open Batteries.PairingHeapImp (Heap)

theorem run_publish_indexed_iff (productive : Bool) (item : Item) (input : List Item)
    (reverse index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (children following : Heap PlainBnfHeapSourceExecution.Item) (scheduled : NameIndex)
    (valid : PlainBnfKnownNamesSourceExecution.Valid index history)
    (indexed : Step (engineBasePremises scalarRelations) PlainBnfReverseIndexSourceExecution.language
      (PlainBnfReverseIndexSourceExecution.reverseCall input lexicals .empty) (result (trie reverse)))
    (output : Pattern) :
    Step (engineBasePremises relations) language
      (runCall productive reverse lexicals index history
        (.node (heapItem item) children .nil, following, scheduled)) output ↔
    Step (engineBasePremises relations) language
      (runCall productive reverse lexicals (publishedIndex item index) (publishedHistory item history)
        (publishedQueues productive item (PlainBnfStructuredReverseDependencies.bucket input item.2.name lexicals)
          history lexicals children following scheduled)) output :=
  PlainBnfRunSourceExecution.run_publish_iff productive item _ reverse index history lexicals
    children following scheduled valid
    (PlainBnfStructuredReverseDependencies.execution_lookup_bucket input item.2.name lexicals reverse indexed)
    output

theorem closure_enumerated_iff (productive : Bool)
    (definitions : PlainBnfStructuredDiscoveryGraph.Definitions) (input : List Item)
    (enumerated : Step (engineBasePremises scalarRelations) PlainBnfEnumerationSourceExecution.language
      (PlainBnfEnumerationSourceExecution.enumerationCall
        (definitions.map PlainBnfStructuredEnumeration.wireDefinition) .zero) (result (nodes input)))
    (reverse : NameIndex) (lexicals : List LexicalDeclaration) (output : Pattern) :
    Step (engineBasePremises relations) language (closureCall productive input reverse lexicals) output ↔
    Step (engineBasePremises relations) language
      (runCall productive reverse lexicals .empty []
        (initialQueues productive (PlainBnfStructuredEnumeration.candidates definitions) lexicals)) output := by
  have exactInput := (PlainBnfStructuredEnumeration.source_decoded_step_iff
    scalarRelations definitions input).mp enumerated
  subst input
  exact PlainBnfRunSourceExecution.closure_iff productive _ reverse lexicals output

/-- Empty internal work is a valid controller boundary, not admission of an
empty grammar by the public library. The exact empty known packet is returned. -/
theorem empty_closure_iff (productive : Bool) (reverse : NameIndex)
    (lexicals : List LexicalDeclaration) (output : Pattern) :
    Step (engineBasePremises relations) language (closureCall productive [] reverse lexicals) output ↔
      output = result (PlainBnfKnownNamesSourceExecution.known (.empty : NameIndex) []) := by
  rw [PlainBnfRunSourceExecution.closure_iff]
  exact PlainBnfRunSourceExecution.run_done productive reverse lexicals .empty [] .empty output

theorem empty_closure_cannot_invent_atom (productive : Bool) (reverse : NameIndex)
    (lexicals : List LexicalDeclaration) (atom : String) :
    ¬ Step (engineBasePremises relations) language (closureCall productive [] reverse lexicals)
      (result (.atom atom)) := by
  rw [empty_closure_iff, PlainBnfTrieSourceExecution.result_injective.eq_iff]
  simp [PlainBnfKnownNamesSourceExecution.known]

#print axioms run_publish_indexed_iff
#print axioms closure_enumerated_iff
#print axioms empty_closure_iff
#print axioms empty_closure_cannot_invent_atom

end Mettapedia.GSLT.Parsing.PlainBnfRunIndexedInputs
