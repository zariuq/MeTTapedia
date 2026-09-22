import Mettapedia.GSLT.Parsing.PlainBnfControllerObservedAnswers
import Mettapedia.GSLT.Parsing.PlainBnfGraphDiagnosticsSourceExecution

/-!
# Productive discovery followed by ordered unproductive diagnostics

The actual productive Closure supplies the valid known packet consumed by
the actual diagnostic clauses. Exact index and history are derived from
execution, not assumed as a membership oracle. Diagnostics retain original
declaration order and spans, and their membership is precisely nonproductivity
in the independently defined grammar least fixed point.

This connects selected source calls. The entire analysis wrapper, reachability,
generated continuations, and native execution remain separate boundaries.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfControllerDiagnostics

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (Step engineBasePremises)
open PlainBnfSemanticAdmission (AdmittedInput)
open PlainBnfStructuredDenotation (SourceSpan)
open PlainBnfStructuredDiscoveryGraph (Definitions definitionsFromDocument nameAt graphKnown)
open PlainBnfStructuredEnumeration (candidates)
open PlainBnfControllerPublicationFrontier (graph)
open PlainBnfOrderedGraphDiscovery (runEvents)
open PlainBnfReferenceCollectionSourceExecution (text)
open PlainBnfWakeContextualExecution (NameIndex)
open PlainBnfTrieSourceExecution (result result_injective trie scalarRelations)
open PlainBnfLexicalMatcherSourceExecution (relations)
open PlainBnfKnownNamesSourceExecution (known known_eq_iff Valid)
open PlainBnfRunSourceExecution (closureCall)
open PlainBnfControllerCompletedAnswers (admitted_closure_reference_answers)

theorem closure_packet_valid (productive : Bool) (admitted : AdmittedInput) (reverse : NameIndex)
    (indexed : Step (engineBasePremises scalarRelations) PlainBnfReverseIndexSourceExecution.language
      (PlainBnfReverseIndexSourceExecution.reverseCall (candidates (definitionsFromDocument admitted.document))
        admitted.authority.lexicalDeclarations .empty) (result (trie reverse)))
    (index : NameIndex) (history : List SExpr)
    (closed : Step (engineBasePremises relations) PlainBnfRunSourceFamily.language
      (closureCall productive (candidates (definitionsFromDocument admitted.document)) reverse
        admitted.authority.lexicalDeclarations) (result (known index history))) : Valid index history := by
  have packet := (admitted_closure_reference_answers productive admitted reverse indexed).1 _ |>.mp closed
  obtain ⟨rfl, rfl⟩ := (known_eq_iff _ _ _ _).mp (result_injective packet)
  exact PlainBnfControllerReferenceIndex.index_history_fold_valid _ _ .empty []
    PlainBnfKnownNamesSourceExecution.valid_empty

/-- The history invariant required by diagnostics is discharged by Closure,
so it is not a new caller assumption. -/
theorem completed_diagnostics_iff (admitted : AdmittedInput) (reverse : NameIndex)
    (indexed : Step (engineBasePremises scalarRelations) PlainBnfReverseIndexSourceExecution.language
      (PlainBnfReverseIndexSourceExecution.reverseCall (candidates (definitionsFromDocument admitted.document))
        admitted.authority.lexicalDeclarations .empty) (result (trie reverse)))
    (index : NameIndex) (history : List SExpr)
    (closed : Step (engineBasePremises relations) PlainBnfRunSourceFamily.language
      (closureCall true (candidates (definitionsFromDocument admitted.document)) reverse
        admitted.authority.lexicalDeclarations) (result (known index history)))
    (target : Pattern) :
    Step (engineBasePremises scalarRelations) (PlainBnfGraphDiagnosticsSourceExecution.language true)
      (PlainBnfGraphDiagnosticsSourceExecution.diagnosticsCall true (definitionsFromDocument admitted.document)
        index history) target ↔
      target = result (PlainBnfGraphDiagnosticsSourceExecution.diagnostics true
        (((definitionsFromDocument admitted.document).filter fun definition =>
          decide (text definition.name ∉ history)).map (fun definition => (definition.name, definition.span)))) :=
  PlainBnfGraphDiagnosticsSourceExecution.valid_diagnostics_step_iff true _ index history
    (closure_packet_valid true admitted reverse indexed index history closed) target

/-- The exact ordered diagnostic result after the real productive controller.
The selector is productive, not nullable; false in the diagnostic family
denotes unreachable diagnostics and is intentionally not used here. -/
theorem closure_unproductive_diagnostics_iff (admitted : AdmittedInput) (reverse : NameIndex)
    (indexed : Step (engineBasePremises scalarRelations) PlainBnfReverseIndexSourceExecution.language
      (PlainBnfReverseIndexSourceExecution.reverseCall (candidates (definitionsFromDocument admitted.document))
        admitted.authority.lexicalDeclarations .empty) (result (trie reverse)))
    (target : Pattern) :
    let definitions := definitionsFromDocument admitted.document
    let lexicals := admitted.authority.lexicalDeclarations
    let events := runEvents (graph true definitions lexicals) definitions.length (graphKnown definitions []) 0 0
    let history := events.foldl (fun current event => text (nameAt definitions event.position) :: current) []
    (∃ (index : NameIndex) (actualHistory : List SExpr),
      Step (engineBasePremises relations) PlainBnfRunSourceFamily.language
        (closureCall true (candidates definitions) reverse lexicals) (result (known index actualHistory)) ∧
      Step (engineBasePremises scalarRelations) (PlainBnfGraphDiagnosticsSourceExecution.language true)
        (PlainBnfGraphDiagnosticsSourceExecution.diagnosticsCall true definitions index actualHistory) target) ↔
      target = result (PlainBnfGraphDiagnosticsSourceExecution.diagnostics true
        ((definitions.filter fun definition => decide (text definition.name ∉ history)).map
          (fun definition => (definition.name, definition.span)))) := by
  dsimp only
  have complete := (admitted_closure_reference_answers true admitted reverse indexed).1
  constructor
  · rintro ⟨index, history, closed, diagnosed⟩
    have packet := (complete _).mp closed
    obtain ⟨rfl, rfl⟩ := (known_eq_iff _ _ _ _).mp (result_injective packet)
    exact (completed_diagnostics_iff admitted reverse indexed _ _ closed target).mp diagnosed
  · intro same
    have closed := (complete _).mpr rfl
    exact ⟨_, _, closed, (completed_diagnostics_iff admitted reverse indexed _ _ closed target).mpr same⟩

/-- Every returned diagnostic refers to an original declaration occurrence
whose name is absent from the independent least productive set, and every
such occurrence appears. Order and multiplicity are stronger list properties
retained by the preceding exact-result theorem. -/
theorem completed_diagnostic_membership (admitted : AdmittedInput) (reverse : NameIndex)
    (indexed : Step (engineBasePremises scalarRelations) PlainBnfReverseIndexSourceExecution.language
      (PlainBnfReverseIndexSourceExecution.reverseCall (candidates (definitionsFromDocument admitted.document))
        admitted.authority.lexicalDeclarations .empty) (result (trie reverse)))
    (index : NameIndex) (history : List SExpr)
    (closed : Step (engineBasePremises relations) PlainBnfRunSourceFamily.language
      (closureCall true (candidates (definitionsFromDocument admitted.document)) reverse
        admitted.authority.lexicalDeclarations) (result (known index history)))
    (output : List (String × SourceSpan))
    (diagnosed : Step (engineBasePremises scalarRelations) (PlainBnfGraphDiagnosticsSourceExecution.language true)
      (PlainBnfGraphDiagnosticsSourceExecution.diagnosticsCall true (definitionsFromDocument admitted.document)
        index history) (result (PlainBnfGraphDiagnosticsSourceExecution.diagnostics true output))) :
    ∀ pair, pair ∈ output ↔ ∃ definition ∈ definitionsFromDocument admitted.document,
      pair = (definition.name, definition.span) ∧
      definition.name ∉ PlainBnfGraphSemantics.Productive admitted.document admitted.authority := by
  have outputExact := (PlainBnfGraphDiagnosticsSourceExecution.diagnostics_decoded_step_iff
    true _ index history output).mp diagnosed
  rw [outputExact, PlainBnfGraphDiagnosticsSourceExecution.missing_eq_history_filter _ index history
    (closure_packet_valid true admitted reverse indexed index history closed)]
  intro pair
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  have members := PlainBnfControllerLeastFixedPoint.closure_answer_membership
    true admitted reverse indexed index history closed
  constructor
  · rintro ⟨definition, ⟨inside, missing⟩, same⟩
    exact ⟨definition, inside, same.symm, fun member => missing ((members definition.name).mpr member)⟩
  · rintro ⟨definition, inside, same, absent⟩
    exact ⟨definition, ⟨inside, fun member => absent ((members definition.name).mp member)⟩, same.symm⟩

#print axioms closure_packet_valid
#print axioms completed_diagnostics_iff
#print axioms closure_unproductive_diagnostics_iff
#print axioms completed_diagnostic_membership

end Mettapedia.GSLT.Parsing.PlainBnfControllerDiagnostics
