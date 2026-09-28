import Mettapedia.GSLT.Parsing.PlainBnfDeclarationAccumulator
import Mettapedia.GSLT.Parsing.PlainBnfDeclarationReflection

/-!
# Authored declaration results and the distinct-key accumulator

The source inventory and provider hypotheses are discharged by the source
quotation client. These theorems connect its existing declaration operations
to the independently proved accumulator result. They do not claim that new
accumulator GSLT rules or a native lowering have been authored or generated.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfDeclarationAccumulatorSource

open HornCertificate
open PlainBnfDeclarationEncoding
open PlainBnfDeclarationSemantics PlainBnfDeclarationSource PlainBnfDeclarationRealization
open PlainBnfDeclarationReflection PlainBnfDeclarationAccumulator

theorem source_empty_iff_accumulator_outputs {program : Program} {offset : Nat}
    (source : HasDeclarationRules program offset) (only : OnlyDeclarationRules program offset)
    (noDifferent : NoDifferentRules program) (noDeclarations : NoDeclarationProviders program)
    (differentSound : DifferentProviderSound program) (differentRuns : DifferentRealizes program)
    (entries : List (Entry GroundTerm GroundTerm GroundTerm GroundTerm)) (after diagnostics : GroundTerm)
    (canonical : CanonicalEntries entries) :
    Realizable program ⟨"BNFCollectDefinitionsV1", GroundTerms.ofList
      [encodeEntries entries, encodeDefinitions [], after, diagnostics]⟩ ↔
      after = encodeDefinitions (collectFromEmptyFast entries).1 ∧
      diagnostics = encodeDiagnostics (collectFromEmptyFast entries).2 := by
  rw [collectFromEmptyFast_eq]
  exact collect_realizable_iff_outputs source only noDifferent noDeclarations
    differentSound differentRuns entries [] after diagnostics canonical
    (by intro definition member; cases member)

/-- Every successful source result from the empty environment carries the
distinct-key refinement required by the accumulator specialization. -/
theorem source_empty_definitions_distinct {program : Program} {offset : Nat}
    (source : HasDeclarationRules program offset) (only : OnlyDeclarationRules program offset)
    (noDifferent : NoDifferentRules program) (noDeclarations : NoDeclarationProviders program)
    (differentSound : DifferentProviderSound program)
    (entries : List (Entry GroundTerm GroundTerm GroundTerm GroundTerm)) (after diagnostics : GroundTerm)
    (canonical : CanonicalEntries entries)
    (runs : Realizable program ⟨"BNFCollectDefinitionsV1", GroundTerms.ofList
      [encodeEntries entries, encodeDefinitions [], after, diagnostics]⟩) :
    ∃ definitions, after = encodeDefinitions definitions ∧ DistinctDefinitionNames definitions := by
  obtain ⟨fuel, actions, path⟩ := runs
  have outputs := collect_path_reflects_outputs source only noDifferent noDeclarations
    differentSound entries [] after diagnostics canonical
    (by intro definition member; cases member) path
  exact ⟨(collect entries []).1, outputs.1, collect_empty_distinct entries⟩

end Mettapedia.GSLT.Parsing.PlainBnfDeclarationAccumulatorSource
