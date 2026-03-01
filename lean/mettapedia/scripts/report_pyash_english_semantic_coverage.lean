import Mettapedia.OSLF.Framework.PyashGFEnglishFragment
import Mettapedia.OSLF.Framework.PyashGFComparative

open Mettapedia.OSLF.Framework.PyashGFEnglishFragment
open Mettapedia.OSLF.Framework.PyashGFComparative
open Mettapedia.OSLF.Framework.PyashGFInventory

def main : IO Unit := do
  let total := pyashEnglishHeadInventory.length
  let mapped := pyashEnglishObservedMappedHeadCount
  let unmapped := pyashEnglishObservedUnmappedHeadCount
  let mappedPct := pyashEnglishObservedMappedHeadPercent
  let isFull := mapped == total
  let canaryAll := pyashEnglishSemanticCoverageCanaries.all (fun row => row.2)
  let wdfTotal := pyashEnglishWDFAll.length
  let cmpAll := pyashEnglishComparativeCanaries.all (fun row => row.2)

  IO.println s!"pyash_en_semantic_coverage.total_observed_heads={total}"
  IO.println s!"pyash_en_semantic_coverage.mapped_observed_heads={mapped}"
  IO.println s!"pyash_en_semantic_coverage.unmapped_observed_heads={unmapped}"
  IO.println s!"pyash_en_semantic_coverage.mapped_observed_heads_percent={mappedPct}"
  IO.println s!"pyash_en_semantic_coverage.is_full={isFull}"
  IO.println s!"pyash_en_semantic_coverage.controlled_wdf_clauses={wdfTotal}"
  IO.println s!"pyash_en_semantic_coverage.canaries_all_true={canaryAll}"
  IO.println s!"pyash_en_semantic_coverage.comparative_canaries_all_true={cmpAll}"

  let mappedCsv := String.intercalate "," pyashEnglishObservedMappedHeads
  let unmappedCsv := String.intercalate "," pyashEnglishObservedUnmappedHeads
  IO.println s!"pyash_en_semantic_coverage.mapped_heads_csv={mappedCsv}"
  IO.println s!"pyash_en_semantic_coverage.unmapped_heads_csv={unmappedCsv}"

  for row in pyashEnglishMoodCoverageRows do
    IO.println s!"pyash_en_semantic_coverage.mood.{row.1}.mapped_heads={row.2}"

  if !canaryAll || !cmpAll then
    throw <| IO.userError "pyash_en_semantic_coverage canary bundle failed"
