import Mettapedia.Languages.GF.English.Linearization

open Mettapedia.Languages.GF.English.Linearization

private def preview (xs : List String) (k : Nat) : String :=
  String.intercalate "," (xs.take k)

def main : IO Unit := do
  let total := totalFunctionCount
  let explicit := explicitCoverageCount
  let explicitApply := explicitApplyCoverageCount
  let typedLeaf := typedLeafCoverageCount
  let overlap := applyLeafOverlapCount
  let uncovered := uncoveredFunctionNames
  let pct := explicitCoveragePercent
  let totalNonLex := nonLexicalFunctionCount
  let explicitNonLex := explicitNonLexicalCoverageCount
  let uncoveredNonLex := uncoveredNonLexicalFunctionNames
  let pctNonLex := explicitNonLexicalCoveragePercent

  IO.println s!"gf_en_linearization.total_functions={total}"
  IO.println s!"gf_en_linearization.explicit_handlers={explicit}"
  IO.println s!"gf_en_linearization.explicit_apply_handlers={explicitApply}"
  IO.println s!"gf_en_linearization.typed_leaf_handlers={typedLeaf}"
  IO.println s!"gf_en_linearization.apply_leaf_overlap={overlap}"
  IO.println s!"gf_en_linearization.uncovered_functions={uncovered.length}"
  IO.println s!"gf_en_linearization.explicit_percent={pct}"
  IO.println s!"gf_en_linearization.nonlex_total_functions={totalNonLex}"
  IO.println s!"gf_en_linearization.nonlex_explicit_handlers={explicitNonLex}"
  IO.println s!"gf_en_linearization.nonlex_uncovered_functions={uncoveredNonLex.length}"
  IO.println s!"gf_en_linearization.nonlex_explicit_percent={pctNonLex}"
  IO.println s!"gf_en_linearization.preview_uncovered_csv={preview uncovered 40}"
  IO.println s!"gf_en_linearization.preview_nonlex_uncovered_csv={preview uncoveredNonLex 40}"

  if total != explicit + uncovered.length then
    throw <| IO.userError "coverage accounting mismatch: explicit + uncovered != total"
  if explicit != explicitApply + typedLeaf - overlap then
    throw <| IO.userError "handler accounting mismatch: explicit != apply + leaf - overlap"
  if totalNonLex != explicitNonLex + uncoveredNonLex.length then
    throw <| IO.userError "nonlex coverage accounting mismatch: explicit + uncovered != total"
