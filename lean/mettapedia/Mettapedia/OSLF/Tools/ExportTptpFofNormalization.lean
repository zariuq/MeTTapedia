import Mettapedia.GSLT.LanguageDef.TptpFofNormalizationLanguageDef

/-! Export the canonical wire of the proved FOF normalization language. -/

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [path] =>
      Mettapedia.GSLT.LanguageDef.TptpFofNormalizationLanguageDef.writeWire
        path
  | _ =>
      IO.eprintln
        "usage: ExportTptpFofNormalization <output-path>"
      IO.Process.exit 2
