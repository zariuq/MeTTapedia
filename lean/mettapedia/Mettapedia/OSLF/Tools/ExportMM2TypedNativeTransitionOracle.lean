import Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2TypedNativeTransitionOracle

def main (args : List String) : IO Unit :=
  match args with
  | [path] =>
      Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2TypedNativeTransitionOracle.writeWire path
  | _ => throw <| IO.userError
      "usage: ExportMM2TypedNativeTransitionOracle OUTPUT"
