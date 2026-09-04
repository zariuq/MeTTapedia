import Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2TypedNativeWire

def main (args : List String) : IO Unit :=
  match args with
  | [path] =>
      Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2TypedNativeWire.writeWire path
  | _ => throw <| IO.userError "usage: ExportMM2TypedNative OUTPUT"
