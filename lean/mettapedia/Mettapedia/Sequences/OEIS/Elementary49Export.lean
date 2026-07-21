import Mettapedia.Sequences.OEIS.Elementary49

namespace Mettapedia.Sequences.OEIS.Elementary49Export

open Mettapedia.Sequences.OEIS
open Mettapedia.Sequences.OEIS.Elementary49

def generatedValues (formalization : Formalization) (count : Nat) : List Int :=
  (List.range count).map fun position =>
    formalization.spec.value (formalization.spec.index position)

def renderRow (formalization : Formalization) (count : Nat) : String :=
  String.intercalate "\t"
    [ formalization.source.oeisId,
      formalization.source.entrySha256,
      formalization.source.snapshotRevision,
      toString formalization.source.offset,
      String.intercalate "," ((generatedValues formalization count).map toString) ]

def main : IO Unit :=
  registry.forM fun formalization =>
    IO.println (renderRow formalization 140)

end Mettapedia.Sequences.OEIS.Elementary49Export

def main : IO Unit :=
  Mettapedia.Sequences.OEIS.Elementary49Export.main
