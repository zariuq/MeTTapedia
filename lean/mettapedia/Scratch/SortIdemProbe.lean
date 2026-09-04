import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalKeyed

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode

def constantKey (_ : Pattern) : Nat := 0

#eval sortPatternsBy constantKey [.fvar "a", .fvar "b", .fvar "c"]
#eval sortPatternsBy constantKey
  (sortPatternsBy constantKey [.fvar "a", .fvar "b", .fvar "c"])
