import Algorithms.GF.CompiledIR

namespace Algorithms.GF.Tokenize

open Algorithms.GF.CompiledIR

private def isSeparator (c : Char) : Bool :=
  c.isWhitespace || c ∈ [',', '.', ';', ':', '!', '?', '(', ')', '[', ']', '{', '}', '"']

private def isWordChar (c : Char) : Bool :=
  !isSeparator c

private def flushToken (currRev : List Char) (accRev : List Tok) : List Tok :=
  if currRev.isEmpty then
    accRev
  else
    String.ofList currRev.reverse :: accRev

private def tokenizeAux : List Char → List Char → List Tok → List Tok
  | [], currRev, accRev => (flushToken currRev accRev).reverse
  | c :: cs, currRev, accRev =>
      let c := c.toLower
      if isWordChar c then
        tokenizeAux cs (c :: currRev) accRev
      else
        tokenizeAux cs [] (flushToken currRev accRev)

def tokenize (input : String) : Array Tok :=
  (tokenizeAux input.toList [] []).toArray

example : tokenize "John saw the man with the telescope." =
    #["john", "saw", "the", "man", "with", "the", "telescope"] := by
  decide

example : tokenize "Anna dressed the baby in the crib" =
    #["anna", "dressed", "the", "baby", "in", "the", "crib"] := by
  decide

end Algorithms.GF.Tokenize
