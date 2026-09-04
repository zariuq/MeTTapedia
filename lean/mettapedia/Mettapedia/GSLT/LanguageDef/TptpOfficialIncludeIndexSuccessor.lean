import Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolutionResultCarrier
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Explicit source-index successor service for TPTP include resolution

Official include resolution preserves each formula's zero-based position in
its source file.  The structural controller traverses the official input list,
while this relation supplies the one arithmetic operation needed to advance
that position.  It accepts exactly canonical nonnegative decimal atoms and
returns exactly one canonical successor atom.

The relation performs no parsing, lookup, selection, or include expansion.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeIndexSuccessor

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine

def relationName : String := "TptpOfficialIncludeIndexSuccessor"

def zeroRelationName : String := "TptpOfficialIncludeIndexZero"

def zeroTuples (relation : String) (arguments : List Pattern) :
    List (List Pattern) :=
  match relation, arguments with
  | "TptpOfficialIncludeIndexZero", [_] => [[.apply "0" []]]
  | _, _ => []

def successorTuples (relation : String) (arguments : List Pattern) :
    List (List Pattern) :=
  match relation, arguments with
  | "TptpOfficialIncludeIndexSuccessor", [.apply current [], _] =>
      match current.toNat? with
      | none => []
      | some index =>
          [[.apply current [], .apply (toString (index + 1)) []]]
  | _, _ => []

def indexTuples (relation : String) (arguments : List Pattern) :
    List (List Pattern) :=
  zeroTuples relation arguments ++ successorTuples relation arguments

def relationEnv : RelationEnv where
  tuples := indexTuples

theorem zero_exact (output : Pattern) :
    indexTuples zeroRelationName [output] = [[.apply "0" []]] := by
  simp [indexTuples, zeroTuples, zeroRelationName, successorTuples]

theorem successor_exact (index : Nat) (output : Pattern) :
    indexTuples relationName
      [.apply (toString index) [], output] =
      [[.apply (toString index) [], .apply (toString (index + 1)) []]] := by
  simp [indexTuples, zeroTuples, successorTuples, relationName,
    Nat.toNat?_repr]

theorem successor_is_singleton (index : Nat) (output : Pattern) :
    (indexTuples relationName
      [.apply (toString index) [], output]).length = 1 := by
  rw [successor_exact]
  rfl

theorem non_atom_index_rejected :
    indexTuples relationName
      [.fvar "not-an-index", .fvar "output"] = [] := by
  rfl

theorem wrong_arity_rejected (index : Nat) :
    indexTuples relationName [.apply (toString index) []] = [] := by
  simp [indexTuples, zeroTuples, successorTuples, relationName]

#print axioms zero_exact
#print axioms successor_exact
#print axioms successor_is_singleton
#print axioms non_atom_index_rejected
#print axioms wrong_arity_rejected

end Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeIndexSuccessor
