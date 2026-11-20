import Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-!
# Native constructor code for an already read data template

This is the Atom-carrier counterpart of the direct compiler's emitted
structural spine. Leaves remain values or variable references. Every source
expression is assembled from the existing native constructor, ending in the
actual empty-expression spelling that the emitter writes.

This module defines source code, not another evaluator. Its execution laws
use the existing PeTTa machine and standard primitive table.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPattern

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

mutual
  def atomCode : Atom → Atom
    | .var name => .var name
    | .symbol name => .symbol name
    | .grounded value => .grounded value
    | .expression items => listCode items

  def listCode : List Atom → Atom
    | [] => .expression []
    | first :: rest => .expression [.symbol "cons-atom", atomCode first, listCode rest]
end

end Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPattern
