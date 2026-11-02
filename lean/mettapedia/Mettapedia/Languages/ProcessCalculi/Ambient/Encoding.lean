import Mettapedia.Languages.ProcessCalculi.Ambient.Core
import Mettapedia.Languages.ProcessCalculi.Ambient.Located

/-!
# The located form of an ambient process

An ambient process at a location is read as located atoms (`encode`): an ambient `m[P]` at `p` becomes a fresh
location `ℓ`, restricted around the marker `LAmb[p, ℓ, m]` and the located form of `P` at `ℓ`; a capability at `p`
becomes the located capability at `p`, its continuation read at `p`, and so does a prefix by a capability term; an
input at `p` becomes the located input at `p`, its body read at `p` under its binder; an output at `p` becomes the
located output at `p`; inaction, parallel composition, restriction and replication are read as themselves. The free variables of the process are renamed as they are read
(`relabel`): under a restriction the renaming is lifted past the restricted name, and under an ambient every free
variable moves past the fresh location.

The ambients' law that a restriction crosses an ambient boundary it does not name becomes, in located form, scope
extrusion and exchange of restrictions, which the restriction-block theory decides.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Encoding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (liftIndex)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (rename)

/-- A name read under one more binder. -/
def shiftName (name : Pattern) : Pattern := rename Nat.succ name

mutual
  /-- **The located form of an ambient process** at location `here`, its free variables renamed by `relabel`; a term
  of no ambient shape is only renamed. -/
  def encode (relabel : Nat → Nat) (here : Pattern) : Pattern → Pattern
    | .apply label [] => if label = "AZero" then .apply "LZero" [] else .apply label []
    | .apply label [.lambda binder body] =>
        if label = "ANu" then .apply "LNu" [.lambda binder (encode (liftIndex 1 relabel) (shiftName here) body)]
        else if label = "AInName" then
          .apply "LInName" [here, .lambda binder (encode (liftIndex 1 relabel) (shiftName here) body)]
        else if label = "AInCap" then
          .apply "LInCap" [here, .lambda binder (encode (liftIndex 1 relabel) (shiftName here) body)]
        else rename relabel (.apply label [.lambda binder body])
    | .apply label [argument] =>
        if label = "ARep" then .apply "LRep" [encode relabel here argument]
        else if label = "AOutName" then .apply "LOutName" [here, rename relabel argument]
        else if label = "AOutCap" then .apply "LOutCap" [here, rename relabel argument]
        else rename relabel (.apply label [argument])
    | .apply label [name, process] =>
        if label = "AAmb" then
          .apply "LNu" [.lambda none (.collection .hashBag
            [.apply "LAmb" [shiftName here, .bvar 0, rename (Nat.succ ∘ relabel) name],
              encode (Nat.succ ∘ relabel) (.bvar 0) process] none)]
        else if label = "AIn" then .apply "LIn" [here, rename relabel name, encode relabel here process]
        else if label = "AOut" then .apply "LOut" [here, rename relabel name, encode relabel here process]
        else if label = "AOpen" then .apply "LOpen" [here, rename relabel name, encode relabel here process]
        else if label = "ACap" then .apply "LCap" [here, rename relabel name, encode relabel here process]
        else rename relabel (.apply label [name, process])
    | .collection .hashBag elements tail => .collection .hashBag (encodeList relabel here elements) tail
    | other => rename relabel other

  /-- The located forms of the members of a bag. -/
  def encodeList (relabel : Nat → Nat) (here : Pattern) : List Pattern → List Pattern
    | [] => []
    | first :: rest => encode relabel here first :: encodeList relabel here rest
end

/-- **The located form of a process at the root**, a location bound outside it: the outermost bound variable, every
free variable of the process moved past it. -/
def located (process : Pattern) : Pattern := encode Nat.succ (.bvar 0) process

end Mettapedia.Languages.ProcessCalculi.Ambient.Encoding
