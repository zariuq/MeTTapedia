import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CettaWireAtom

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CettaWireAtom

open Mettapedia.GSLT.LanguageDef.CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

mutual
  def decode? : Atom → Option Term
    | .symbol name => some (.symbol name)
    | .grounded (.string value) => some (.string value)
    | .grounded (.int value) => if value < 0 then none else some (.natural value.toNat)
    -- The source reader recognizes wire truth tokens as host Booleans.
    | .grounded (.bool value) => some (.symbol (if value then "True" else "False"))
    | .expression (.symbol head :: arguments) => Term.application head <$> decodeMany? arguments
    | _ => none
  def decodeMany? : List Atom → Option (List Term)
    | [] => some []
    | atom :: rest => do pure ((← decode? atom) :: (← decodeMany? rest))
end

mutual
  @[simp] theorem decode?_encode (term : Term) : decode? (encode term) = some term := by
    cases term with
    | symbol _ => rfl
    | string _ => rfl
    | natural value => simp [decode?,encode]
    | application head arguments =>
      change (decodeMany? (encodeMany arguments)).map (Term.application head) = _
      rw [decodeMany?_encodeMany]
      rfl
  @[simp] theorem decodeMany?_encodeMany (terms : List Term) : decodeMany? (encodeMany terms) = some terms := by
    cases terms with
    | nil => rfl
    | cons head tail =>
      change (do pure ((← decode? (encode head)) :: (← decodeMany? (encodeMany tail)))) = _
      rw [decode?_encode,decodeMany?_encodeMany]
      rfl
end

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CettaWireAtom
