import Mettapedia.GSLT.LanguageDef.CettaWireTerm
import Lean.Data.Json.Printer

/-! Text transport of physical carrier data. String contents use JSON
escaping, as required by the data reader. Executable MeTTa source rendering
is a separate dialect-dependent operation. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CettaWireData

open CettaWire (Term)

mutual
  def render : Term → String
    | .symbol name => name
    | .string value => (Lean.Json.str value).compress
    | .natural value => toString value
    | .application head arguments => "(" ++ head ++ renderArguments arguments ++ ")"

  def renderArguments : List Term → String
    | [] => ""
    | head :: rest => " " ++ render head ++ renderArguments rest
end

end Mettapedia.GSLT.LanguageDef.CettaWireData
