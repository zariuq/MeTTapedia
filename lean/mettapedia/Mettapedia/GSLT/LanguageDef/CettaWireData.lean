import Mettapedia.GSLT.LanguageDef.CettaWireTerm
import Mettapedia.Languages.MeTTa.PeTTa.StringLiteral
import Lean.Data.Json.Printer

/-! Text transport of physical carrier data. A string is written in the
canonical spelling of module text: the quote and the backslash escaped,
newline, carriage return and tab as named escapes, other controls and DEL as
`\xhh` with lowercase digits, and every other character as itself. Writers choose this spelling; readers also accept other lossless spellings.
The data reader decodes
it back to the string (`decodeBody_canonicalBody`). Executable MeTTa source
rendering is a separate dialect-dependent operation. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CettaWireData

open CettaWire (Term)
open Mettapedia.Languages.MeTTa.PeTTa.StringLiteral (canonicalBody decodeBody_canonicalBody)

/-! ## Terms -/

mutual
  def render : Term → String
    | .symbol name => name
    | .string value => String.ofList ('"' :: canonicalBody value.toList ++ ['"'])
    | .natural value => toString value
    | .application head arguments => "(" ++ head ++ renderArguments arguments ++ ")"

  def renderArguments : List Term → String
    | [] => ""
    | head :: rest => " " ++ render head ++ renderArguments rest
end

#print axioms decodeBody_canonicalBody

end Mettapedia.GSLT.LanguageDef.CettaWireData
