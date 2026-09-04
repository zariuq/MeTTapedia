import Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionVerifier

namespace Mettapedia.OSLF.Tools.ExportTptpOfficialGroundResolutionCanary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionVerifier

private def quote (value : String) : String :=
  "\"" ++ (value.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""

private def carrierFor? (language : LanguageDef) (expected : TypeExpr) :
    Option CarrierKind := do
  let .base sort := expected | none
  let declaration <- language.types.find? (fun declaration => declaration.name == sort)
  some declaration.carrier

mutual
  /-- Render a checked first-order carrier term while preserving the difference
  between nullary constructors and builtin values.  `Pattern` deliberately
  represents both with `apply _ []`; the expected sort from the supplied
  `LanguageDef` is therefore essential to faithful MeTTa serialization. -/
  private def renderTyped? (language : LanguageDef) :
      Pattern -> TypeExpr -> Option String
    | .apply head [], expected =>
        match carrierFor? language expected with
        | some .builtinString => some (quote head)
        | some .builtinInt => if head.toInt?.isSome then some head else none
        | some .builtinBool =>
            if head == "True" || head == "False" then some head else none
        | _ =>
            match expected with
            | .base category =>
                if language.terms.any fun rule =>
                    rule.label == head && rule.category == category &&
                      rule.params.isEmpty
                then some s!"({head})"
                else none
            | _ => none
    | .apply head arguments, expected => do
        let .base category := expected | none
        let rule <- language.terms.find? fun rule =>
          rule.label == head && rule.category == category &&
            rule.params.length == arguments.length
        let rendered <- renderArguments? language arguments rule.params
        some ("(" ++ head ++ " " ++ String.intercalate " " rendered ++ ")")
    | _, _ => none

  private def renderArguments? (language : LanguageDef) :
      List Pattern -> List TermParam -> Option (List String)
    | [], [] => some []
    | argument :: arguments, parameter :: parameters => do
        let expected <- parameterType? parameter
        let first <- renderTyped? language argument expected
        let rest <- renderArguments? language arguments parameters
        some (first :: rest)
    | _, _ => none
end

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [path] =>
      match renderTyped? TptpOfficialSemanticCarrier.language Canary.valid
          (.base "TptpSemantic:derivation") with
      | some rendered =>
          IO.FS.writeFile path (rendered ++ "\n")
          pure 0
      | none =>
          IO.eprintln "the official ground-resolution canary is not serializable"
          pure 1
  | _ =>
      IO.eprintln
        "usage: export-tptp-official-ground-resolution-canary <output>"
      pure 2

end Mettapedia.OSLF.Tools.ExportTptpOfficialGroundResolutionCanary

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.OSLF.Tools.ExportTptpOfficialGroundResolutionCanary.main arguments
