import Mettapedia.GSLT.LanguageDef.FirstOrderPremiseSearch
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer

/-! Application-only certificate interchange. This explicit data adapter is
not an adequacy theorem for a textual source language. The admitted calculus
and the generic checker determine authority independently of these records. -/

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.FirstOrderCertificateData

open Lean (Json toJson)
open Mettapedia.OSLF.MeTTaIL.Syntax
open FirstOrderRules InferenceChecker FirstOrderPremiseSearch

def field (value : Json) (name : String) : Except String Json := value.getObjVal? name
def stringField (value : Json) (name : String) : Except String String := do (← field value name).getStr?
def arrayField (value : Json) (name : String) : Except String (Array Json) := do (← field value name).getArr?

partial def pattern (value : Json) (metavariables : Bool := false) : Except String Pattern := do
  if let .ok name := stringField value "var" then
    unless metavariables do throw "a ground argument cannot contain a metavariable"
    return .fvar name
  let values ← value.getArr?
  unless values.size = 2 do throw "expected [head, arguments]"
  return .apply (← values[0]!.getStr?)
    ((← (← values[1]!.getArr?).mapM (fun child => pattern child metavariables)).toList)

partial def patternJson : Pattern → Except String Json
  | .apply head arguments => return .arr #[.str head, .arr (← arguments.toArray.mapM patternJson)]
  | .fvar name => return Json.mkObj [("var", .str name)]
  | _ => .error "outside the application-only certificate fragment"

def rule (value : Json) : Except String FORule := do
  return ⟨← stringField value "id", (← (← arrayField value "vars").mapM Json.getStr?).toList,
    (← (← arrayField value "premises").mapM (fun premise => pattern premise true)).toList,
    ← pattern (← field value "conclusion") true⟩

partial def seed (value : Json) : Except String (Option Seed) := do
  if let .null := value then return none
  let name ← stringField value "rule"
  let arguments ← (← arrayField value "arguments").mapM (fun argument => pattern argument false)
  let children ← (← arrayField value "children").mapM seed
  return some (.node name arguments.toList children.toList)

partial def article (value : Json) : Except String RawProof := do
  let name ← stringField value "rule"
  let arguments ← (← arrayField value "arguments").mapM (fun argument => pattern argument false)
  let children ← (← arrayField value "children").mapM article
  return .node ⟨⟨name⟩, arguments.toList⟩ children.toList

partial def articleJson : RawProof → Except String Json
  | .node application children => return Json.mkObj [
      ("rule", .str application.ruleId.value),
      ("arguments", .arr (← application.arguments.toArray.mapM patternJson)),
      ("children", .arr (← children.toArray.mapM articleJson))]

def reportJson (name : String) (goal : Pattern) (report : Report) : Except String Json := do
  let status : List (String × Json) ← match report.outcome with
    | .candidate proof => (articleJson proof).map fun encoded =>
        [("status", Json.str "candidate"), ("article", encoded)]
    | .noCandidate => pure [("status", .str "no-candidate")]
    | .exhausted reason => pure [("status", .str "budget-exhausted"), ("limit", .str reason)]
    | .fault reason => pure [("status", .str "fault"), ("reason", .str reason)]
  return Json.mkObj (status ++ [("name", .str name), ("goal", ← patternJson goal),
    ("steps", toJson report.steps), ("attempts", toJson report.attempts)])

def unwrap {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)

end Mettapedia.GSLT.LanguageDef.FirstOrderCertificateData
