import Mettapedia.Languages.MeTTa.PeTTa.StableIntrinsicTypeQuery

/-! Shared-alias and query-policy controls for the corrected stable boundary. -/

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000

namespace Mettapedia.Languages.MeTTa.PeTTa.StableIntrinsicTypeQuery.Controls

open Mettapedia.Logic.LP
open IntrinsicTypeFacts (TypeTerm Declaration named undefinedType)
open IndependentTypeOutput (Result row matched freshSupply callerName)

def library : List Declaration := [⟨0, .symbol "Number", named "Type"⟩]
def subject : TypeTerm := row [.const (.number "1"), .var (callerName 0)]
def required : TypeTerm := row [.var (callerName 0), named "String"]

def fieldNames : TypeTerm → Option (List String)
  | .app _ fields =>
      (List.ofFn fields).mapM fun field => match field with
        | .const (.symbol name) => some name
        | _ => none
  | _ => none

def observations (result : Result) : Option (List (Option (List String))) :=
  result.map (List.map fieldNames)

theorem shared_subject_is_rejected :
    run library freshSupply 3 [] subject (some required) = some [] := by
  cbv

theorem fresh_then_late_match_is_different :
    observations ((run library freshSupply 3 [] subject none).map (matched required)) =
      some [some ["Number", "String"]] := by
  cbv

theorem number_has_no_undefined_answer :
    run [] freshSupply 1 [] (.const (.number "1")) (some undefinedType) = some [] := by
  cbv

theorem undeclared_symbol_has_undefined_answer :
    run [] freshSupply 1 [] (named "unregistered") (some undefinedType) = some [undefinedType] := by
  cbv

theorem incomplete_query_is_not_empty :
    run [] freshSupply 0 [] (.const (.number "1")) (some undefinedType) = none := rfl

theorem root_alias_requirement_still_uses_fresh_mode :
    run library freshSupply 3 [] subject (some (.var (callerName 0))) =
      run library freshSupply 3 [] subject none := rfl

def variableDomainLibrary : List Declaration :=
  [⟨0, .symbol "V", row [named "->", .var 0, .var 0]⟩]

theorem instantiated_undefined_does_not_remove_domain_guard :
    run variableDomainLibrary freshSupply 3 []
      (row [named "V", .const (.number "1")]) (some undefinedType) = some [] := by cbv

def uncheckedDomainLibrary : List Declaration :=
  [⟨0, .symbol "U", row [named "->", undefinedType, named "Tag"]⟩]

theorem literal_undefined_domain_skips_its_query :
    run uncheckedDomainLibrary freshSupply 1 []
      (row [named "U", .const (.number "1")]) (some (named "Tag")) = some [named "Tag"] := by cbv

end Mettapedia.Languages.MeTTa.PeTTa.StableIntrinsicTypeQuery.Controls
