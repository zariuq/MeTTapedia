import Mettapedia.Logic.Prolog.ReaderProfile
import Mettapedia.Logic.Prolog.ReaderDirective

/-! Read-time profile transitions. Parsed directives remain source forms;
only their declared reader effects update the next sentence's environment.
Import resolution is explicit and is never delegated to the host implicitly. -/

namespace Mettapedia.Logic.Prolog.ReaderProfileState

open ReaderProfile SourceSignature

def noImports : ReaderDirective.ImportProfile String := fun _ =>
  .error "source import needs an explicit operator-profile resolver"

private def textMode? : SourceSignature.Term → Option QuotedText
  | .const (.atom "atom") => some .atom | .const (.atom "chars") => some .chars
  | .const (.atom "codes") => some .codes | .const (.atom "string") => some .string
  | _ => none

private def flags (profile : Profile) : SourceSignature.Goal → Except String Profile
  | .conj left right => do flags (← flags profile left) right
  | .call call =>
      if call.symbol.name != "set_prolog_flag" then .ok profile else
      match List.ofFn call.args with
      | [.const (.atom name), value] =>
          if name == "double_quotes" || name == "back_quotes" then do
            let some mode := textMode? value | .error "invalid quoted-text interpretation"
            if profile.dialect == .iso && (name == "back_quotes" || mode == .string) then
              .error "quoted-text flag is outside the ISO profile"
            else if name == "double_quotes" then .ok {profile with doubleQuotes := mode}
            else .ok {profile with backQuotes := some mode}
          else if ["character_escapes", "char_conversion", "var_prefix"].contains name then
            .error "this lexical flag requires a separately qualified lexer profile"
          else .ok profile
      | _ => .error "malformed source reader flag"
  | _ => .ok profile

def advance (imports : ReaderDirective.ImportProfile String) (profile : Profile)
    (form : ReaderSource.Form) : Except String Profile := do
  let operators ← (ReaderDirective.effectWithLists profile.lists imports form profile.operators).mapError
    (fun _ => "invalid or unresolved source operator directive")
  let next := {profile with operators}
  match form with
  | .directive goal => flags next goal
  | _ => .ok next

structure Sentence where
  text : String
  before : Profile
  reading : ReaderTerm.Result
  form : ReaderSource.Form
  after : Profile

/-- Segmentation/reference reading is separate from grammar-derived parsing.
The native syntax pipeline checks each retained sentence under `before`. -/
def readSource (imports : ReaderDirective.ImportProfile String) :
    Nat → Profile → String → Except String (List Sentence × Profile)
  | 0, _, _ => .error "source sentence budget exhausted"
  | fuel + 1, profile, input => do
      let tokens ← (ReaderLexer.scan input).mapError (fun e => reprStr e)
      if tokens.isEmpty then pure ([],profile) else do
        let reading ← (ReaderTerm.parseOneWith profile profile.operators tokens).mapError (fun e => reprStr e)
        let form ← (ReaderSource.classify reading.term).mapError (fun e => reprStr e)
        let after ← advance imports profile form
        let stop := reading.remaining.head?.map (·.span.start.offset) |>.getD input.toList.length
        let sentence := String.ofList (input.toList.take stop)
        let remaining := String.ofList (input.toList.drop stop)
        let (sentences, final) ← readSource imports fuel after remaining
        pure (⟨sentence,profile,reading,form,after⟩ :: sentences, final)

theorem advance_clause (imports : ReaderDirective.ImportProfile String) (profile : Profile)
    (clause : SourceSignature.Clause) : advance imports profile (.clause clause) = .ok profile := rfl

end Mettapedia.Logic.Prolog.ReaderProfileState
