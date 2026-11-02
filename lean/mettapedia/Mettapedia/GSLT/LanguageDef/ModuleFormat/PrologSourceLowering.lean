import Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologSyntaxModule
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketView
import Mettapedia.Logic.Prolog.ReaderTerm

/-! Interpret retained Prolog syntax into the existing LP term carrier.
Variable interning is shared with the independent reference reader. Syntax
readback, lexical interpretation, operator interpretation and clause/control
classification remain separate operations. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologSourceLowering

open Mettapedia.Logic.Prolog ReaderProfile ReaderOperator
open SourcePacket SourcePacketView
abbrev Lower := Except String

def keepField : Mettapedia.OSLF.MeTTaIL.Syntax.TermParam → Bool
  | .simple _ (.base "PlLayout") => false
  | _ => true

def view (profile : Profile) := SourcePacketView.view (.ok (PrologSyntax.description profile)) keepField
def text (profile : Profile) := SourcePacketView.text (.ok (PrologSyntax.description profile))

private def literal (profile : Profile) (spelling : String) : Lower SourceSignature.Term :=
  match ReaderTerm.readOneWith profile profile.operators (spelling ++ " .") with
  | .ok result => .ok result.term
  | .error error => .error s!"invalid source literal: {reprStr error}"

private def atomName (profile : Profile) (packet : Packet) : Lower String := do
  let .const (.atom name) ← literal profile (← text profile "PlAtom" packet)
    | .error "expected an atom"
  pure name

mutual
  def term (profile : Profile) : Nat → Packet → ReaderTerm.State → Lower (SourceSignature.Term × ReaderTerm.State)
    | 0, _, _ => .error "source term exceeds its packet size"
    | fuel + 1, source, state => do
      let (label, fields) ← view profile source
      if label.startsWith "pl:level:" then
        let [child] := fields | .error "malformed precedence lift"
        term profile fuel child state
      else if label.startsWith "pl:apply:" then
        let index ← requireSome "invalid operator occurrence" ((label.drop 9).toString.toNat?)
        let op ← requireSome "missing operator occurrence" profile.operators[index]?
        let operands ← match op.specifier, fields with
          | .fx, [_,right] | .fy, [_,right] => pure [right]
          | .xf, [left,_] | .yf, [left,_] => pure [left]
          | .xfx, [left,_,right] | .xfy, [left,_,right] | .yfx, [left,_,right] => pure [left,right]
          | _, _ => .error "operator arity disagrees with its declaration"
        let (values, after) ← terms profile fuel operands state
        let spelling ← text profile (PrologSyntax.exprSort op.priority.value) source
        if op.name == "-" && op.specifier.isPrefix &&
            spelling.toList[1]?.any Char.isDigit then
          pure (← literal profile spelling, after)
        else pure (SourceSignature.compound op.name values, after)
      else match label, fields with
        | "pl:term-variable", [name] =>
            let spelling ← text profile "PlVariableName" name
            let (identity, after) := ReaderTerm.internVariable spelling state
            pure (.var identity, after)
        | "pl:term-atom", [name] => pure (SourceSignature.atom (← atomName profile name), state)
        | "pl:term-number", [_] | "pl:term-negative", [_]
        | "pl:term-text", [_] | "pl:term-backtext", [_] =>
            pure (← literal profile (← text profile "PlExpr0" source), state)
        | "pl:term-parens", [child] => term profile fuel child state
        | "pl:term-compound", [name,args] =>
            let name ← atomName profile name
            let (values, after) ← arguments profile fuel args state
            pure (SourceSignature.compound name values, after)
        | "pl:term-zero-arity", [name] =>
            if profile.zeroArityCompounds then pure (SourceSignature.compound (← atomName profile name) [],state)
            else .error "zero-argument compounds are outside the selected profile"
        | "pl:term-nil", [] => pure (profile.nil,state)
        | "pl:term-list", [args] =>
            let (values, after) ← arguments profile fuel args state
            pure (profile.list values,after)
        | "pl:term-list-tail", [args,tail] =>
            let (values, after) ← arguments profile fuel args state
            let (tail, after) ← term profile fuel tail after
            pure (profile.list values tail,after)
        | "pl:term-braces-empty", [] => pure (SourceSignature.atom "{}",state)
        | "pl:term-braces", [body] =>
            let (body,after) ← term profile fuel body state
            pure (SourceSignature.compound "{}" [body],after)
        | _, _ => .error s!"invalid source term constructor {label}"

  def arguments (profile : Profile) : Nat → Packet → ReaderTerm.State → Lower (List SourceSignature.Term × ReaderTerm.State)
    | 0, _, _ => .error "source arguments exceed their packet size"
    | fuel + 1, source, state => do
      match ← view profile source with
      | ("pl:arguments-one",[child]) =>
          let (value,after) ← term profile fuel child state
          pure ([value],after)
      | ("pl:arguments-more",[child,rest]) =>
          let (value,after) ← term profile fuel child state
          let (values,after) ← arguments profile fuel rest after
          pure (value::values,after)
      | _ => .error "invalid argument list"

  def terms (profile : Profile) : Nat → List Packet → ReaderTerm.State → Lower (List SourceSignature.Term × ReaderTerm.State)
    | _, [], state => pure ([],state)
    | 0, _::_, _ => .error "source operands exceed their packet size"
    | fuel + 1, first::rest, state => do
        let (value,after) ← term profile fuel first state
        let (values,after) ← terms profile fuel rest after
        pure (value::values,after)
end

def lower (profile : Profile) (input : String) (packet : Packet) : Lower ReaderTerm.Result := do
  let spec := PrologSyntax.description profile
  unless SourcePacket.validates spec.grammar spec.profile "PlSentence" input packet do
    .error "source packet does not read back to the complete sentence"
  let ("pl:sentence",[body]) ← view profile packet | .error "expected a sentence packet"
  let (value,state) ← term profile (packetNodes packet + 1) body {remaining := []}
  pure ⟨value,state.bindings.reverse,[]⟩

end Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologSourceLowering
