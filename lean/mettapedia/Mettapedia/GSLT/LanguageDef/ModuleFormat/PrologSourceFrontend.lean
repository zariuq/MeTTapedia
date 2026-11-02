import Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologSourceLowering
import Mettapedia.GSLT.LanguageDef.ModuleFormat.RetainedSourceLowering
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxIO
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketSelection
import Mettapedia.Logic.LP.TermEquality

/-! Prolog uses the same independently checked source boundary as Datalog
and the other Gold frontends. Source syntax is retained beside the LP term;
execution and Datalog admission remain downstream. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologSourceFrontend

open Mettapedia.Logic.Prolog ReaderProfile
open ScalarSyntaxCore RetainedSourceLowering
open Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter (stringScalars)

def description (profile : Profile) := SourceSyntaxIO.description (PrologSyntax.description profile)

/-- Constructor interpretation and the independent operator reader must
agree before an LP term leaves this frontend. This check does not establish
that either reader covers all syntax of the external dialect. -/
def checkedLower (profile : Profile) (input : String) (packet : SourcePacket.Packet) :
    Except String ReaderTerm.Result := do
  let result ← PrologSourceLowering.lower profile input packet
  let reference ← (ReaderTerm.readOneWith profile profile.operators input).mapError
    (fun _ => "source is outside the independent reference-reader profile")
  if result.term = reference.term ∧ result.bindings = reference.bindings then pure result
  else .error "source constructor and reference interpretations disagree"

theorem checkedLower_agrees {profile : Profile} {input : String} {packet : SourcePacket.Packet}
    {result : ReaderTerm.Result} (accepted : checkedLower profile input packet = .ok result) :
    ∃ reference, ReaderTerm.readOneWith profile profile.operators input = .ok reference ∧
      result.term = reference.term ∧ result.bindings = reference.bindings := by
  unfold checkedLower at accepted
  cases lowered : PrologSourceLowering.lower profile input packet with
  | error reason => simp [lowered, bind, Except.bind] at accepted
  | ok value =>
      cases read : ReaderTerm.readOneWith profile profile.operators input with
      | error reason => simp [lowered, read, bind, Except.bind, Except.mapError] at accepted
      | ok reference =>
          simp only [lowered, read, Except.mapError, bind, Except.bind] at accepted
          split at accepted
          next same =>
            cases Except.ok.inj accepted
            exact ⟨reference,rfl,same⟩
          next => cases accepted

def read (profile : Profile) (input : String) (packet : SourcePacket.Packet) :
    Except String (Retained ReaderTerm.Result) :=
  match admit? (description profile) with
  | none => .error "source grammar does not meet the shared reader admission conditions"
  | some admitted =>
    lower (description profile) admitted.parser admitted.shape (fun text tree => do
      let some reading := SourcePacketCertificate.readPacket? (description profile)
        admitted.parser admitted.shape (stringScalars text) "PlSentence" tree
        | .error "source certificate replay failed"
      unless SourcePacketSelection.selected
          (SourcePacketSelection.allows (PrologSyntax.selection profile) (stringScalars text))
          "PlSentence" reading.certificate do .error "source lexical selection failed"
      checkedLower profile text tree) input packet

theorem read_prints {profile : Profile} {input : String} {packet : SourcePacket.Packet}
    {result : Retained ReaderTerm.Result} (accepted : read profile input packet = .ok result) :
    printText? (description profile) "PlSentence" result.sourceCore = some input := by
  unfold read at accepted
  cases admitted : admit? (description profile) with
  | none => simp [admitted] at accepted
  | some witness =>
      simp only [admitted] at accepted
      exact lower_prints accepted

/-- Several syntax derivations may denote one sentence. Retain all their
syntax cores while exposing one LP interpretation; never concatenate parse
alternatives into extra clauses. Forest completeness is checked separately. -/
structure Alternatives where
  sourceCores : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
  lowered : ReaderTerm.Result

def readAlternatives (profile : Profile) (input : String) (packets : List SourcePacket.Packet) :
    Except String Alternatives := do
  let readings ← packets.mapM (read profile input)
  let first :: rest := readings | .error "no retained source alternative"
  unless rest.all (fun r => decide (r.lowered.term = first.lowered.term ∧
      r.lowered.bindings = first.lowered.bindings)) do
    .error "retained source alternatives have different interpretations"
  pure ⟨readings.map (·.sourceCore), first.lowered⟩

end Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologSourceFrontend
