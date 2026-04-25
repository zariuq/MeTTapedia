import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Basic
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

/-!
# Rho calculus bridge to OSLF reduction

This file connects the direct executable rho model in `Basic.lean` with the
existing Pattern/OSLF reduction relation for the subset where both
presentations have the same operational shape.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Basic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

/-!
The executable rho syntax is intentionally direct: communication payloads are
`Data`, while the existing OSLF COMM rule substitutes an `NQuote` of a Pattern
process into a locally nameless Pattern body.  This bridge therefore starts
with the exact common DROP shape.  Extending it to COMM should first define the
payload/body encoding relation explicitly, rather than silently identifying
those two representations.
-/

/-- Names whose executable representation has a direct OSLF Pattern name. -/
inductive EncodesName : Name -> Pattern -> Prop where
  | free (s : String) : EncodesName (Name.free s) (.fvar s)
  | var (n : Nat) : EncodesName (Name.var n) (.bvar n)

/-- Data payloads in the conservative Pattern-shaped subset. -/
inductive EncodesData : Data -> Pattern -> Prop where
  | atom (s : String) : EncodesData (Data.atom s) (.apply "DAtom" [.fvar s])
  | var (n : Nat) : EncodesData (Data.var n) (.bvar n)
  | tuple {ds : List Data} {ps : List Pattern} :
      List.Forall₂ EncodesData ds ps ->
      EncodesData (Data.tuple ds) (.apply "DTuple" ps)
  | name {name : Name} {namePattern : Pattern} :
      EncodesName name namePattern ->
      EncodesData (Data.name name) namePattern

/-- Processes in the conservative OSLF-shaped subset of the executable model. -/
inductive EncodesProc : Proc -> Pattern -> Prop where
  | nil : EncodesProc Proc.nil (.apply "PZero" [])
  | par {ps : List Proc} {qs : List Pattern} :
      List.Forall₂ EncodesProc ps qs ->
      EncodesProc (Proc.par ps) (.collection .hashBag qs none)
  | send {ch : Name} {data : Data} {chPattern dataPattern : Pattern} :
      EncodesName ch chPattern ->
      EncodesData data dataPattern ->
      EncodesProc (Proc.send ch data) (.apply "POutput" [chPattern, dataPattern])
  | quote {p : Proc} {pp : Pattern} :
      EncodesProc p pp ->
      EncodesProc (Proc.quote p) (.apply "NQuote" [pp])
  | drop {p : Proc} {pp : Pattern} :
      EncodesProc p pp ->
      EncodesProc (Proc.drop p) (.apply "PDrop" [pp])

/--
The executable DROP step coincides with the existing OSLF DROP reduction on the
encoded subset.
-/
theorem dropQuoteStep_toReduces
    {p : Proc} {pp : Pattern}
    (_hp : EncodesProc p pp)
    (hstep : Step (Proc.drop (Proc.quote p)) p) :
    Nonempty (Reduces (.apply "PDrop" [.apply "NQuote" [pp]]) pp) := by
  cases hstep
  exact ⟨Reduces.drop⟩

/--
The executable receive-communication constructor and the OSLF COMM rule are
available from the same checked match/substitution premises when the payload,
channel, and post-substitution result are related by the explicit encoding
relations.

The theorem deliberately does not claim a total translation from executable
`Data` substitution to OSLF `NQuote` substitution.  That stronger theorem needs
the payload/body encoding to say when executable data denotes a quoted process
name.  This theorem is the common communication kernel.
-/
theorem recvCommBridge
    {ch : Name} {msg : Data} {pat : Pat} {body result : Proc} {s : Subst}
    {chPattern msgPattern bodyPattern : Pattern}
    (hch : EncodesName ch chPattern)
    (hmsg : EncodesData msg msgPattern)
    (hmatch : matchPat pat msg = some s)
    (hcheck : checkedSubstProc s body = some result)
    (hresult : EncodesProc result (commSubst bodyPattern msgPattern)) :
    Step (Proc.par [Proc.send ch msg, Proc.recv ch pat body]) result /\
      EncodesProc (Proc.send ch msg) (.apply "POutput" [chPattern, msgPattern]) /\
      Nonempty
        (Reduces
          (.collection .hashBag
            [.apply "POutput" [chPattern, msgPattern],
             .apply "PInput" [chPattern, .lambda none bodyPattern]]
            none)
          (.collection .hashBag [commSubst bodyPattern msgPattern] none)) /\
      EncodesProc result (commSubst bodyPattern msgPattern) := by
  exact
    ⟨Step.recvComm hmatch hcheck,
     EncodesProc.send hch hmsg,
     ⟨Reduces.comm⟩,
     hresult⟩

/--
If an executable receive COMM step is already known, the same explicit encoding
premises yield the corresponding OSLF COMM reduction.
-/
theorem recvCommStep_toReduces
    {ch : Name} {msg : Data} {pat : Pat} {body result : Proc}
    {chPattern msgPattern bodyPattern : Pattern}
    (hch : EncodesName ch chPattern)
    (hmsg : EncodesData msg msgPattern)
    (hresult : EncodesProc result (commSubst bodyPattern msgPattern))
    (_hstep : Step (Proc.par [Proc.send ch msg, Proc.recv ch pat body]) result) :
    EncodesProc (Proc.send ch msg) (.apply "POutput" [chPattern, msgPattern]) /\
      Nonempty
        (Reduces
          (.collection .hashBag
            [.apply "POutput" [chPattern, msgPattern],
             .apply "PInput" [chPattern, .lambda none bodyPattern]]
            none)
          (.collection .hashBag [commSubst bodyPattern msgPattern] none)) /\
      EncodesProc result (commSubst bodyPattern msgPattern) := by
  exact ⟨EncodesProc.send hch hmsg, ⟨Reduces.comm⟩, hresult⟩

example :
    Nonempty (Reduces
      (.apply "PDrop" [.apply "NQuote" [.apply "PZero" []]])
      (.apply "PZero" [])) := by
  exact dropQuoteStep_toReduces EncodesProc.nil Step.dropQuote

example :
    EncodesProc (Proc.send (Name.free "ch") (Data.atom "hello"))
        (.apply "POutput" [.fvar "ch", .apply "DAtom" [.fvar "hello"]]) /\
      Nonempty
        (Reduces
          (.collection .hashBag
            [.apply "POutput" [.fvar "ch", .apply "DAtom" [.fvar "hello"]],
             .apply "PInput" [.fvar "ch", .lambda none (.apply "PZero" [])]]
            none)
          (.collection .hashBag [.apply "PZero" []] none)) /\
      EncodesProc Proc.nil (.apply "PZero" []) := by
  simpa [commSubst, openBVar] using (recvCommBridge
    (ch := Name.free "ch")
    (msg := Data.atom "hello")
    (pat := Pat.wild)
    (body := Proc.nil)
    (result := Proc.nil)
    (s := [])
    (chPattern := .fvar "ch")
    (msgPattern := .apply "DAtom" [.fvar "hello"])
    (bodyPattern := .apply "PZero" [])
    (EncodesName.free "ch")
    (EncodesData.atom "hello")
    (by rfl)
    (by simp [checkedSubstProc, substProc, procWF])
    (by
      unfold commSubst openBVar
      exact EncodesProc.nil)).2

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Basic
