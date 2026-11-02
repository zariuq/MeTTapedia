import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangProgramCompilation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldOSLF

/-! Front-door tests of the operational mailbox IR. Expected queue contents
come from the independent list model. Full Core evaluation, channels, fresh
pids and the source-to-IR connection remain separate obligations. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Controls

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.NativeTypes.GeneratedLogic
open Mettapedia.Languages.Erlang

structure Example where
  name : String
  source : Pattern
  expected : Pattern
  wrong : Pattern

def box (saved front rear : List String) : Pattern := mailbox atom ⟨saved, front, rear⟩

def firstClosure : Value := .closure 0 (.lambda 1) []
def capturedClosure : Value := .closure 1 (.lambda 4) [.literal (.integer 7), .pid 3]
def recursiveClosure : Value := .closure 1 (.recursive 17 1) [.tuple [firstClosure, .literal (.atom "captured")]]
def unicodeAtom : Value := .literal (.atom "λ🙂")

def valueBox (source : Mailbox Value) : Pattern := mailbox ErlangCompilation.value source

def payloadExamples : List Example :=
  let empty : Mailbox Value := {}
  let deliver := fun name value => Example.mk name
    (node "ErDeliver" [ErlangCompilation.value value, valueBox empty])
    (node "ErDelivered" [valueBox (empty.deliver value)])
    (node "ErDelivered" [valueBox empty])
  [deliver "deliver-closure" firstClosure,
   deliver "deliver-captured-closure" capturedClosure,
   deliver "deliver-recursive-closure" recursiveClosure,
   deliver "deliver-nested-closures" (.tuple [firstClosure, .cons capturedClosure (.literal .nil)]),
   deliver "deliver-unicode-atom" unicodeAtom,
   ⟨"peek-unicode-rotation", node "ErPeek" [valueBox ⟨[firstClosure], [], [capturedClosure, unicodeAtom]⟩],
     node "ErPeekValue" [ErlangCompilation.value unicodeAtom,
       valueBox (Mailbox.normalize ⟨[firstClosure], [], [capturedClosure, unicodeAtom]⟩)],
     node "ErPeekValue" [ErlangCompilation.value capturedClosure,
       valueBox (Mailbox.normalize ⟨[firstClosure], [], [capturedClosure, unicodeAtom]⟩)]⟩,
   ⟨"peek-closure-rotation", node "ErPeek" [valueBox ⟨[recursiveClosure], [], [capturedClosure, firstClosure]⟩],
     node "ErPeekValue" [ErlangCompilation.value firstClosure,
       valueBox (Mailbox.normalize ⟨[recursiveClosure], [], [capturedClosure, firstClosure]⟩)],
     node "ErPeekValue" [ErlangCompilation.value capturedClosure,
       valueBox (Mailbox.normalize ⟨[recursiveClosure], [], [capturedClosure, firstClosure]⟩)]⟩,
   ⟨"remove-one-closure-duplicate", node "ErRemove" [valueBox ⟨[], [firstClosure, firstClosure], []⟩],
     node "ErRemoved" [valueBox ⟨[], [firstClosure], []⟩], node "ErRemoved" [valueBox empty]⟩,
   ⟨"next-retains-closure", node "ErNext" [valueBox ⟨[recursiveClosure], [firstClosure, capturedClosure], []⟩],
     node "ErAdvanced" [valueBox ⟨[firstClosure, recursiveClosure], [capturedClosure], []⟩],
     node "ErAdvanced" [valueBox ⟨[recursiveClosure], [capturedClosure], []⟩]⟩,
   ⟨"wake-with-closure", node "ErWake" [ErlangCompilation.value capturedClosure, valueBox ⟨[firstClosure], [], []⟩],
     node "ErReady" [valueBox ⟨[firstClosure], [], [capturedClosure]⟩],
     node "ErReady" [valueBox ⟨[], [], [capturedClosure]⟩]⟩]

def examples : List Example := [
  ⟨"peek-first", node "ErPeek" [box [] ["a", "b"] ["c"]],
    node "ErPeekValue" [atom "a", box [] ["a", "b"] ["c"]],
    node "ErPeekValue" [atom "b", box [] ["a", "b"] ["c"]]⟩,
  ⟨"peek-rotation", node "ErPeek" [box ["skipped"] [] ["b", "a"]],
    node "ErPeekValue" [atom "a", mailbox atom (Mailbox.normalize ⟨["skipped"], [], ["b", "a"]⟩)],
    node "ErPeekValue" [atom "b", box ["skipped"] ["b", "a"] []]⟩,
  ⟨"next-retains", node "ErNext" [box ["old"] ["b", "a"] ["c"]],
    node "ErAdvanced" [box ["b", "old"] ["a"] ["c"]],
    node "ErAdvanced" [box ["old"] ["a"] ["c"]]⟩,
  ⟨"remove-restores-prefix", node "ErRemove" [box ["second", "first"] ["a", "later"] ["new"]],
    node "ErRemoved" [box [] ["first", "second", "later"] ["new"]],
    node "ErRemoved" [box [] ["later"] ["new"]]⟩,
  ⟨"remove-one-duplicate", node "ErRemove" [box [] ["a", "a"] []],
    node "ErRemoved" [box [] ["a"] []], node "ErRemoved" [box [] [] []]⟩,
  ⟨"delivery-order", node "ErDeliver" [atom "new", box ["old"] ["a"] ["b"]],
    node "ErDelivered" [mailbox atom ((Mailbox.mk ["old"] ["a"] ["b"]).deliver "new")],
    node "ErDelivered" [box ["old"] ["a"] ["b", "new"]]⟩,
  ⟨"peek-empty-after-scan", node "ErPeek" [box ["b"] [] []],
    node "ErPeekEmpty" [box ["b"] [] []], node "ErPeekValue" [atom "b", box [] ["b"] []]⟩,
  ⟨"wait-retains-prefix", node "ErWait" [box ["b"] [] []],
    node "ErWaiting" [box ["b"] [] []], node "ErWaiting" [box [] [] []]⟩,
  ⟨"incoming-is-ready", node "ErWait" [box ["b"] [] ["a"]],
    node "ErReady" [box ["b"] [] ["a"]], node "ErWaiting" [box ["b"] [] ["a"]]⟩,
  ⟨"wake-retains-prefix", node "ErWake" [atom "a", box ["b"] [] []],
    node "ErReady" [box ["b"] [] ["a"]], node "ErReady" [box [] [] ["a"]]⟩] ++ payloadExamples

def verdicts : List (String × Option Bool × Option Bool) := examples.map fun sample =>
  (sample.name, GoldOSLF.verdict (GoldOSLF.ask language provider 2 16 (GoldOSLF.reaches sample.expected) sample.source),
    GoldOSLF.verdict (GoldOSLF.ask language provider 2 16 (GoldOSLF.reaches sample.wrong) sample.source))

#eval verdicts
#guard verdicts.length == 20
#guard verdicts.all fun entry => entry.2.1 == some true && entry.2.2 == some false

/- A local waiter has no autonomous transition. The external wake operation
does have one. Only the complete actor configuration can decide blockedness. -/
def waitingVerdicts : List (String × Option Bool × Bool) := [
  ("erlang-local-wait-no-autonomous-step", GoldOSLF.verdict (GoldOSLF.ask language provider 2 4 (.possibly .any .top)
    (node "ErWaiting" [box ["b"] [] []])), false),
  ("erlang-explicit-wake", GoldOSLF.verdict (GoldOSLF.ask language provider 2 4 (.possibly .any .top)
    (node "ErWake" [atom "a", box ["b"] [] []])), true)]

#guard waitingVerdicts.all fun entry => entry.2.1 == some entry.2.2

def exhaustedVerdict : Option Bool :=
  let sample := examples[1]'(by decide)
  GoldOSLF.verdict (GoldOSLF.ask language provider 2 0 (GoldOSLF.reaches sample.expected) sample.source)

/- With no search rounds, the rotating mailbox question stays open. The
same question above is proved when the finite region has been explored. -/
#guard exhaustedVerdict == none

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Controls
