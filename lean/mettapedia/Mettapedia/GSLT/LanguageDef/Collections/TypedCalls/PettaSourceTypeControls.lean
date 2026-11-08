import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSourceTypeServices

/-!
# Live declaration and ordered guard controls

Programs here are read and loaded through the source loader. The occurrence
owner uses concrete live-world services, rather than hand-supplied call rows
or guard answers. Whole runs are executable checks; theorem declarations
below are independently kernel checked.
-/

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSourceTypeControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open PettaOccurrenceOverlay (State Row RowLookup)
open PettaSourceTypeRows (declaration typeAtom)

def num (n : Int) : Atom := .grounded (.int n)
def sym (name : String) : Atom := .symbol name
def call (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)

def world (rows : List Atom) : EagerDFS.World := ⟨NamedSpaces.Store.new rows [], [], []⟩

def start (program : SpaceSemantics.Program) (query : Atom) : State Unit :=
  (Allocator.empty 8 256, ⟨⟨Effects.loaded program, [], []⟩,
    [{frontier := [(⟨[], [.evaluate query (.var "result")], .var "result", ∅, 0⟩, ⟨(), []⟩, [])]}]⟩)

def runText (source : String) (query : Atom) (budget : Nat := 400) : Option (List Atom × List Atom) := do
  let forms ← (SpaceSemantics.readSource source).toOption
  let program ← (SpaceSemantics.collect forms).toOption
  let run := (PettaOccurrenceOverlay.machine (PettaSourceTypeServices.services []) .eagerValue program).run
    budget (start program query)
  match run.2 with
  | .finished final => some (run.1.map (·.value), final.2.world.output)
  | _ => none

def identitySource : String :=
  "(: ident (-> $t $t))\n(= (ident $x) $x)"

#guard runText identitySource (call "ident" [num 7]) == some ([num 7], [])

#guard runText (identitySource ++ "\n(: ident (-> $u $u))") (call "ident" [num 7]) ==
  some ([num 7], [])

def badSource : String :=
  "(: bad (-> $t $t))\n(= (bad $x) (let $ignored (println! body) \"wrong\"))"

#guard runText badSource (call "bad" [num 7]) == some ([], [sym "body"])

def taggedSource : String :=
  identitySource ++ "\n(: tag First)\n(: tag Second)"

#guard runText taggedSource (call "ident" [sym "tag"]) == some ([sym "tag", sym "tag"], [])

def rawSource : String := "(: hold (-> Atom Atom))\n(= (hold $x) $x)"

#guard runText rawSource (call "hold" [call "println!" [sym "must-not-run"]]) ==
  some ([call "println!" [sym "must-not-run"]], [])

def recursiveSource : String :=
  "(: down (-> Number Number))\n(= (down $n) (if (== $n 0) 0 (down (- $n 1))))"

#guard runText recursiveSource (call "down" [num 3]) 700 == some ([num 0], [])

def listSource : String :=
  "(: Cons (-> $a (List $a) (List $a)))\n(: Nil (List $a))\n(: keep (-> (List $a) (List $a)))\n(= (keep $x) $x)"

def numericList : Atom := call "Cons" [num 1, sym "Nil"]
def mixedList : Atom := call "Cons" [num 1, call "Cons" [.grounded (.string "bad"), sym "Nil"]]

#guard runText listSource (call "keep" [numericList]) == some ([numericList], [])
#guard runText listSource (call "keep" [mixedList]) == some ([], [])

def tagWorld : EagerDFS.World := world
  [declaration "tag" (.sym "First"), declaration "tag" (.sym "Second")]

local instance : DecidableEq (Eqn CallVar) :=
  fun first second =>
    match Ty.decEq first.1 second.1, Ty.decEq first.2 second.2 with
    | isTrue left, isTrue right => isTrue (Prod.ext left right)
    | isFalse different, _ => isFalse fun same => different (congrArg Prod.fst same)
    | _, isFalse different => isFalse fun same => different (congrArg Prod.snd same)

#guard decide (PettaSourceTypeServices.orderedGuard [] tagWorld 0 [] (.var "t") (sym "tag") =
  some [[(.sym "First", .var (.inl "t"))], [(.sym "Second", .var (.inl "t"))]])

def repeatedTagWorld : EagerDFS.World := world
  [declaration "tag" (.sym "First"), declaration "tag" (.sym "First"), declaration "tag" (.sym "Second")]

#guard decide (PettaSourceTypeServices.orderedGuard [] repeatedTagWorld 0 [] (.var "t") (sym "tag") =
  PettaSourceTypeServices.orderedGuard [] tagWorld 0 [] (.var "t") (sym "tag"))

#guard decide (PettaSourceTypeServices.orderedGuard [] tagWorld 0 [] (.var "t") (sym "tag") ≠
  some [[(.sym "Second", .var (.inl "t"))], [(.sym "First", .var (.inl "t"))]])

#guard decide (PettaSourceTypeServices.orderedGuard [] tagWorld 0 [] (.sym "Number") (sym "tag") = some [])

#guard decide (PettaSourceTypeServices.orderedGuard [] (world []) 0 [] (.sym "Symbol") (sym "bare") =
  some [[(.sym "Symbol", .sym "Symbol")]])

def opaqueTypeWorld : EagerDFS.World := world [call ":" [sym "f", num 7]]
def expressionSubjectWorld : EagerDFS.World := world [call ":" [call "f" [.var "x"], sym "Number"]]

theorem unsupported_type_is_not_absent :
    PettaSourceTypeRows.lookup [] opaqueTypeWorld "f" [] = .unserved := by rfl

theorem expression_annotation_needs_other_profile :
    PettaSourceTypeRows.lookup [] expressionSubjectWorld "f" [] = .unserved := by rfl

def identityRow : Row := ⟨[.var "t"], .var "t"⟩
def identityWorld : EagerDFS.World := world [declaration "ident" identityRow.asType]

theorem one_row_shares_parameter_and_range_variable :
    PettaSourceTypeRows.lookup [] identityWorld "ident" [num 7] = .typed [identityRow] := by
  apply PettaSourceTypeRows.lookup_written_rows
  · simp
  · rfl
  · rfl

theorem unsupported_guard_is_retained :
    PettaSourceTypeServices.orderedGuard [] opaqueTypeWorld 0 [] (.sym "Number") (num 1) = none := by
  apply PettaSourceTypeServices.unsupported_source_retained
  decide

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSourceTypeControls
