import Mettapedia.GSLT.Parsing.GrammarConstructorActions

/-! ParserPack constructor actions for the shared source packet format.
Actions preserve selected child positions and order. They construct data;
independent source-certificate replay supplies parsing authority. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.SourcePacketActions

open Mettapedia.GSLT.LanguageDef.CettaWire
open GrammarConstructorActions

def children : List Term → Term
  | [] => .symbol "nil"
  | first :: rest => .application "pair" [first,children rest]

def node (label : String) (values : List Term) : Term :=
  .application "node" [.symbol label,children values]

def childAction : List Nat → Action
  | [] => .constant (.symbol "nil")
  | index :: rest => .apply "pair" [.slot index,childAction rest]

def structural (label : String) (positions : List Nat) : Action :=
  .apply "node" [.constant (.symbol label),childAction positions]

def lexical (label : String) : Action :=
  .apply "node" [.constant (.symbol label),.slot 0]

def entry (position : Nat) : Action := .slot position

theorem children_execute (slots : List Term) (positions : List Nat) :
    (childAction positions).execute slots = (positions.mapM fun index => slots[index]?).map children := by
  induction positions with
  | nil => rfl
  | cons index rest ih =>
      simp only [childAction,Action.execute,executeArguments,ih,List.mapM_cons]
      cases first : slots[index]? <;> cases later : rest.mapM (fun index => slots[index]?) <;> rfl

theorem structural_execute (label : String) (slots : List Term) (positions : List Nat) :
    (structural label positions).execute slots = (positions.mapM fun index => slots[index]?).map (node label) := by
  simp only [structural,Action.execute,executeArguments,children_execute]
  cases positions.mapM (fun index => slots[index]?) <;> rfl

theorem lexical_execute (label : String) (point : Term) (rest : List Term) :
    (lexical label).execute (point :: rest) = some (.application "node" [.symbol label,point]) := rfl

theorem entry_execute (root : Term) (rest : List Term) :
    (entry 0).execute (root :: rest) = some root := rfl

theorem missing_child_refused : (structural "Pair" [0,1]).execute [.symbol "a"] = none := rfl

theorem child_order_retained :
    (structural "Pair" [1,0]).execute [.symbol "a",.symbol "b"] =
      some (node "Pair" [.symbol "b",.symbol "a"]) := rfl

theorem duplicate_child_retained :
    (structural "Pair" [0,0]).execute [.symbol "a"] = some (node "Pair" [.symbol "a",.symbol "a"]) := rfl

end Mettapedia.GSLT.Parsing.SourcePacketActions
