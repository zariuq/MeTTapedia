import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacket
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Portable

/-! Grammar-aware access to retained source packets. Field erasure is an
explicit interpretation policy; it does not change the packet or certify an
IR. Binding, literal interpretation and runtime admission remain downstream. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketView

open Mettapedia.OSLF.MeTTaIL.Syntax SourcePacket

def requireSome {α : Type} (message : String) : Option α → Except String α
  | some value => .ok value
  | none => .error message

/-- Keep the parameter with its value until all field policies are applied. -/
def select (keep : TermParam → Bool) (fields : List (Packet × TermParam)) :=
  fields.filter (fun field => keep field.2)

theorem select_append (keep : TermParam → Bool) (left right : List (Packet × TermParam)) :
    select keep (left ++ right) = select keep left ++ select keep right := by
  simp only [select, List.filter_append]

theorem select_comp (first second : TermParam → Bool) (fields : List (Packet × TermParam)) :
    select second (select first fields) = select (fun p => first p && second p) fields := by
  simp only [select, List.filter_filter, Bool.and_comm]

theorem select_sublist (keep : TermParam → Bool) (fields : List (Packet × TermParam)) :
    (select keep fields).Sublist fields := List.filter_sublist

def fields (keep : TermParam → Bool) (children : List Packet) (parameters : List TermParam) : List Packet :=
  (children.zip parameters).filterMap fun (child, parameter) => if keep parameter then some child else none

theorem fields_eq_select (keep : TermParam → Bool) (children : List Packet) (parameters : List TermParam) :
    fields keep children parameters = (select keep (children.zip parameters)).map Prod.fst := by
  unfold fields select
  induction children.zip parameters with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨child, parameter⟩
      cases h : keep parameter <;> simp [h, ih]

def text (description : Except String Portable.SyntaxDescription) (sort : String)
    (source : Packet) : Except String String := do
  let grammar ← description
  requireSome s!"invalid {sort} packet" (readback? grammar.grammar grammar.profile sort source)

/-- This is a projection of one already retained tree, not parse selection.
The enclosing source reader checks the complete grammar and input. -/
def view (description : Except String Portable.SyntaxDescription) (keep : TermParam → Bool)
    (source : Packet) : Except String (String × List Packet) := do
  let (label, children) ← requireSome "malformed source node" (node? source)
  let grammar ← description
  let row ← requireSome s!"unknown production {label}" (grammar.grammar.terms.find? (·.label == label))
  unless children.length == row.params.length do .error s!"wrong child count for {label}"
  pure (label, fields keep children row.params)

def series (view : Packet → Except String (String × List Packet)) (family : String) :
    Nat → Packet → Except String (List Packet)
  | 0, _ => .error "source sequence exceeds its packet size"
  | fuel + 1, source => do
      let (label, fields) ← view source
      match fields with
      | [] => if label == family ++ "-empty" then pure [] else .error s!"malformed sequence {label}"
      | [first] => if label == family ++ "-one" then pure [first] else .error s!"malformed sequence {label}"
      | [first, rest] => if label == family ++ "-more" then
          (first :: ·) <$> series view family fuel rest else .error s!"malformed sequence {label}"
      | _ => .error s!"malformed sequence {label}"

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketView
