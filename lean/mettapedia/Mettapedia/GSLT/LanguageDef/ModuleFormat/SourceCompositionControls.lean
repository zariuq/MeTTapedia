import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketView
import Mettapedia.GSLT.LanguageDef.ModuleFormat.RetainedSourceLowering

/-! Source retention and field-projection controls. Equal runtime values do
not identify source spellings; field policies preserve order and occurrences. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCompositionControls

open Mettapedia.OSLF.MeTTaIL.Syntax SourcePacketView RetainedSourceLowering

private def keepData : TermParam → Bool
  | .simple _ (.base "Trivia") => false
  | _ => true

private def keepUnannotated : TermParam → Bool
  | .simple _ (.base "Annotation") => false
  | _ => true

private def rows : List (SourcePacket.Packet × TermParam) :=
  [(.symbol "a", .simple "first" (.base "Value")),
   (.symbol " ", .simple "space" (.base "Trivia")),
   (.symbol "a", .simple "second" (.base "Value")),
   (.symbol "note", .simple "annotation" (.base "Annotation"))]

example : (select keepUnannotated (select keepData rows)).map Prod.fst =
    [.symbol "a", .symbol "a"] := rfl

example : select keepUnannotated (select keepData rows) =
    select (fun p => keepData p && keepUnannotated p) rows := select_comp _ _ _

/-- A binder body is not trivia merely because its result sort has that name. -/
example : keepData (.abstraction "body" (.base "Trivia")) = true := rfl

private def syntaxA : Pattern := .apply "decimal-spelling" [.apply "007" []]
private def syntaxB : Pattern := .apply "decimal-spelling" [.apply "7" []]
private def first : Nat → Except String Nat := fun n => .ok (n % 10)
private def second : Nat → Except String Nat := fun n => .ok (n + 1)

example : continueWith second (continueWith first (.ok ⟨syntaxA, 17⟩)) =
    .ok ⟨syntaxA, 8⟩ := rfl

example : continueWith second (continueWith first (.ok ⟨syntaxA, 17⟩)) =
    continueWith (fun n => (first n).bind second) (.ok ⟨syntaxA, 17⟩) :=
  continueWith_comp _ _ _

/-- Identical interpretations do not erase distinct retained source data. -/
example : continueWith first (.ok ⟨syntaxA, 7⟩) ≠
    continueWith first (.ok ⟨syntaxB, 7⟩) := by
  simp [continueWith, first, syntaxA, syntaxB, Retained.mk.injEq]

example : continueWith (fun _ : Nat => Except.error "later")
    (.error "earlier" : Except String (Retained Nat)) =
      (Except.error "earlier" : Except String (Retained Nat)) := rfl

example : continueWith (fun _ : Nat => Except.error "formation failed") (.ok ⟨syntaxA, 7⟩) =
    (Except.error "formation failed" : Except String (Retained Nat)) := rfl

example : SourcePacketView.view (.error "missing grammar") keepData (.symbol "bad") =
    .error "malformed source node" := rfl

private def listView : SourcePacket.Packet → Except String (String × List SourcePacket.Packet)
  | .symbol "two" => .ok ("items-more", [.symbol "x", .symbol "one"])
  | .symbol "one" => .ok ("items-one", [.symbol "x"])
  | _ => .error "not a list"

example : series listView "items" 2 (.symbol "two") = .ok [.symbol "x", .symbol "x"] := rfl
example : series listView "items" 1 (.symbol "two") =
    .error "source sequence exceeds its packet size" := rfl

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCompositionControls
