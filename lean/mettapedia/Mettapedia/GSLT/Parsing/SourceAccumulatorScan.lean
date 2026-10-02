import Mettapedia.GSLT.Parsing.SourceScanSegments

/-!
Replay laws for the original source scanner with an arbitrary accumulator.
A local transition never needs to reduce the preceding source history. The
retained characters are explicit, so this interface also distinguishes source
input from the text retained by comment handling.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.SourceAccumulatorScan

open SourceScanSegments

structure Point where
  line : Nat
  depth : Nat
  inComment : Bool
  inString : Bool
  escaped : Bool
  started : Bool
  startLine : Nat
  deriving DecidableEq, Repr

def Point.state (point : Point) (current : List Char) (forms : List (Nat × String)) : ScanState :=
  makeScanState point.line point.depth point.inComment point.inString point.escaped
    point.started point.startLine current forms none

def initialPoint : Point := ⟨1, 0, false, false, false, false, 1⟩

def closingPoint (line : Nat) : Point := ⟨line, 1, false, false, false, true, 1⟩

def Agreement (before after : Point) (input retained : List Char) : Prop :=
  ∀ current forms, input.foldl step (before.state current forms) =
    after.state (retained.reverse ++ current) forms

theorem agreement_append (before middle after : Point)
    (firstInput secondInput firstRetained secondRetained : List Char)
    (first : Agreement before middle firstInput firstRetained)
    (second : Agreement middle after secondInput secondRetained) :
    Agreement before after (firstInput ++ secondInput) (firstRetained ++ secondRetained) := by
  intro current forms
  rw [List.foldl_append, first current forms, second (firstRetained.reverse ++ current) forms]
  simp only [List.reverse_append, List.append_assoc]

theorem agreement_empty (point : Point) : Agreement point point [] [] := by
  intro current forms
  rfl

theorem initial_state : initialPoint.state [] [] = initialScanState := rfl

theorem scanned_single_form (line : Nat) (input retained : List Char) (source : String)
    (replay : Agreement initialPoint (closingPoint line) input retained)
    (text : String.ofList (retained ++ [')']) = source)
    (trimmed : source.trimAscii.toString = source) (nonempty : source.isEmpty = false) :
    (input ++ [')']).foldl step initialScanState =
      makeScanState line 0 false false false false line [] [(1, source)] none := by
  rw [← initial_state, List.foldl_append, replay [] []]
  simp only [List.append_nil]
  have reversed : String.ofList (')' :: retained.reverse).reverse = source := by
    simpa only [List.reverse_cons, List.reverse_reverse] using text
  exact close_singleton_form line retained.reverse source reversed trimmed nonempty

theorem retained_last_boundary (retained : List Char) :
    (retained ++ [')']).getLast? = some ')' := by simp

end Mettapedia.GSLT.Parsing.SourceAccumulatorScan
