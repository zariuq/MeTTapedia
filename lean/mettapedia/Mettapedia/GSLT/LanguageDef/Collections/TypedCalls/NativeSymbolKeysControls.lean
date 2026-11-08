import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeSymbolKeys

/-! # Symbol-sensitive key controls on actual annotation reads -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeSymbolKeysControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space)
open NativeTypeViews NativeTypeViewsControls NativeSymbolKeys

def tupleView (types : List Atom) : List Atom := types.filter (keepTuple false)

theorem symbols_with_equal_inferred_types_keep_distinct_keys :
    key (reads subtypeSpace) true "h" [sym "x"] ≠
      key (reads subtypeSpace) true "h" [sym "y"] := by decide +kernel

theorem subtype_left_admitted :
    Admitted (reads subtypeSpace) tupleView true "h" [sym "x"] := by
  simp only [Admitted, List.mem_singleton, forall_eq]
  dsimp only [sym, ChildAdmitted]
  decide +kernel

theorem subtype_right_admitted :
    Admitted (reads subtypeSpace) tupleView true "h" [sym "y"] := by
  simp only [Admitted, List.mem_singleton, forall_eq]
  dsimp only [sym, ChildAdmitted]
  decide +kernel

theorem symbol_sensitive_transitions_keep_raw_views :
    transition (ops subtypeSpace)
      (decode (reads subtypeSpace) tupleView (key (reads subtypeSpace) true "h" [sym "x"])) =
      [expr [sym "H", sym "A"]] ∧
    transition (ops subtypeSpace)
      (decode (reads subtypeSpace) tupleView (key (reads subtypeSpace) true "h" [sym "y"])) =
      [expr [sym "H", sym "A"], expr [sym "H", sym "B"]] := by
  rw [key_computes_source (ops subtypeSpace) subtype_left_admitted,
    key_computes_source (ops subtypeSpace) subtype_right_admitted]
  exact subtype_raw_tuple_answers

def numericSpace : Space := Space.ofList [annotation "h" (sym "H")]
def one : Atom := .grounded (.int 1)
def two : Atom := .grounded (.int 2)

theorem literal_values_still_share_key :
    key (reads numericSpace) true "h" [one] =
      key (reads numericSpace) true "h" [two] := by decide +kernel

theorem literal_views_admitted :
    Admitted (reads numericSpace) tupleView true "h" [one] ∧
      Admitted (reads numericSpace) tupleView true "h" [two] := by
  simp only [Admitted, List.mem_singleton, forall_eq]
  dsimp only [one, two, ChildAdmitted]
  decide +kernel

theorem literal_key_source_equality :
    sourceNode (ops numericSpace) (reads numericSpace) true (sym "h") [one] =
      sourceNode (ops numericSpace) (reads numericSpace) true (sym "h") [two] :=
  equal_keys_equal_source (ops numericSpace) literal_views_admitted.1 literal_views_admitted.2
    literal_values_still_share_key

def leftNode : Atom := expr [sym "Left", one]
def rightNode : Atom := expr [sym "Right", two]
def expressionSpace : Space := Space.ofList
  [annotation "h" (sym "H"), expr [sym ":", leftNode, sym "W"],
    expr [sym ":", rightNode, sym "W"]]

/-- Expression children are not keyed by their whole syntax. The actual
annotation reader supplies the same completed inference and tuple views. -/
theorem distinct_expression_children_share_key :
    leftNode ≠ rightNode ∧
      key (reads expressionSpace) true "h" [leftNode] =
        key (reads expressionSpace) true "h" [rightNode] := by decide +kernel

theorem expression_children_admitted :
    Admitted (reads expressionSpace) tupleView true "h" [leftNode] ∧
      Admitted (reads expressionSpace) tupleView true "h" [rightNode] := by
  simp only [Admitted, List.mem_singleton, forall_eq]
  dsimp only [leftNode, rightNode, expr, ChildAdmitted]
  decide +kernel

theorem expression_key_preserves_tuple_result :
    sourceNode (ops expressionSpace) (reads expressionSpace) true (sym "h") [leftNode] =
      [expr [sym "H", sym "W"]] ∧
    sourceNode (ops expressionSpace) (reads expressionSpace) true (sym "h") [rightNode] =
      [expr [sym "H", sym "W"]] := by decide +kernel

/-- The ordinary-head gate cannot admit the literal-sensitive special case.
Its whole-node inference remains available on a shape miss. -/
theorem native_handle_not_ordinary :
    ¬ Admitted (reads handleSpace) tupleView true "NativeHandle" [sym "mork-space", zero] := by
  intro admitted
  have ordinary := admitted.1
  have special : (reads handleSpace).classify (.symbol "NativeHandle") [sym "mork-space", zero] =
      .nativeMork := by decide +kernel
  rw [special] at ordinary
  cases ordinary

def annotatedParent : Space := expressionSpace.add
  (expr [sym ":", expr [sym "h", leftNode], sym "Override"])

theorem parent_annotation_blocks_shape_gate :
    ¬ Admitted (reads annotatedParent) tupleView true "h" [leftNode] := by
  intro admitted
  have none := admitted.2.1 rfl
  have some : (reads annotatedParent).annotations (.symbol "h") [leftNode] = [sym "Override"] := by
    decide +kernel
  rw [some] at none
  cases none

theorem ignored_annotation_question_retains_separate_key :
    key (reads annotatedParent) false "h" [leftNode] ≠
      key (reads annotatedParent) true "h" [leftNode] := by decide +kernel

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeSymbolKeysControls
