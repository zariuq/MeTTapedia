import Mettapedia.OSLF.Framework.RedexPosition
import Mettapedia.OSLF.Framework.WMCalculusOccurrenceTrace

/-!
# Concrete one-hole positions for world-model computation

Each typed contextual WM event selects one root rule inside an exact
constructor position. The selected subterm is an actual subterm of the
encoded source, and replacing it with the root rule's target reconstructs
the encoded target. This connects the proof-relevant WM event layer to the
generic one-hole position API. It concerns positions in running terms; it
does not identify them with positions in a rule schema's left-hand side.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusRedexPosition

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.RedexPosition
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusEncoding
open Mettapedia.OSLF.Framework.WMCalculusOccurrenceTrace

/-- The typed root occurrence and one-hole position selected by a contextual
event, with both reconstruction equations retained as data. -/
structure EventCut {s : WMSort} (source target : WMTerm s) where
  focusSort : WMSort
  focusSource : WMTerm focusSort
  focusTarget : WMTerm focusSort
  root : WMRootEvent focusSource focusTarget
  position : Position
  sourceAt : subtermAt (encodeWM source) position = some (encodeWM focusSource)
  targetPlug : plug (encodeWM source) position (encodeWM focusTarget) =
    some (encodeWM target)

private theorem binary_left_subterm (name : String) (left right focus : Pattern)
    (position : Position) (h : subtermAt left position = some focus) :
    subtermAt (.apply name [left, right]) (0 :: position) = some focus := by
  simpa [subtermAt, childAt, children] using h

private theorem binary_right_subterm (name : String) (left right focus : Pattern)
    (position : Position) (h : subtermAt right position = some focus) :
    subtermAt (.apply name [left, right]) (1 :: position) = some focus := by
  simpa [subtermAt, childAt, children] using h

private theorem binary_left_plug (name : String) (left left' right focus : Pattern)
    (position : Position) (rebuild : plug left position focus = some left') :
    plug (.apply name [left, right]) (0 :: position) focus =
      some (.apply name [left', right]) := by
  simp [plug, childAt, children, rebuild, withChildAt]

private theorem binary_right_plug (name : String) (left right right' focus : Pattern)
    (position : Position) (rebuild : plug right position focus = some right') :
    plug (.apply name [left, right]) (1 :: position) focus =
      some (.apply name [left, right']) := by
  simp [plug, childAt, children, rebuild, withChildAt]

/-- A contextual occurrence yields a genuine chosen one-hole position in
its encoded source, retaining the authored root rule at that position. -/
def cutOfEvent {s : WMSort} {source target : WMTerm s}
    (event : WMContextEvent source target) : EventCut source target :=
  match event with
  | .root root =>
      { focusSort := _
        focusSource := _
        focusTarget := _
        root := root
        position := []
        sourceAt := rfl
        targetPlug := rfl }
  | .revise_left second earlier =>
      let ih := cutOfEvent earlier
      { focusSort := ih.focusSort
        focusSource := ih.focusSource
        focusTarget := ih.focusTarget
        root := ih.root
        position := 0 :: ih.position
        sourceAt := binary_left_subterm "Revise" _ _ _ _ ih.sourceAt
        targetPlug := binary_left_plug "Revise" _ _ _ _ _ ih.targetPlug }
  | .revise_right first earlier =>
      let ih := cutOfEvent earlier
      { focusSort := ih.focusSort
        focusSource := ih.focusSource
        focusTarget := ih.focusTarget
        root := ih.root
        position := 1 :: ih.position
        sourceAt := binary_right_subterm "Revise" _ _ _ _ ih.sourceAt
        targetPlug := binary_right_plug "Revise" _ _ _ _ _ ih.targetPlug }
  | .extract_left query earlier =>
      let ih := cutOfEvent earlier
      { focusSort := ih.focusSort
        focusSource := ih.focusSource
        focusTarget := ih.focusTarget
        root := ih.root
        position := 0 :: ih.position
        sourceAt := binary_left_subterm "Extract" _ _ _ _ ih.sourceAt
        targetPlug := binary_left_plug "Extract" _ _ _ _ _ ih.targetPlug }
  | .extract_right world earlier =>
      let ih := cutOfEvent earlier
      { focusSort := ih.focusSort
        focusSource := ih.focusSource
        focusTarget := ih.focusTarget
        root := ih.root
        position := 1 :: ih.position
        sourceAt := binary_right_subterm "Extract" _ _ _ _ ih.sourceAt
        targetPlug := binary_right_plug "Extract" _ _ _ _ _ ih.targetPlug }
  | .combine_left second earlier =>
      let ih := cutOfEvent earlier
      { focusSort := ih.focusSort
        focusSource := ih.focusSource
        focusTarget := ih.focusTarget
        root := ih.root
        position := 0 :: ih.position
        sourceAt := binary_left_subterm "Combine" _ _ _ _ ih.sourceAt
        targetPlug := binary_left_plug "Combine" _ _ _ _ _ ih.targetPlug }
  | .combine_right first earlier =>
      let ih := cutOfEvent earlier
      { focusSort := ih.focusSort
        focusSource := ih.focusSource
        focusTarget := ih.focusTarget
        root := ih.root
        position := 1 :: ih.position
        sourceAt := binary_right_subterm "Combine" _ _ _ _ ih.sourceAt
        targetPlug := binary_right_plug "Combine" _ _ _ _ _ ih.targetPlug }

private def nestedSource : WMTerm .state :=
  .revise (.state "a") (.revise (.state "b") (.state "c"))

private def nestedTarget : WMTerm .state :=
  .revise (.state "a") (.revise (.state "c") (.state "b"))

private def nestedEvent : WMContextEvent nestedSource nestedTarget :=
  .revise_right (.state "a")
    (.root (.revision_comm (.state "b") (.state "c")))

/-- The chosen root redex really is the second argument of the outer
revision; its position is not recovered merely from the endpoint relation. -/
theorem nested_position : (cutOfEvent nestedEvent).position = [1] := rfl

theorem nested_sourceAt :
    subtermAt (encodeWM nestedSource) [1] =
      some (encodeWM (.revise (.state "b") (.state "c"))) := by
  decide +kernel

theorem nested_targetPlug :
    plug (encodeWM nestedSource) [1]
      (encodeWM (.revise (.state "c") (.state "b"))) =
        some (encodeWM nestedTarget) := by
  decide +kernel

/-- Selecting the other child would not locate the nested redex. -/
theorem nested_wrong_child :
    subtermAt (encodeWM nestedSource) [0] ≠
      some (encodeWM (.revise (.state "b") (.state "c"))) := by
  decide +kernel

end Mettapedia.OSLF.Framework.WMCalculusRedexPosition
