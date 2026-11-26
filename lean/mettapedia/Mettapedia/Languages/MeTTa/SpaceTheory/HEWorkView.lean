import Mettapedia.Languages.MeTTa.SpaceTheory.HEContextOnTransform

/-! The tag and payload of a local request, independently of its surrounding state. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HEWorkView

open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Task)
open Mettapedia.Languages.MeTTa.HE.ContextualData (taskData)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep (Expr)
open HEFocused (NativeRequest Leaf)
open HENativeOnTransform (ordinaryTag nativeExtras atom answerField)

def workView (task : Task) : Nat × List Expr :=
  match NativeRequest.recognize task with
  | some request => (1, nativeExtras request)
  | none => match HEContextEntry.Request.recognize task with
    | some request => (HEContextOnTransform.requestTag request, [])
    | none => (ordinaryTag task, [])

theorem workTag_not_return (task : Task) : (workView task).1 ≠ 2 := by
  unfold workView
  split
  · change 1 ≠ 2
    decide
  · split
    · exact HEContextOnTransform.tag_not_return _
    · exact HENativeOnTransform.ordinaryTag_not_return task

def leafView : Leaf → Nat × List Expr
  | .work task => ((workView task).1, atom (taskData task) :: (workView task).2)
  | .returning answers => (2, [answerField answers])

end Mettapedia.Languages.MeTTa.SpaceTheory.HEWorkView
