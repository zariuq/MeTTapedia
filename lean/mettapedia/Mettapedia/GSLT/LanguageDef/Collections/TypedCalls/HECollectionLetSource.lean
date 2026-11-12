import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionLetFrontier
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionUnifySource

/-!
# The authored let call resumes its numeric consumer

The complete physical frontier and contextual capture earn the raw unify
body. Ordinary return evaluation enters its four held operands, binds the
collected data, and runs the actual fold. No completed let result is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionLetSource

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation Spec.Bindings.ScopeObservation
open RetainedTypePayloads (ExternalView)
open HECollectionWorld (World environment)
open HECollectionNumericFold (number)
open HECollectionLetCapture (call instruction)

variable (minimal : Minimal.Services) (nativePolicy : Policy) (external : ExternalView)
  (active : String → Bool) (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)

local notation "current" => environment minimal nativePolicy external active primitive subtypes
local notation "sourceSpace" => HECollectionSpaceExtension.space

theorem called (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (values : List Int) (init : Int) (listName left right : String) (itemsMark : Entry.Status)
    (listLeft : listName ≠ left) (listRight : listName ≠ right) (different : left ≠ right)
    (listFixed : before.read policy (.var listName) = .var listName)
    (leftFixed : before.read policy (.var left) = .var left) (rightFixed : before.read policy (.var right) = .var right) :
    ∃ after, Stateful.CallRel current sourceSpace world live scope
      (call values init listName left right itemsMark) Atom.undefinedType before
      [(number (values.foldl (· + ·) init), after)] world (policy := policy) := by
  obtain ⟨work, captured, patternName, frontier, bindings, unified, bodyRead, patternLeft, patternRight,
      patternFixed, keptLeft, keptRight⟩ := HECollectionLetFrontier.complete_frame policy (Atom.undefinedType :: live) before
    values init listName left right itemsMark listLeft listRight different listFixed leftFixed rightFixed
  obtain ⟨after, executed⟩ := HECollectionUnifySource.source minimal nativePolicy external active primitive subtypes
    world policy captured live scope values init patternName left right itemsMark patternLeft patternRight different patternFixed keptLeft keptRight
  have returned : Stateful.ReturnRel current sourceSpace world live scope (call values init listName left right itemsMark) Atom.undefinedType
      (instruction values init patternName left right itemsMark) captured
      [(number (values.foldl (· + ·) init), after)] world (policy := policy) :=
    .evaluate (by simp [instruction, Entry.Value.erase, Atom.notReducible])
      (by simp [instruction, Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) executed
  refine ⟨after, Stateful.CallRel.equations (works := [work]) ?_ ?_ frontier (by simp) ?_⟩
  · simp [call, Entry.Value.erase, IsErrorRel]
  · simpa only [call, Entry.Value.erase, List.map_cons, List.map_nil] using
      HECollectionWorld.ordinary minimal nativePolicy external active primitive subtypes "let"
        [(.var listName : Entry.Value).erase,
          (.expression itemsMark (HECollectionNumericFold.numbers values) : Entry.Value).erase,
          (HECollectionLetCapture.template listName left right init).erase] (by simp)
  · simpa only [List.append_nil] using
      (Stateful.EquationBodiesRel.cons bindings unified
        (by
          rw [bodyRead]
          exact Stateful.BoundaryRel.producerRaw (by
            simp [FunctionPending, instruction, Entry.Value.erase, Minimal.IsFunction]))
        (Stateful.BoundaryBatchRel.single_iff.mpr (.returned returned)) Stateful.EquationBodiesRel.nil)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionLetSource
