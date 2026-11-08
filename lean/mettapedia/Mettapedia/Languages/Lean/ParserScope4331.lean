import Mettapedia.GSLT.Parsing.ScopedGrammarState
import Mettapedia.Languages.Lean.ParserAdapter4331

/-!
# Lean 4.33.1 scoped-parser state correspondence

The portable frame operations are compared with the pinned implementation's
actual local and global update functions. Context is retained as an opaque
parameter in the frame theorem, so parser callbacks and active-name sets are
not replaced by hashes. Environment loading and command elaboration remain
separate executable boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Lean.ParserScope4331

open _root_.Lean
open Mettapedia.GSLT.Parsing.ScopedGrammarState

def exportFrame {Value : Type} (frame : Lean.ScopedEnvExtension.State Value) : Frame NameSet Value :=
  ⟨frame.state, frame.activeScopes, frame.delimitsLocal⟩

def importFrame {Value : Type} (frame : Frame NameSet Value) : Lean.ScopedEnvExtension.State Value :=
  ⟨frame.value, frame.context, frame.delimitsLocal⟩

theorem import_export_frame {Value : Type} (frame : Lean.ScopedEnvExtension.State Value) :
    importFrame (exportFrame frame) = frame := rfl

theorem export_import_frame {Value : Type} (frame : Frame NameSet Value) :
    exportFrame (importFrame frame) = frame := rfl

theorem local_update_agrees {Stored Entry Value : Type}
    (extension : Lean.ScopedEnvExtension Stored Entry Value)
    (frames : List (Lean.ScopedEnvExtension.State Value)) (entry : Entry) :
    (Lean.stateStackModify extension frames entry).map exportFrame =
      Frames.localUpdate extension.descr.addEntry entry (frames.map exportFrame) := by
  induction frames with
  | nil => rfl
  | cons top rest ih =>
      cases boundary : top.delimitsLocal <;>
        simp [Lean.stateStackModify, Frames.localUpdate, exportFrame, boundary, ih]

theorem global_update_agrees {Stored Entry Value : Type}
    (description : Lean.ScopedEnvExtension.Descr Stored Entry Value)
    (state : Lean.ScopedEnvExtension.StateStack Stored Entry Value) (entry : Entry) :
    (Lean.ScopedEnvExtension.addEntryFn description state (.global entry)).stateStack.map exportFrame =
      Frames.globalUpdate description.addEntry entry (state.stateStack.map exportFrame) := by
  cases state
  simp [Lean.ScopedEnvExtension.addEntryFn, Frames.globalUpdate, List.map_map, exportFrame]

theorem scoped_update_agrees {Stored Entry Value : Type}
    (description : Lean.ScopedEnvExtension.Descr Stored Entry Value)
    (state : Lean.ScopedEnvExtension.StateStack Stored Entry Value) (scopeName : Name) (entry : Entry) :
    (Lean.ScopedEnvExtension.addEntryFn description state (.scoped scopeName entry)).stateStack.map exportFrame =
      (state.stateStack.map exportFrame).map (fun frame =>
        if frame.context.contains scopeName then { frame with value := description.addEntry frame.value entry }
        else frame) := by
  cases state with
  | mk frames registry published =>
      simp only [Lean.ScopedEnvExtension.addEntryFn, List.map_map]
      apply List.map_congr_left
      intro frame member
      cases active : frame.activeScopes.contains scopeName <;> simp [exportFrame, active]

end Mettapedia.Languages.Lean.ParserScope4331
