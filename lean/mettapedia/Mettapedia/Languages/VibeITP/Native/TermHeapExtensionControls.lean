import Mettapedia.Languages.VibeITP.Native.TermHeapExtension
import Mettapedia.Languages.VibeITP.Native.TermHeapControls

/-! Fresh insertion preserves actual shared graphs; freeing a child breaks them. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.TermHeapExtensionControls

open Mettapedia.GSLT.LanguageDef.NativeOps
open HeapCells TermHeap TermHeapControls

theorem fresh_insertion_keeps_shared_application :
    At (sourceStoreCell memory 200 0 (.word 99)) signature markers rootAddress
      (.app (.fresh 0) [.bvar 0, .bvar 0]) :=
  fresh_store_preserves_term shared_application_represented 200 0 (.word 99) rfl

theorem fresh_insertion_keeps_literal :
    At (sourceStoreCell memory 200 0 (.word 99)) signature markers literalAddress (.lit [65, 66]) :=
  fresh_store_preserves_term literal_represented 200 0 (.word 99) rfl

theorem released_child_has_no_interpretation :
    ∀ term, ¬ At (sourceRelease memory childAddress.storage) signature markers childAddress term :=
  missing_cell_unrepresented (by simp [sourceRead, sourceRelease])

theorem released_child_breaks_shared_application :
    ¬ At (sourceRelease memory childAddress.storage) signature markers rootAddress
      (.app (.fresh 0) [.bvar 0, .bvar 0]) := by
  intro represented
  cases represented with
  | @app address symbolAddress cell symbol info addresses terms stored head symbolStored declared
      contents children arity depth free noLiteral =>
      have same := term_cell_unique (sourceRelease memory childAddress.storage) rootAddress
        cell rootCell stored rfl
      cases same
      have arguments : [childAddress, childAddress] = addresses := Option.some.inj contents
      cases arguments
      cases children with
      | cons child tail => exact released_child_has_no_interpretation _ child

end Mettapedia.Languages.VibeITP.Native.TermHeapExtensionControls
