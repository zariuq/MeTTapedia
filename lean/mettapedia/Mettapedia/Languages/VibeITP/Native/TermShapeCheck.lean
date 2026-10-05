import Mettapedia.Languages.VibeITP.Presentation.TermShape

/-!
# Executable structural guards for Vibe term computations

The guard checks symbol membership, arity and every child. Word bounds remain
the responsibility of each operation; early exits must retain their meaning
even when a structural term contains an unbounded natural index.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.TermShapeCheck

open Mettapedia.Languages.VibeITP.Spec
open Mettapedia.Languages.VibeITP.Presentation

mutual
def check (sig : Sig) : Term → Bool
  | .bvar _ => true
  | .lit _ => true
  | .app symbol arguments =>
      match sig symbol with
      | none => false
      | some info => decide (arguments.length = info.arity) && checkList sig arguments

def checkList (sig : Sig) : List Term → Bool
  | [] => true
  | term :: terms => check sig term && checkList sig terms
end

mutual
theorem check_iff (sig : Sig) (term : Term) : check sig term = true ↔ TermShape sig term := by
  cases term with
  | bvar index => exact ⟨fun _ => .bvar index, fun _ => rfl⟩
  | lit bytes => exact ⟨fun _ => .lit bytes, fun _ => rfl⟩
  | app symbol arguments =>
      rw [TermShape.app_iff]
      cases lookup : sig symbol with
      | none => simp [check, lookup]
      | some info => simp [check, lookup, checkList_iff sig arguments]
termination_by sizeOf term

theorem checkList_iff (sig : Sig) (terms : List Term) :
    checkList sig terms = true ↔ TermShapeList sig terms := by
  cases terms with
  | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
  | cons term terms =>
      simp only [checkList, Bool.and_eq_true, TermShapeList.cons_iff,
        check_iff sig term, checkList_iff sig terms]
termination_by sizeOf terms
end

end Mettapedia.Languages.VibeITP.Native.TermShapeCheck
