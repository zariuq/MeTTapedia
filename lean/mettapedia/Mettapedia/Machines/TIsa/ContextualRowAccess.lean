import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStoredRowCompilation
import Mettapedia.Machines.TIsa.PreparedFrameAccess

/-!
# Loads from a prepared contextual declaration frame

An operand is a slot of a particular compiled row. In a prepared p1 frame
that operand selects a constant displacement. The word representation of
slot images and custody of the frame are inputs to the load theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.ContextualRowAccess

open P1Source P1WordExecution PreparedFrameAccess
open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStoredRowCompilation (Code)

variable {S : Signature} {Local Shared : Type} {locals : Local → MetaArity S}
  {captures : Shared → MetaArity S} {Γ : Ctx S} {sort : S.Srt}

def load (convention : Convention) (code : Code locals captures Γ sort) (slot : Fin code.names.length)
    (destination : Reg) : Stmt :=
  PreparedFrameAccess.load convention destination (slotByte convention slot)

theorem load_executes (code : Code locals captures Γ sort) (slot : Fin code.names.length)
    (destination : Reg) {convention : Convention} {state : State} {offset : Nat}
    (layout : FrameLayout convention state offset code.names.length)
    (words : Fin code.names.length → Word)
    (present : state.memory (frameAddress convention state offset (slotByte convention slot)) =
      some (words slot)) :
    execute state (load convention code slot destination) = .continuing (state.write destination (words slot)) :=
  layout.loadsSlot destination slot (words slot) present

end Mettapedia.Machines.TIsa.ContextualRowAccess
