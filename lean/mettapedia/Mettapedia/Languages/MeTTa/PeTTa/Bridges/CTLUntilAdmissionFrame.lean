import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilScopedRound

/-!
# Entry conditions for uniformly admitted EU source frames

Completed refinement uses the weaker `Frame`. Uniform admission additionally
needs fresh result/temporary slots and the actual empty collapse-child tail.
The outer caller is retained by the enclosing collector, not erased here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilAdmissionFrame

open EagerDFS.Destination
open FlatQueryRowCodec (Codec)
open CTLUntilScopedRound (Query Frame)
open ClosedOnceQueryFrame (FreshFor)

structure AdmissionFrame {Label : Type} (codec : Codec Label) (label operand : Label)
    (round : Nat) (query : Query) (legs : List NestedQuerySource.Leg) (caller : Control) : Prop where
  frame : Frame codec label operand round query legs caller
  resultFresh : FreshFor query.names.result caller.bindings
  temporaryFresh : FreshFor query.names.temporary caller.bindings
  finished : caller.goals = []
  output : caller.destination = .var query.names.result

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilAdmissionFrame
