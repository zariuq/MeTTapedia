import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EscapeTransport

/-! # The actual endpoint isomorphism of a transported native run -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport

universe uO uT uH uOcc uS uF uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} (T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P)

def moveRunEndIso : ∀ {source target : State} (iso : T.Iso source target) (run : P.Run source),
    T.Iso run.last (T.moveRun iso run).last
  | _, _, iso, .nil _ => iso
  | _, _, iso, .cons firing allowed rest => moveRunEndIso (T.result_move iso firing allowed) rest

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport
