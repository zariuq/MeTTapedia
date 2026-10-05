import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimePublicSelection
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolCallbackSupport
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimePrivateUpdate

/-!
# The actual public decoder receipt in the occurrence world

Receipt allocates the decoder's genuine fresh callback. The actual body of
that restriction is computed by opening its session binder with the selected
sender's name. After the unused reserved callback binder is exchanged with
this new binder, the result is the pending occurrence's original template.
No free private names are identified and no source continuation is replaced.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimePublicReceipt

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open Capabilities Ownership RuntimeState RuntimeActors ScopedActiveFrontier

def receiverPart {Γ : Ctx sig} (call : Call Γ) : Proc (.nm :: .nm :: Γ) :=
  par (out1 (.var (.succ .zero)) (.var .zero)) (receiveFields (lower call.body))

def freshBody {Γ : Ctx sig} (n : Nat) (owner : Fin n) (call : Call Γ) : Proc (.nm :: World n Γ) :=
  bind (liftSub (extend (keyName n owner .session)) [.nm])
    (rename (liftRen (ambient n) [.nm, .nm]) (receiverPart call))

def sessionRen {Γ : Ctx sig} (n : Nat) (owner : Fin n) :
    Ren sig (.nm :: Γ) (World n Γ) :=
  fun sort name => placement n owner sort (Var.succ name)

/-- Opening the actual decoded session leaves the new callback binder
intact. Ambient source names remain the existing injective inclusion. -/
theorem decoder_receipt {Γ : Ctx sig} (n : Nat) (owner : Fin n) (call : Call Γ) :
    inst (rename (liftRen (ambient n) [.nm]) (PublicRoles.decoderBody call.body))
        (keyName n owner .session) = nu (freshBody n owner call) := by
  unfold PublicRoles.decoderBody freshBody
  unfold receiverPart
  rw [rename_nu, ← liftRen_two (ambient n) Srt.nm Srt.nm]
  rfl

/-- Both actual name openings are the independently computed placement of
the original session/callback binders, with source names unchanged. -/
theorem callback_receipt {Γ : Ctx sig} (n : Nat) (owner : Fin n) (call : Call Γ) :
    inst (freshBody n owner call) (keyName n owner .callback) =
      rename (placement n owner) (receiverPart call) := by
  unfold freshBody inst
  rw [bind_comp, bind_rename]
  have nameMap :
      (fun (sort : Srt) (name : Var (Srt.nm :: Srt.nm :: Γ) sort) => bind (extend (keyName n owner .callback))
        (liftSub (extend (keyName n owner .session)) [.nm] sort
          (liftRen (ambient n) [.nm, .nm] sort name))) =
      (fun (sort : Srt) (name : Var (Srt.nm :: Srt.nm :: Γ) sort) => Term.var (placement n owner sort name)) := by
    funext sort name
    cases name with
    | zero => rfl
    | succ name => cases name with
      | zero => rfl
      | succ old => rfl
  calc
    _ = bind (fun sort name => Term.var (placement n owner sort name)) (receiverPart call) :=
      congrArg (fun sigma : Sub sig (.nm :: .nm :: Γ) (World n Γ) => bind sigma (receiverPart call)) nameMap
    _ = _ := bind_var_eq_rename _ _

theorem fresh_body_rename {Γ : Ctx sig} (n : Nat) (owner : Fin n) (call : Call Γ) :
    freshBody n owner call = rename
      (liftRen (sessionRen n owner) [.nm])
      (receiverPart call) := by
  unfold freshBody
  rw [bind_rename]
  have nameMap :
      (fun (sort : Srt) (name : Var (Srt.nm :: Srt.nm :: Γ) sort) =>
        liftSub (extend (keyName n owner .session)) [.nm] sort
          (liftRen (ambient n) [.nm, .nm] sort name)) =
      (fun (sort : Srt) (name : Var (Srt.nm :: Srt.nm :: Γ) sort) => Term.var
        (liftRen (sessionRen (Γ := Γ) n owner) [.nm] sort name)) := by
    funext sort name
    cases name with
    | zero => rfl
    | succ name => cases name <;> rfl
  calc
    _ = bind (fun (sort : Srt) (name : Var (Srt.nm :: Srt.nm :: Γ) sort) => Term.var
        (liftRen (sessionRen (Γ := Γ) n owner) [.nm] sort name))
        (receiverPart call) :=
      congrArg (fun sigma : Sub sig (.nm :: .nm :: Γ) (.nm :: World n Γ) =>
        bind sigma (receiverPart call)) nameMap
    _ = _ := bind_var_eq_rename _ _

theorem fresh_body_support {Γ : Ctx sig} (n : Nat) (owner : Fin n) (call : Call Γ) :
    countVar (Var.succ (key n owner .callback)) (freshBody n owner call) = 0 := by
  rw [fresh_body_rename]
  exact CallbackSupport.fresh_session_template_full_count_zero n owner _

/-- The sender's original waiter is the sender component of the pending
callback phase. Its body depends only on its retained ordered fields. -/
theorem waiter_receipt {Γ : Ctx sig} (n : Nat) (owner : Fin n) (call : Call Γ) :
    Actor.render (.waiter owner call.first call.second) =
      rename (placement n owner) (weaken (sendFields call.first call.second)) := by
  simp only [Actor.render, placedInput, inputTemplate, inputBody, waiterCall]
  rfl

theorem pending_receipt {Γ : Ctx sig} (n : Nat) (owner : Fin n) (call : Call Γ) :
    StructuralEq
      (par (inst (freshBody n owner call) (keyName n owner .callback))
        (Actor.render (.waiter owner call.first call.second)))
      ((Slot.pending .callback call).placed n owner) := by
  rw [callback_receipt, waiter_receipt, ← rename_par]
  apply StructuralEq.rename
  change StructuralEq
    (par (par _ _) _) (par (par _ _) _)
  exact (StructuralEq.parAssoc _ _ _).trans
    ((StructuralEq.par (.refl _) (.parComm _ _)).trans (StructuralEq.parAssoc _ _ _).symm)

/-- The exact supplied fresh callback endpoint, after closing the old
occurrence telescope, is the pending template beside the same frame. The
absence condition concerns the full term, including every guarded body. -/
theorem closed_receipt {Γ : Ctx sig} (n : Nat) (owner : Fin n) (call : Call Γ)
    (frame : Proc (World n Γ))
    (unused : countVar (Var.succ (key n owner .callback))
      (par (freshBody n owner call)
        (weaken (par (Actor.render (.waiter owner call.first call.second)) frame))) = 0) :
    StructuralEq
      ((privateScope n).close
        (par (nu (freshBody n owner call))
          (par (Actor.render (.waiter owner call.first call.second)) frame)))
      ((privateScope n).close (par ((Slot.pending .callback call).placed n owner) frame)) := by
  have extruded := (StructuralEq.nuPar (freshBody n owner call)
    (par (Actor.render (.waiter owner call.first call.second)) frame))
  have replaced := CallbackReuse.private_callback n owner
    (par (freshBody n owner call)
      (weaken (par (Actor.render (.waiter owner call.first call.second)) frame))) unused
  refine ((privateScope n).congr extruded).trans (replaced.trans ?_)
  change StructuralEq ((privateScope n).close
    (par (inst (freshBody n owner call) (keyName n owner .callback))
      (inst (weaken (par (Actor.render (.waiter owner call.first call.second)) frame))
        (keyName n owner .callback)))) _
  rw [inst_weaken]
  exact (privateScope n).congr ((StructuralEq.parAssoc _ _ _).symm.trans
    (.par (pending_receipt n owner call) (.refl _)))

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimePublicReceipt
