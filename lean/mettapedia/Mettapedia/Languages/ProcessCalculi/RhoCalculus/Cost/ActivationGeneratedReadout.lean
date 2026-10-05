import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

/-!
# The readout, one constructor at a time

Each equation is the defining clause of the readout for one generated constructor, stated for
the readout with its guarantees attached and projected to the term it returns.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax

theorem config_contact_readout (location : CostName LiteralAuthority)
    (free : location.purseInventory = 0) (supported : location.RuntimeSupported)
    (fuel : Nat) (left stackSource : Pattern) :
    (config? location free supported (fuel + 1)
      (.apply "$cost:apparatus-constructor:contact"
        [left, .apply "$cost:apparatus-constructor:funding" [stackSource]])).map Subtype.val =
      (do
        let code ← (config? location free supported fuel left).map Subtype.val
        let stack ← (stack? fuel stackSource).map Subtype.val
        some (locatedContact location code stack)) := by
  simp only [config?_val, stack?_val]; rfl

theorem config_signed_readout (location : CostName LiteralAuthority)
    (free : location.purseInventory = 0) (supported : location.RuntimeSupported)
    (fuel : Nat) (core signatureSource : Pattern) :
    (config? location free supported (fuel + 1)
      (.apply "$cost:apparatus-constructor:signed" [core, signatureSource])).map Subtype.val =
      (code? fuel 0 (.apply "$cost:apparatus-constructor:signed" [core, signatureSource])).map
        Subtype.val := by
  simp only [config?_val, code?_val]; rfl

theorem code_signed_readout (fuel depth : Nat) (core signatureSource : Pattern) :
    (code? (fuel + 1) depth
      (.apply "$cost:apparatus-constructor:signed" [core, signatureSource])).map Subtype.val =
      (do
        let signature ← (signature? signatureSource).map Subtype.val
        let process ← (proc? fuel depth core).map Subtype.val
        some (CostTerm.signed process signature)) := by
  simp only [code?_val, proc?_val]; rfl

theorem proc_pair_readout (fuel depth : Nat) (left right : Pattern) :
    (proc? (fuel + 1) depth (.collection .hashBag [left, right] none)).map Subtype.val =
      (do
        let first ← (proc? fuel depth left).map Subtype.val
        let second ← (proc? fuel depth right).map Subtype.val
        some (CostProc.par first second)) := by
  simp only [proc?_val]; rfl

theorem proc_recv_readout (fuel depth : Nat) (channel body : Pattern) :
    (proc? (fuel + 1) depth
      (.apply "$cost:base-constructor:PInput" [channel, .lambda none body])).map Subtype.val =
      (do
        let location ← (name? fuel depth channel).map Subtype.val
        let continuation ← (code? fuel (depth + 1) body).map Subtype.val
        some (CostProc.recv location continuation)) := by
  simp only [proc?_val, name?_val, code?_val]; rfl

theorem proc_send_readout (fuel depth : Nat) (channel payload : Pattern) :
    (proc? (fuel + 1) depth
      (.apply "$cost:base-constructor:POutput" [channel, payload])).map Subtype.val =
      (do
        let location ← (name? fuel depth channel).map Subtype.val
        let sent ← (code? fuel depth payload).map Subtype.val
        some (CostProc.send location sent)) := by
  simp only [proc?_val, name?_val, code?_val]; rfl

theorem code_drop_readout (fuel depth : Nat) (name : Pattern) :
    (code? (fuel + 1) depth (.apply "$cost:wrapped-constructor:PDrop" [name])).map Subtype.val =
      ((name? fuel depth name).map Subtype.val).map CostTerm.drop := by
  simp only [code?_val, name?_val]; rfl

theorem name_base_zero_quote_readout (fuel depth : Nat) :
    (name? (fuel + 1) depth
      (.apply "$cost:base-constructor:NQuote" [.apply "$cost:base-constructor:PZero" []])).map
      Subtype.val = some (.quote .nil) := name?_val _ _ _

theorem name_bvar_readout (fuel depth index : Nat) :
    (name? (fuel + 1) depth (.bvar index)).map Subtype.val =
      if index < depth then some (.bvar index) else none := name?_val _ _ _

theorem stack_cons_readout (fuel : Nat) (signatureSource tailSource : Pattern) :
    (stack? (fuel + 1)
      (.apply "$cost:apparatus-constructor:token-stack-cons" [signatureSource, tailSource])).map
      Subtype.val = (do
        let signature ← (signature? signatureSource).map Subtype.val
        let tail ← (stack? fuel tailSource).map Subtype.val
        some (CostStack.cons signature tail)) := by
  simp only [stack?_val]; rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
