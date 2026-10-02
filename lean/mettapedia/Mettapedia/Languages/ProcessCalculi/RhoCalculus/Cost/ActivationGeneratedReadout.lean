import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

/-!
# Computational projections of the certifying generated decoder

Each equation is derived from the actual decoder, retaining its checks while
exposing only returned syntax. This keeps composition proofs independent of
the size of the erased proof certificates.
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
  cases codeParsed : config? location free supported fuel left <;>
    cases stackParsed : stack? fuel stackSource <;>
    simp [config?, codeParsed, stackParsed]

theorem config_signed_readout (location : CostName LiteralAuthority)
    (free : location.purseInventory = 0) (supported : location.RuntimeSupported)
    (fuel : Nat) (core signatureSource : Pattern) :
    (config? location free supported (fuel + 1)
      (.apply "$cost:apparatus-constructor:signed" [core, signatureSource])).map Subtype.val =
      (code? fuel 0 (.apply "$cost:apparatus-constructor:signed" [core, signatureSource])).map
        Subtype.val := by
  cases parsed : code? fuel 0 (.apply "$cost:apparatus-constructor:signed" [core, signatureSource]) <;>
    simp [config?, parsed]

theorem code_signed_readout (fuel depth : Nat) (core signatureSource : Pattern) :
    (code? (fuel + 1) depth
      (.apply "$cost:apparatus-constructor:signed" [core, signatureSource])).map Subtype.val =
      (do
        let signature ← (signature? signatureSource).map Subtype.val
        let process ← (proc? fuel depth core).map Subtype.val
        some (CostTerm.signed process signature)) := by
  cases signatureParsed : signature? signatureSource <;>
    cases processParsed : proc? fuel depth core <;>
    simp [code?, signatureParsed, processParsed]

theorem proc_pair_readout (fuel depth : Nat) (left right : Pattern) :
    (proc? (fuel + 1) depth (.collection .hashBag [left, right] none)).map Subtype.val =
      (do
        let first ← (proc? fuel depth left).map Subtype.val
        let second ← (proc? fuel depth right).map Subtype.val
        some (CostProc.par first second)) := by
  cases firstParsed : proc? fuel depth left <;>
    cases secondParsed : proc? fuel depth right <;>
    simp [proc?, firstParsed, secondParsed]

theorem proc_recv_readout (fuel depth : Nat) (channel body : Pattern) :
    (proc? (fuel + 1) depth
      (.apply "$cost:base-constructor:PInput" [channel, .lambda none body])).map Subtype.val =
      (do
        let location ← (name? fuel depth channel).map Subtype.val
        let continuation ← (code? fuel (depth + 1) body).map Subtype.val
        some (CostProc.recv location continuation)) := by
  cases channelParsed : name? fuel depth channel <;>
    cases bodyParsed : code? fuel (depth + 1) body <;>
    simp [proc?, channelParsed, bodyParsed]

theorem proc_send_readout (fuel depth : Nat) (channel payload : Pattern) :
    (proc? (fuel + 1) depth
      (.apply "$cost:base-constructor:POutput" [channel, payload])).map Subtype.val =
      (do
        let location ← (name? fuel depth channel).map Subtype.val
        let sent ← (code? fuel depth payload).map Subtype.val
        some (CostProc.send location sent)) := by
  cases channelParsed : name? fuel depth channel <;>
    cases payloadParsed : code? fuel depth payload <;>
    simp [proc?, channelParsed, payloadParsed]

theorem code_drop_readout (fuel depth : Nat) (name : Pattern) :
    (code? (fuel + 1) depth (.apply "$cost:wrapped-constructor:PDrop" [name])).map Subtype.val =
      ((name? fuel depth name).map Subtype.val).map CostTerm.drop := by
  cases parsed : name? fuel depth name <;> simp [code?, parsed]

theorem name_base_zero_quote_readout (fuel depth : Nat) :
    (name? (fuel + 1) depth
      (.apply "$cost:base-constructor:NQuote" [.apply "$cost:base-constructor:PZero" []])).map
      Subtype.val = some (.quote .nil) := rfl

theorem name_bvar_readout (fuel depth index : Nat) :
    (name? (fuel + 1) depth (.bvar index)).map Subtype.val =
      if index < depth then some (.bvar index) else none := by
  by_cases bound : index < depth <;> simp [name?, bound]

theorem stack_cons_readout (fuel : Nat) (signatureSource tailSource : Pattern) :
    (stack? (fuel + 1)
      (.apply "$cost:apparatus-constructor:token-stack-cons" [signatureSource, tailSource])).map
      Subtype.val = (do
        let signature ← (signature? signatureSource).map Subtype.val
        let tail ← (stack? fuel tailSource).map Subtype.val
        some (CostStack.cons signature tail)) := by
  cases signatureParsed : signature? signatureSource <;>
    cases tailParsed : stack? fuel tailSource <;>
    simp [stack?, signatureParsed, tailParsed]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
