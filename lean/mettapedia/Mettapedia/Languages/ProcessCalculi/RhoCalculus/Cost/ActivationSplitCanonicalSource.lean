import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAmbientCanonicalEntry

/-!
# Separately signed endpoints, each with its own purse

The generated syntax of a receive and a send, signed separately, each in a contact with its own
purse, and its configuration image. The redex is `Funding.split`; the raw lemmas of its firing are
in `ActivationFundedRedex`. No generated rewrite is asserted for it: the generated language has
the whole rule only.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax

def splitReceiverSource (channel body payload recvSignature sendSignature recvTail sendTail : Pattern) : Pattern :=
  .collection .hashBag
    [.apply "$cost:apparatus-constructor:contact"
      [.apply "$cost:apparatus-constructor:signed"
        [.apply "$cost:base-constructor:PInput" [channel, .lambda none body], recvSignature],
       .apply "$cost:apparatus-constructor:funding"
        [.apply "$cost:apparatus-constructor:token-stack-cons" [recvSignature, recvTail]]],
     .apply "$cost:apparatus-constructor:contact"
      [.apply "$cost:apparatus-constructor:signed"
        [.apply "$cost:base-constructor:POutput" [channel, payload], sendSignature],
       .apply "$cost:apparatus-constructor:funding"
        [.apply "$cost:apparatus-constructor:token-stack-cons" [sendSignature, sendTail]]]] none

theorem split_receiver_config_image
    {channelSource bodySource payloadSource recvSignatureSource sendSignatureSource recvTailSource sendTailSource : Pattern}
    {location : CostName LiteralAuthority} {body payload : CostTerm LiteralAuthority}
    {recvTail sendTail : CostStack LiteralAuthority}
    (channelImage : NameImage 0 channelSource location)
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (recvSignature : TypedSignature recvSignatureSource)
    (recvAccepted : signature? recvSignatureSource = some recvSignature)
    (sendSignature : TypedSignature sendSignatureSource)
    (sendAccepted : signature? sendSignatureSource = some sendSignature)
    (recvTailImage : StackImage recvTailSource recvTail) (sendTailImage : StackImage sendTailSource sendTail) :
    ConfigImage location
      (splitReceiverSource channelSource bodySource payloadSource recvSignatureSource sendSignatureSource
        recvTailSource sendTailSource)
      (decodedSplitReceiver location body payload recvSignature.val sendSignature.val recvTail sendTail) :=
  .collection (.cons
    (.contact (.signed recvSignature recvAccepted (.recv channelImage bodyImage))
      (.cons recvSignature recvAccepted recvTailImage))
    (.cons (.contact (.signed sendSignature sendAccepted (.send channelImage payloadImage))
      (.cons sendSignature sendAccepted sendTailImage)) .nil))

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
