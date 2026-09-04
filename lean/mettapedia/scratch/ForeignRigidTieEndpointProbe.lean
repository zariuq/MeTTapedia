import ForeignRigidTieOrderCanary

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace ForeignRigidTieOrderCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

noncomputable def leftEnvironment := CostStaticAtomEnvironment.ofInventory
  (leftView.node.semanticAtomEnvironment
    (leftView.children.normalizeValues
      (normalizeStatic := rhoHereditaryStaticNormalizer))).1

noncomputable def rightEnvironment := CostStaticAtomEnvironment.ofInventory
  (rightView.node.semanticAtomEnvironment
    (rightView.children.normalizeValues
      (normalizeStatic := rhoHereditaryStaticNormalizer))).1

noncomputable def cospan := leftEnvironment.semanticKeyCospan rightEnvironment

noncomputable def leftEndpoint (availableDepth scopeDepth : Nat) : Pattern :=
  cospan.reifyLeft leftEnvironment.lookupAtom?
    (leftView.node.thinning.thickenAmbientBVars scopeDepth
      (mapPattern (.base.symbols rhoCIGSLT)
        (canonicalizeByDepths
          (CostStaticRegionNode.sourceSemanticPatternKeyAt leftView.node
            leftEnvironment)
          rhoReflectivePresentation.toReflectivePresentationDecl
          availableDepth scopeDepth
          (leftEnvironment.reify leftView.node.plan.abstractPattern))))

noncomputable def rightEndpoint (availableDepth scopeDepth : Nat) : Pattern :=
  cospan.reifyRight rightEnvironment.lookupAtom?
    (rightView.node.thinning.thickenAmbientBVars scopeDepth
      (mapPattern (.base.symbols rhoCIGSLT)
        (canonicalizeByDepths
          (CostStaticRegionNode.sourceSemanticPatternKeyAt rightView.node
            rightEnvironment)
          rhoReflectivePresentation.toReflectivePresentationDecl
          availableDepth scopeDepth
          (rightEnvironment.reify rightView.node.plan.abstractPattern))))

#eval leftEndpoint 0 0
#eval rightEndpoint 0 0
#eval leftEndpoint 1 0
#eval rightEndpoint 1 0

end ForeignRigidTieOrderCanary
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
