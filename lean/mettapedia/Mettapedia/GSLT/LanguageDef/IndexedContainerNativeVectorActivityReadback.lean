import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorPositionReading
import Mettapedia.Logic.HOL.OrderedPositionActivityReadback

/-!
# Exact guarded activity reading of the original mixed source

The generated activity programme is equal to the conjunction of its original
field guard and a scoped canonical-plan witness. Both directions use retained
proofs of the actual count/label conversions. No Peano, array, selection or
recursion premise is required for this representation equation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorActivityReadback
open Mettapedia.Logic Mettapedia.Logic.HOL
open IndexedContainerNativeVectorMethodReading (Base Const N E original)
open IndexedContainerNativeVectorPositionReading
open OrderedPositionPrograms

variable {Γ : Ctx Base} {Δ : List (Formula Const Γ)}

def positionWitness (length slot : Term Const Γ N) : Formula Const Γ :=
  activeAt original.zero original.successor (mixedPlan original.zero original.successor length .top .top .top) slot

@[irreducible] def certifiedEquation (payload : Term Const Γ (E ⇒ .prop))
    (length : Term Const Γ N) (tag : Term Const Γ E) (shape slot : Term Const Γ N) :
    { proof : ProofSyntax Const Δ (.eq (.app (sourceActivity payload length tag shape) slot)
      (.and (sourceAllowed payload length tag shape) (positionWitness length slot))) // proof.FunctionExtensionalityFree } :=
  IndexedConstructorGuards.PositionPrograms.certifiedActivityCanonicalEquation (constructors payload) original.zero original.successor
    (plans payload) (occurrence payload) (sourceArguments payload length tag shape)
    (mixedPlan original.zero original.successor length .top .top .top)
    (planEquations payload length tag shape) slot (planEquations_free _ _ _ _)

def equation (payload : Term Const Γ (E ⇒ .prop))
    (length : Term Const Γ N) (tag : Term Const Γ E) (shape slot : Term Const Γ N) :
    ProofSyntax Const Δ (.eq (.app (sourceActivity payload length tag shape) slot)
      (.and (sourceAllowed payload length tag shape) (positionWitness length slot))) :=
  (certifiedEquation payload length tag shape slot).val

theorem equation_free (payload : Term Const Γ (E ⇒ .prop))
    (length : Term Const Γ N) (tag : Term Const Γ E) (shape slot : Term Const Γ N) :
    (equation (Δ := Δ) payload length tag shape slot).FunctionExtensionalityFree :=
  (certifiedEquation payload length tag shape slot).property

def fromActivity (payload : Term Const Γ (E ⇒ .prop))
    (length : Term Const Γ N) (tag : Term Const Γ E) (shape slot : Term Const Γ N)
    (present : ProofSyntax Const Δ (.app (sourceActivity payload length tag shape) slot)) :
    ProofSyntax Const Δ (.and (sourceAllowed payload length tag shape) (positionWitness length slot)) :=
  .impE (.eqPropEL (equation payload length tag shape slot)) present

def toActivity (payload : Term Const Γ (E ⇒ .prop))
    (length : Term Const Γ N) (tag : Term Const Γ E) (shape slot : Term Const Γ N)
    (present : ProofSyntax Const Δ (.and (sourceAllowed payload length tag shape) (positionWitness length slot))) :
    ProofSyntax Const Δ (.app (sourceActivity payload length tag shape) slot) :=
  .impE (.eqPropER (equation payload length tag shape slot)) present

theorem fromActivity_free (payload : Term Const Γ (E ⇒ .prop))
    (length : Term Const Γ N) (tag : Term Const Γ E) (shape slot : Term Const Γ N)
    (present : ProofSyntax Const Δ (.app (sourceActivity payload length tag shape) slot))
    (free : present.FunctionExtensionalityFree) :
    (fromActivity payload length tag shape slot present).FunctionExtensionalityFree :=
  ⟨equation_free _ _ _ _ _,free⟩

theorem toActivity_free (payload : Term Const Γ (E ⇒ .prop))
    (length : Term Const Γ N) (tag : Term Const Γ E) (shape slot : Term Const Γ N)
    (present : ProofSyntax Const Δ (.and (sourceAllowed payload length tag shape) (positionWitness length slot)))
    (free : present.FunctionExtensionalityFree) :
    (toActivity payload length tag shape slot present).FunctionExtensionalityFree :=
  ⟨equation_free _ _ _ _ _,free⟩

#print axioms equation_free
#print axioms fromActivity
#print axioms toActivity
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorActivityReadback
