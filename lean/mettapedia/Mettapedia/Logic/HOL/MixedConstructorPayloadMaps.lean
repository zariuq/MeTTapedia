import Mettapedia.Logic.HOL.CurriedGuardProgramProofs
import Mettapedia.Logic.HOL.GuardedRetraction

/-!
# Retained maps of the middle field of a mixed constructor payload

The map precomposes the actual predicate handler with the field map. Beta
proofs compute it on the original number/element/number encoding. A supplied
field recovery proof then gives an explicit payload recovery derivation.
Neither payload injectivity nor constructor uniqueness is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.MixedConstructorPayloadMaps
open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
    {number source target : Ty Base} {Δ : List (Formula Const Γ)}

abbrev Payload (number element : Ty Base) := payloadType [[number,element,number]]

def pack (index : Term Const Γ number) (element : Term Const Γ source) (shape : Term Const Γ number) :
    Term Const Γ (Payload number source) := encode [[number,source,number]] ⟨0,Nat.zero_lt_succ 0⟩ (index,element,shape,PUnit.unit)

theorem pack_subst (images : Subst Const Γ Ξ) (index : Term Const Γ number)
    (element : Term Const Γ source) (shape : Term Const Γ number) :
    HOL.subst images (pack index element shape) =
      pack (HOL.subst images index) (HOL.subst images element) (HOL.subst images shape) := by
  simp only [pack,encode_subst]
  rfl

theorem pack_weaken (index : Term Const Γ number) (element : Term Const Γ source)
    (shape : Term Const Γ number) {bound : Ty Base} :
    weaken (σ := bound) (pack index element shape) = pack (weaken index) (weaken element) (weaken shape) := by
  simpa only [subst_ofRename,weaken] using pack_subst (Subst.ofRename (Rename.weaken (σ := bound))) index element shape

def handlerBody (fieldMap : Term Const Γ (source ⇒ target))
    (targetHandler : Term Const Γ (handlerType [number,target,number])) : ArgumentBody Const Γ [number,source,number] :=
  fun images arguments => applyArguments [number,target,number] (HOL.subst images targetHandler)
    (arguments.1,.app (HOL.subst images fieldMap) arguments.2.1,arguments.2.2.1,PUnit.unit)

theorem handlerBody_natural (fieldMap : Term Const Γ (source ⇒ target))
    (targetHandler : Term Const Γ (handlerType [number,target,number])) : NaturalBody (handlerBody fieldMap targetHandler) := by
  intro Ξ Ω earlier later arguments
  simp only [handlerBody,applyArguments,substituteArguments,HOL.subst,HOL.subst_comp]
  rfl

def handler (fieldMap : Term Const Γ (source ⇒ target))
    (targetHandler : Term Const Γ (handlerType [number,target,number])) :
    Term Const Γ (handlerType [number,source,number]) :=
  abstractArguments [number,source,number] (handlerBody fieldMap targetHandler)

def mapPayload (fieldMap : Term Const Γ (source ⇒ target)) (payload : Term Const Γ (Payload number source)) :
    Term Const Γ (Payload number target) :=
  .lam (.app (weaken payload) (handler (weaken fieldMap) (.var .vz)))

theorem handler_subst (images : Subst Const Γ Ξ) (fieldMap : Term Const Γ (source ⇒ target))
    (targetHandler : Term Const Γ (handlerType [number,target,number])) :
    HOL.subst images (handler fieldMap targetHandler) = handler (HOL.subst images fieldMap) (HOL.subst images targetHandler) := by
  rw [handler,abstractArguments_subst _ _ _ (handlerBody_natural fieldMap targetHandler)]
  apply congrArg (abstractArguments [number,source,number])
  funext laterContext later arguments
  simp only [handlerBody,HOL.subst_comp]
  rfl

theorem mapPayload_subst (images : Subst Const Γ Ξ) (fieldMap : Term Const Γ (source ⇒ target))
    (payload : Term Const Γ (Payload number source)) :
    HOL.subst images (mapPayload fieldMap payload) = mapPayload (HOL.subst images fieldMap) (HOL.subst images payload) := by
  simp only [mapPayload,HOL.subst,subst_weaken,handler_subst]
  rfl

@[irreducible] def handler_apply (fieldMap : Term Const Γ (source ⇒ target))
    (targetHandler : Term Const Γ (handlerType [number,target,number]))
    (index : Term Const Γ number) (element : Term Const Γ source) (shape : Term Const Γ number) :
    ProofSyntax Const Δ (.eq (applyArguments [number,source,number] (handler fieldMap targetHandler)
      (index,element,shape,PUnit.unit))
      (applyArguments [number,target,number] targetHandler (index,.app fieldMap element,shape,PUnit.unit))) := by
  apply ProofSyntax.castIndices rfl ?_ (abstractArguments_beta [number,source,number]
    (handlerBody fieldMap targetHandler) (handlerBody_natural fieldMap targetHandler) (index,element,shape,PUnit.unit))
  have identityTerm {type : Ty Base} (term : Term Const Γ type) : HOL.subst (fun index => .var index) term = term :=
    ProofSyntax.term_subst_of_identity (fun _ => rfl) term
  simp only [handlerBody,identityTerm,handler]

theorem handler_apply_free (fieldMap : Term Const Γ (source ⇒ target))
    (targetHandler : Term Const Γ (handlerType [number,target,number]))
    (index : Term Const Γ number) (element : Term Const Γ source) (shape : Term Const Γ number) :
    (handler_apply (Δ := Δ) fieldMap targetHandler index element shape).FunctionExtensionalityFree := by
  unfold handler_apply
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact abstractArguments_beta_free _ _ _ _

def mapPayload_congr (fieldMap : Term Const Γ (source ⇒ target))
    (first second : Term Const Γ (Payload number source))
    (proof : ProofSyntax Const Δ (.eq first second)) :
    ProofSyntax Const Δ (.eq (mapPayload fieldMap first) (mapPayload fieldMap second)) :=
  .eqLam (.eqApp (handler (weaken fieldMap) (.var .vz)) (proof.rename Rename.weaken))

theorem mapPayload_congr_free (fieldMap : Term Const Γ (source ⇒ target))
    (first second : Term Const Γ (Payload number source))
    (proof : ProofSyntax Const Δ (.eq first second)) (free : proof.FunctionExtensionalityFree) :
    (mapPayload_congr fieldMap first second proof).FunctionExtensionalityFree :=
  (ProofSyntax.functionExtensionalityFree_rename _ _).mpr free

@[irreducible] def pack_apply (index : Term Const Γ number) (element : Term Const Γ source)
    (shape : Term Const Γ number) (sourceHandler : Term Const Γ (handlerType [number,source,number])) :
    ProofSyntax Const Δ (.eq (.app (pack index element shape) sourceHandler)
      (applyArguments [number,source,number] sourceHandler (index,element,shape,PUnit.unit))) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta sourceHandler
    (applyArguments [number,source,number] (.var .vz)
      (weaken index,weaken element,weaken shape,PUnit.unit)))
  simp only [instantiate,applyArguments,HOL.subst,Subst.single,PredicateFixedPoint.subst_single_weaken]
  rfl

theorem pack_apply_free (index : Term Const Γ number) (element : Term Const Γ source)
    (shape : Term Const Γ number) (sourceHandler : Term Const Γ (handlerType [number,source,number])) :
    (pack_apply (Δ := Δ) index element shape sourceHandler).FunctionExtensionalityFree := by
  unfold pack_apply
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

@[irreducible] def mapPayload_pack (fieldMap : Term Const Γ (source ⇒ target))
    (index : Term Const Γ number) (element : Term Const Γ source) (shape : Term Const Γ number) :
    ProofSyntax Const Δ (.eq (mapPayload fieldMap (pack index element shape))
      (pack index (.app fieldMap element) shape)) := by
  let mapped := handler (number := number) (weaken fieldMap) (.var .vz)
  have first : ProofSyntax Const (weakenHyps (σ := handlerType [number,target,number]) Δ)
      (.eq (.app (weaken (pack index element shape)) mapped)
        (applyArguments [number,source,number] mapped (weaken index,weaken element,weaken shape,PUnit.unit))) := by
    exact ProofSyntax.castIndices rfl
      (congrArg (fun code => Term.eq (.app code mapped)
        (applyArguments [number,source,number] mapped (weaken index,weaken element,weaken shape,PUnit.unit)))
        (pack_weaken index element shape).symm)
      (pack_apply (weaken index) (weaken element) (weaken shape) mapped)
  exact .eqLam (.eqTrans first (handler_apply (weaken fieldMap) (.var .vz) (weaken index) (weaken element) (weaken shape)))

theorem mapPayload_pack_free (fieldMap : Term Const Γ (source ⇒ target))
    (index : Term Const Γ number) (element : Term Const Γ source) (shape : Term Const Γ number) :
    (mapPayload_pack (Δ := Δ) fieldMap index element shape).FunctionExtensionalityFree := by
  unfold mapPayload_pack
  refine ⟨?_,handler_apply_free _ _ _ _ _⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact pack_apply_free _ _ _ _

def pack_middle_congr (index : Term Const Γ number) (first second : Term Const Γ source)
    (shape : Term Const Γ number) (same : ProofSyntax Const Δ (.eq first second)) :
    ProofSyntax Const Δ (.eq (pack index first shape) (pack index second shape)) :=
  .eqLam (.eqApp (weaken shape) (.eqAppArg (.app (.var .vz) (weaken index)) (same.rename Rename.weaken)))

def roundtrip_at (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source))
    (index : Term Const Γ number) (element : Term Const Γ source) (shape : Term Const Γ number)
    (recover : ProofSyntax Const Δ (.eq (.app raise (.app lower element)) element)) :
    ProofSyntax Const Δ (.eq (mapPayload raise (mapPayload lower (pack index element shape))) (pack index element shape)) :=
  .eqTrans (mapPayload_congr raise _ _ (mapPayload_pack lower index element shape))
    (.eqTrans (mapPayload_pack raise index (.app lower element) shape)
      (pack_middle_congr index _ element shape recover))

theorem roundtrip_at_free (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source))
    (index : Term Const Γ number) (element : Term Const Γ source) (shape : Term Const Γ number)
    (recover : ProofSyntax Const Δ (.eq (.app raise (.app lower element)) element))
    (free : recover.FunctionExtensionalityFree) :
    (roundtrip_at lower raise index element shape recover).FunctionExtensionalityFree := by
  refine ⟨mapPayload_congr_free _ _ _ _ (mapPayload_pack_free _ _ _ _),mapPayload_pack_free _ _ _ _,?_⟩
  exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr free

#print axioms mapPayload_pack_free
#print axioms roundtrip_at_free
end Mettapedia.Logic.HOL.MixedConstructorPayloadMaps
