import Mettapedia.Logic.HOL.ConstructorPayloadTransport
import Mettapedia.Logic.HOL.GuardedConstructorProjectionProofs

/-!
# Guarded constructor uniqueness through payload recovery

A source constructor separates its source payload and child fields. A
represented constructor first maps a stored payload to that source type.
Recovery on the admitted domain, expressed by a retained proof producer at
every typed substitution, reflects source equality to the stored payload.
The admission relation may constrain all three ports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.RepresentedConstructorAdmission
open MixedConstructorPayloadMaps
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
  {number source target children carrier : Ty Base} {Δ : List (Formula Const Γ)}

def Recovery (premises : List (Formula Const Γ))
    (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source))
    (domain : Term Const Γ (GuardedConstructorProjections.Admission number (Payload number source) children)) :=
  ∀ {Ξ : Ctx Base} (images : Subst Const Γ Ξ) {assumptions : List (Formula Const Ξ)}
    (_transport : ProofSyntax.OccurrenceMap (premises.map (HOL.subst images)) assumptions)
    (tag : Term Const Ξ number) (payload : Term Const Ξ (Payload number source)) (branches : Term Const Ξ children),
    ProofSyntax Const assumptions (GuardedConstructorProjections.admitted (HOL.subst images domain) tag payload branches) →
    ProofSyntax Const assumptions (.eq
      (mapPayload (HOL.subst images raise) (mapPayload (HOL.subst images lower) payload)) payload)

def Recovery.Free {premises : List (Formula Const Γ)}
    {lower : Term Const Γ (source ⇒ target)} {raise : Term Const Γ (target ⇒ source)}
    {domain : Term Const Γ (GuardedConstructorProjections.Admission number (Payload number source) children)}
    (recover : Recovery premises lower raise domain) : Prop :=
  ∀ {Ξ : Ctx Base} (images : Subst Const Γ Ξ) {assumptions : List (Formula Const Ξ)}
    (transport : ProofSyntax.OccurrenceMap (premises.map (HOL.subst images)) assumptions)
    (tag : Term Const Ξ number) (payload : Term Const Ξ (Payload number source)) (branches : Term Const Ξ children)
    (present : ProofSyntax Const assumptions (GuardedConstructorProjections.admitted (HOL.subst images domain) tag payload branches)),
    present.FunctionExtensionalityFree → (recover images transport tag payload branches present).FunctionExtensionalityFree

theorem constructor_subst (images : Subst Const Γ Ξ)
    (raw : Term Const Γ (ConstructorPayloadTransport.Raw (number := number) (target := target) (children := children) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) :
    HOL.subst images (ConstructorPayloadTransport.constructor raw lower) =
      ConstructorPayloadTransport.constructor (HOL.subst images raw) (HOL.subst images lower) := by
  rw [ConstructorPayloadTransport.constructor,
    CurriedPredicates.abstractFields_subst _ _ _ (ConstructorPayloadTransport.body_natural raw lower)]
  apply congrArg (CurriedPredicates.abstractFields [number,Payload number source,children])
  funext laterContext later arguments
  simp only [ConstructorPayloadTransport.body,ConstructorPayloadTransport.value,
    ConstructorProjections.apply,HOL.subst_comp]
  rfl

def fieldInjective
    (raw : Term Const Γ (ConstructorPayloadTransport.Raw (number := number) (target := target) (children := children) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source))
    (domain : Term Const Γ (GuardedConstructorProjections.Admission number (Payload number source) children))
    (rawLaw : ProofSyntax Const Δ (ConstructorProjections.fieldInjective raw))
    (recover : Recovery Δ lower raise domain) :
    ProofSyntax Const Δ (GuardedConstructorProjections.fieldInjective (ConstructorPayloadTransport.constructor raw lower) domain) := by
  let Ω := children :: Payload number source :: number :: children :: Payload number source :: number :: Γ
  let rho : Rename Base Γ Ω := fun index => .vs (.vs (.vs (.vs (.vs (.vs index)))))
  let images : Subst Const Γ Ω := Subst.ofRename rho
  let firstTag : Term Const Ω number := .var (.vs (.vs (.vs (.vs (.vs .vz)))))
  let firstPayload : Term Const Ω (Payload number source) := .var (.vs (.vs (.vs (.vs .vz))))
  let firstChildren : Term Const Ω children := .var (.vs (.vs (.vs .vz)))
  let secondTag : Term Const Ω number := .var (.vs (.vs .vz))
  let secondPayload : Term Const Ω (Payload number source) := .var (.vs .vz)
  let secondChildren : Term Const Ω children := .var .vz
  let raisedDomain := HOL.subst images domain
  let first := GuardedConstructorProjections.admitted raisedDomain firstTag firstPayload firstChildren
  let second := GuardedConstructorProjections.admitted raisedDomain secondTag secondPayload secondChildren
  let same := Term.eq (ConstructorProjections.apply (HOL.subst images (ConstructorPayloadTransport.constructor raw lower)) secondTag secondPayload secondChildren)
    (ConstructorProjections.apply (HOL.subst images (ConstructorPayloadTransport.constructor raw lower)) firstTag firstPayload firstChildren)
  let assumptions := same :: second :: first :: Δ.map (HOL.subst images)
  let transport : ProofSyntax.OccurrenceMap (Δ.map (HOL.subst images)) assumptions :=
    { index := fun index => index.succ.succ.succ, get_eq := fun _ => rfl }
  have shiftedRaw : ProofSyntax Const assumptions (ConstructorProjections.fieldInjective (HOL.subst images raw)) :=
    ProofSyntax.castIndices rfl (ConstructorProjections.subst_fieldInjective images raw)
      (((rawLaw.subst images).prepend first).prepend second |>.prepend same)
  have firstRecovery := recover images transport firstTag firstPayload firstChildren (ProofSyntax.hyp 2)
  have secondRecovery := recover images transport secondTag secondPayload secondChildren (ProofSyntax.hyp 1)
  have sameProof : ProofSyntax Const assumptions (.eq
      (ConstructorProjections.apply (ConstructorPayloadTransport.constructor (HOL.subst images raw) (HOL.subst images lower))
        secondTag secondPayload secondChildren)
      (ConstructorProjections.apply (ConstructorPayloadTransport.constructor (HOL.subst images raw) (HOL.subst images lower))
        firstTag firstPayload firstChildren)) := by
    apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.hyp 0)
    change same = _
    dsimp only [same]
    rw [constructor_subst]
  have parts := ConstructorPayloadTransport.compareLowered (HOL.subst images raw) (HOL.subst images lower)
    firstTag secondTag firstPayload secondPayload firstChildren secondChildren shiftedRaw sameProof
  have recovered : ProofSyntax Const assumptions (.and (.eq secondPayload firstPayload) (.eq secondChildren firstChildren)) :=
    .andI (.eqTrans (.eqSymm secondRecovery)
      (.eqTrans (mapPayload_congr (HOL.subst images raise) _ _ (.andEL parts)) firstRecovery)) (.andER parts)
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  apply ProofSyntax.impI
  apply ProofSyntax.castIndices ?_ rfl recovered
  simp only [assumptions,same,second,first,raisedDomain,GuardedConstructorProjections.admitted,
    ConstructorProjections.apply,images,weakenHyps,List.map_cons,List.map_map,HOL.weaken,
    HOL.subst_ofRename,HOL.rename_comp,HOL.rename,rho,Rename.weaken,Function.comp_def]
  congr 1
  congr 1
  congr 1
  apply List.map_congr_left
  intro formula _
  exact HOL.subst_ofRename _ formula

theorem fieldInjective_free
    (raw : Term Const Γ (ConstructorPayloadTransport.Raw (number := number) (target := target) (children := children) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source))
    (domain : Term Const Γ (GuardedConstructorProjections.Admission number (Payload number source) children))
    (rawLaw : ProofSyntax Const Δ (ConstructorProjections.fieldInjective raw))
    (recover : Recovery Δ lower raise domain) (rawFree : rawLaw.FunctionExtensionalityFree) (recoverFree : recover.Free) :
    (fieldInjective raw lower raise domain rawLaw recover).FunctionExtensionalityFree := by
  unfold fieldInjective
  simp only [ProofSyntax.FunctionExtensionalityFree,ProofSyntax.functionExtensionalityFree_castIndices,
    ConstructorPayloadTransport.compareLowered_free,mapPayload_congr_free,
    ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_subst,
    rawFree]
  refine ⟨⟨?_,True.intro,?_⟩,True.intro⟩
  all_goals apply recoverFree; trivial

#print axioms fieldInjective
#print axioms fieldInjective_free
end Mettapedia.Logic.HOL.RepresentedConstructorAdmission
