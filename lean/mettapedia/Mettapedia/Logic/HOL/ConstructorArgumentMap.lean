import Mettapedia.Logic.HOL.CurriedFieldPrograms
import Mettapedia.Logic.HOL.GuardedConstructorProjectionProofs

/-!
# Constructor transport through an arbitrary typed argument map

The second argument is mapped by an actual HOL function. Retained beta
proofs expose the wrapper, and recovery on the admitted argument relation
reflects raw equality to the original payload and children. The payload
types need no particular finite-constructor encoding.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.ConstructorArgumentMap
open FiniteConstructorEncoding CurriedPredicates
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
  {first source target third carrier : Ty Base} {Δ : List (Formula Const Γ)}

abbrev Raw := ConstructorProjections.Constructor first target third carrier
abbrev Mapped := ConstructorProjections.Constructor first source third carrier

def value (raw : Term Const Γ (Raw (first := first) (target := target) (third := third) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) (a : Term Const Γ first)
    (payload : Term Const Γ source) (children : Term Const Γ third) : Term Const Γ carrier :=
  ConstructorProjections.apply raw a (.app lower payload) children

def body (raw : Term Const Γ (Raw (first := first) (target := target) (third := third) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) : FieldBody Const Γ [first,source,third] carrier :=
  fun images arguments => value (subst images raw) (subst images lower) arguments.1 arguments.2.1 arguments.2.2.1

theorem body_natural (raw : Term Const Γ (Raw (first := first) (target := target) (third := third) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) : NaturalFieldBody (body raw lower) := by
  intro Ξ Ω earlier later arguments
  simp only [body,value,ConstructorProjections.apply,HOL.subst,HOL.subst_comp,substituteArguments]
  rfl

def constructor (raw : Term Const Γ (Raw (first := first) (target := target) (third := third) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) :
    Term Const Γ (Mapped (first := first) (source := source) (third := third) (carrier := carrier)) :=
  abstractFields [first,source,third] (body raw lower)

theorem constructor_subst (raw : Term Const Γ (Raw (first := first) (target := target) (third := third) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) (images : Subst Const Γ Ξ) :
    subst images (constructor raw lower) = constructor (subst images raw) (subst images lower) := by
  rw [constructor,abstractFields_subst _ _ _ (body_natural raw lower)]
  apply congrArg (abstractFields [first,source,third])
  funext Ω later arguments
  simp only [body,value,ConstructorProjections.apply,HOL.subst_comp]
  rfl

def computation (raw : Term Const Γ (Raw (first := first) (target := target) (third := third) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) (a : Term Const Γ first)
    (payload : Term Const Γ source) (children : Term Const Γ third) :
    ProofSyntax Const Δ (.eq (ConstructorProjections.apply (constructor raw lower) a payload children)
      (value raw lower a payload children)) := by
  apply ProofSyntax.castIndices rfl ?_ (abstractFields_beta [first,source,third]
    (body raw lower) (body_natural raw lower) (a,payload,children,PUnit.unit))
  have identity {type : Ty Base} (term : Term Const Γ type) :
      subst (fun {type} (index : Var Γ type) => Term.var index) term = term := subst_id term
  simp only [body,identity,constructor,applyFields,ConstructorProjections.apply]

theorem computation_free (raw : Term Const Γ (Raw (first := first) (target := target) (third := third) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) (a : Term Const Γ first)
    (payload : Term Const Γ source) (children : Term Const Γ third) :
    (computation (Δ := Δ) raw lower a payload children).FunctionExtensionalityFree := by
  unfold computation
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr (abstractFields_beta_free _ _ _ _)

def compareLowered
    (raw : Term Const Γ (Raw (first := first) (target := target) (third := third) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) (a b : Term Const Γ first)
    (payload otherPayload : Term Const Γ source) (children otherChildren : Term Const Γ third)
    (rawLaw : ProofSyntax Const Δ (ConstructorProjections.fieldInjective raw))
    (same : ProofSyntax Const Δ (.eq
      (ConstructorProjections.apply (constructor raw lower) b otherPayload otherChildren)
      (ConstructorProjections.apply (constructor raw lower) a payload children))) :
    ProofSyntax Const Δ (.and (.eq (.app lower otherPayload) (.app lower payload)) (.eq otherChildren children)) :=
  .impE (ConstructorProjections.compare raw a b (.app lower payload) (.app lower otherPayload) children otherChildren
    (ConstructorProjections.specialize raw a (.app lower payload) children rawLaw))
    (.eqTrans (.eqSymm (computation raw lower b otherPayload otherChildren))
      (.eqTrans same (computation raw lower a payload children)))

theorem compareLowered_free
    (raw : Term Const Γ (Raw (first := first) (target := target) (third := third) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) (a b : Term Const Γ first)
    (payload otherPayload : Term Const Γ source) (children otherChildren : Term Const Γ third)
    (rawLaw : ProofSyntax Const Δ (ConstructorProjections.fieldInjective raw))
    (same : ProofSyntax Const Δ (.eq
      (ConstructorProjections.apply (constructor raw lower) b otherPayload otherChildren)
      (ConstructorProjections.apply (constructor raw lower) a payload children)))
    (rawFree : rawLaw.FunctionExtensionalityFree) (sameFree : same.FunctionExtensionalityFree) :
    (compareLowered raw lower a b payload otherPayload children otherChildren rawLaw same).FunctionExtensionalityFree := by
  unfold compareLowered
  refine ⟨?_,computation_free _ _ _ _ _,sameFree,computation_free _ _ _ _ _⟩
  simpa only [ConstructorProjections.compare,ConstructorProjections.specialize,
    ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree] using rawFree

def reflect
    (raw : Term Const Γ (Raw (first := first) (target := target) (third := third) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source))
    (a b : Term Const Γ first) (payload otherPayload : Term Const Γ source)
    (children otherChildren : Term Const Γ third)
    (rawLaw : ProofSyntax Const Δ (ConstructorProjections.fieldInjective raw))
    (recovery : ProofSyntax Const Δ (.eq (.app raise (.app lower payload)) payload))
    (otherRecovery : ProofSyntax Const Δ (.eq (.app raise (.app lower otherPayload)) otherPayload))
    (same : ProofSyntax Const Δ (.eq
      (ConstructorProjections.apply (constructor raw lower) b otherPayload otherChildren)
      (ConstructorProjections.apply (constructor raw lower) a payload children))) :
    ProofSyntax Const Δ (.and (.eq otherPayload payload) (.eq otherChildren children)) := by
  have compared := compareLowered raw lower a b payload otherPayload children otherChildren rawLaw same
  exact .andI (.eqTrans (.eqSymm otherRecovery)
    (.eqTrans (.eqAppArg raise (.andEL compared)) recovery)) (.andER compared)

def Recovery (premises : List (Formula Const Γ))
    (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source))
    (domain : Term Const Γ (GuardedConstructorProjections.Admission first source third)) :=
  ∀ {Ξ : Ctx Base} (images : Subst Const Γ Ξ) {assumptions : List (Formula Const Ξ)}
    (_transport : ProofSyntax.OccurrenceMap (premises.map (HOL.subst images)) assumptions)
    (tag : Term Const Ξ first) (payload : Term Const Ξ source) (branches : Term Const Ξ third),
    ProofSyntax Const assumptions (GuardedConstructorProjections.admitted (HOL.subst images domain) tag payload branches) →
    ProofSyntax Const assumptions (.eq
      (.app (HOL.subst images raise) (.app (HOL.subst images lower) payload)) payload)

def Recovery.Free {premises : List (Formula Const Γ)}
    {lower : Term Const Γ (source ⇒ target)} {raise : Term Const Γ (target ⇒ source)}
    {domain : Term Const Γ (GuardedConstructorProjections.Admission first source third)}
    (recover : Recovery premises lower raise domain) : Prop :=
  ∀ {Ξ : Ctx Base} (images : Subst Const Γ Ξ) {assumptions : List (Formula Const Ξ)}
    (transport : ProofSyntax.OccurrenceMap (premises.map (HOL.subst images)) assumptions)
    (tag : Term Const Ξ first) (payload : Term Const Ξ source) (branches : Term Const Ξ third)
    (present : ProofSyntax Const assumptions (GuardedConstructorProjections.admitted (HOL.subst images domain) tag payload branches)),
    present.FunctionExtensionalityFree → (recover images transport tag payload branches present).FunctionExtensionalityFree

def fieldInjective
    (raw : Term Const Γ (Raw (first := first) (target := target) (third := third) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source))
    (domain : Term Const Γ (GuardedConstructorProjections.Admission first source third))
    (rawLaw : ProofSyntax Const Δ (ConstructorProjections.fieldInjective raw))
    (recover : Recovery Δ lower raise domain) :
    ProofSyntax Const Δ (GuardedConstructorProjections.fieldInjective (constructor raw lower) domain) := by
  let Ω := third :: source :: first :: third :: source :: first :: Γ
  let rho : Rename Base Γ Ω := fun index => .vs (.vs (.vs (.vs (.vs (.vs index)))))
  let images : Subst Const Γ Ω := Subst.ofRename rho
  let firstTag : Term Const Ω first := .var (.vs (.vs (.vs (.vs (.vs .vz)))))
  let firstPayload : Term Const Ω source := .var (.vs (.vs (.vs (.vs .vz))))
  let firstChildren : Term Const Ω third := .var (.vs (.vs (.vs .vz)))
  let secondTag : Term Const Ω first := .var (.vs (.vs .vz))
  let secondPayload : Term Const Ω source := .var (.vs .vz)
  let secondChildren : Term Const Ω third := .var .vz
  let raisedDomain := HOL.subst images domain
  let first := GuardedConstructorProjections.admitted raisedDomain firstTag firstPayload firstChildren
  let second := GuardedConstructorProjections.admitted raisedDomain secondTag secondPayload secondChildren
  let same := Term.eq (ConstructorProjections.apply (HOL.subst images (constructor raw lower)) secondTag secondPayload secondChildren)
    (ConstructorProjections.apply (HOL.subst images (constructor raw lower)) firstTag firstPayload firstChildren)
  let assumptions := same :: second :: first :: Δ.map (HOL.subst images)
  let transport : ProofSyntax.OccurrenceMap (Δ.map (HOL.subst images)) assumptions :=
    { index := fun index => index.succ.succ.succ, get_eq := fun _ => rfl }
  have shiftedRaw : ProofSyntax Const assumptions (ConstructorProjections.fieldInjective (HOL.subst images raw)) :=
    ProofSyntax.castIndices rfl (ConstructorProjections.subst_fieldInjective images raw)
      (((rawLaw.subst images).prepend first).prepend second |>.prepend same)
  have firstRecovery := recover images transport firstTag firstPayload firstChildren (ProofSyntax.hyp 2)
  have secondRecovery := recover images transport secondTag secondPayload secondChildren (ProofSyntax.hyp 1)
  have sameProof : ProofSyntax Const assumptions (.eq
      (ConstructorProjections.apply (constructor (HOL.subst images raw) (HOL.subst images lower))
        secondTag secondPayload secondChildren)
      (ConstructorProjections.apply (constructor (HOL.subst images raw) (HOL.subst images lower))
        firstTag firstPayload firstChildren)) := by
    apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.hyp 0)
    change same = _
    dsimp only [same]
    rw [constructor_subst]
  have parts := compareLowered (HOL.subst images raw) (HOL.subst images lower)
    firstTag secondTag firstPayload secondPayload firstChildren secondChildren shiftedRaw sameProof
  have recovered : ProofSyntax Const assumptions (.and (.eq secondPayload firstPayload) (.eq secondChildren firstChildren)) :=
    .andI (.eqTrans (.eqSymm secondRecovery)
      (.eqTrans (.eqAppArg (HOL.subst images raise) (.andEL parts)) firstRecovery)) (.andER parts)
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
    (raw : Term Const Γ (Raw (first := first) (target := target) (third := third) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source))
    (domain : Term Const Γ (GuardedConstructorProjections.Admission first source third))
    (rawLaw : ProofSyntax Const Δ (ConstructorProjections.fieldInjective raw))
    (recover : Recovery Δ lower raise domain) (rawFree : rawLaw.FunctionExtensionalityFree) (recoverFree : recover.Free) :
    (fieldInjective raw lower raise domain rawLaw recover).FunctionExtensionalityFree := by
  unfold fieldInjective
  simp only [ProofSyntax.FunctionExtensionalityFree,ProofSyntax.functionExtensionalityFree_castIndices,
    compareLowered_free,
    ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_subst,
    rawFree]
  refine ⟨⟨?_,True.intro,?_⟩,True.intro⟩
  all_goals apply recoverFree; trivial

#print axioms fieldInjective
#print axioms fieldInjective_free
#print axioms computation
#print axioms compareLowered
#print axioms reflect
end Mettapedia.Logic.HOL.ConstructorArgumentMap
