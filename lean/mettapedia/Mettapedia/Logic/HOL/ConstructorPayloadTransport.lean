import Mettapedia.Logic.HOL.MixedConstructorPayloadMaps
import Mettapedia.Logic.HOL.CurriedFieldPrograms
import Mettapedia.Logic.HOL.ConstructorProjections

/-!
# Constructor recovery through a represented payload map

A genuine constructor on the target payload is precomposed with the field
map. Retained beta proofs expose that implementation. Equality reflects to
the original encoded source payload and children when both source fields
have recovery evidence. Target-constructor injectivity is a distinct provider
premise; no uniqueness law for the lifted constructor is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.ConstructorPayloadTransport
open FiniteConstructorEncoding CurriedPredicates MixedConstructorPayloadMaps
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
    {number source target children carrier : Ty Base} {Δ : List (Formula Const Γ)}

abbrev Raw := ConstructorProjections.Constructor number (Payload number target) children carrier
abbrev Lifted := ConstructorProjections.Constructor number (Payload number source) children carrier

def value (raw : Term Const Γ (Raw (number := number) (target := target) (children := children) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) (tag : Term Const Γ number)
    (payload : Term Const Γ (Payload number source)) (branches : Term Const Γ children) : Term Const Γ carrier :=
  ConstructorProjections.apply raw tag (mapPayload lower payload) branches

def body (raw : Term Const Γ (Raw (number := number) (target := target) (children := children) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) : FieldBody Const Γ [number,Payload number source,children] carrier :=
  fun images arguments => value (HOL.subst images raw) (HOL.subst images lower) arguments.1 arguments.2.1 arguments.2.2.1

theorem body_natural (raw : Term Const Γ (Raw (number := number) (target := target) (children := children) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) : NaturalFieldBody (body raw lower) := by
  intro Ξ Ω earlier later arguments
  simp only [body,value,ConstructorProjections.apply,HOL.subst,mapPayload_subst,HOL.subst_comp,substituteArguments]
  rfl

def constructor (raw : Term Const Γ (Raw (number := number) (target := target) (children := children) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) : Term Const Γ (Lifted (number := number) (source := source) (children := children) (carrier := carrier)) :=
  abstractFields [number,Payload number source,children] (body raw lower)

@[irreducible] def computation
    (raw : Term Const Γ (Raw (number := number) (target := target) (children := children) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) (tag : Term Const Γ number)
    (payload : Term Const Γ (Payload number source)) (branches : Term Const Γ children) :
    ProofSyntax Const Δ (.eq (ConstructorProjections.apply (constructor raw lower) tag payload branches)
      (value raw lower tag payload branches)) := by
  apply ProofSyntax.castIndices rfl ?_ (abstractFields_beta [number,Payload number source,children]
    (body raw lower) (body_natural raw lower) (tag,payload,branches,PUnit.unit))
  have identityTerm {type : Ty Base} (term : Term Const Γ type) : HOL.subst (fun index => .var index) term = term :=
    ProofSyntax.term_subst_of_identity (fun _ => rfl) term
  simp only [body,identityTerm,constructor,applyFields,ConstructorProjections.apply]

theorem computation_free
    (raw : Term Const Γ (Raw (number := number) (target := target) (children := children) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) (tag : Term Const Γ number)
    (payload : Term Const Γ (Payload number source)) (branches : Term Const Γ children) :
    (computation (Δ := Δ) raw lower tag payload branches).FunctionExtensionalityFree := by
  unfold computation
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact abstractFields_beta_free _ _ _ _

def compareLowered
    (raw : Term Const Γ (Raw (number := number) (target := target) (children := children) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) (firstTag secondTag : Term Const Γ number)
    (firstPayload secondPayload : Term Const Γ (Payload number source))
    (firstChildren secondChildren : Term Const Γ children)
    (rawInjective : ProofSyntax Const Δ (ConstructorProjections.fieldInjective raw))
    (same : ProofSyntax Const Δ (.eq
      (ConstructorProjections.apply (constructor raw lower) secondTag secondPayload secondChildren)
      (ConstructorProjections.apply (constructor raw lower) firstTag firstPayload firstChildren))) :
    ProofSyntax Const Δ (.and (.eq (mapPayload lower secondPayload) (mapPayload lower firstPayload))
      (.eq secondChildren firstChildren)) :=
  .impE (ConstructorProjections.compare raw firstTag secondTag
    (mapPayload lower firstPayload) (mapPayload lower secondPayload) firstChildren secondChildren
    (ConstructorProjections.specialize raw firstTag (mapPayload lower firstPayload) firstChildren rawInjective))
    (.eqTrans (.eqSymm (computation raw lower secondTag secondPayload secondChildren))
      (.eqTrans same (computation raw lower firstTag firstPayload firstChildren)))

theorem compareLowered_free
    (raw : Term Const Γ (Raw (number := number) (target := target) (children := children) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) (firstTag secondTag : Term Const Γ number)
    (firstPayload secondPayload : Term Const Γ (Payload number source))
    (firstChildren secondChildren : Term Const Γ children)
    (rawInjective : ProofSyntax Const Δ (ConstructorProjections.fieldInjective raw))
    (same : ProofSyntax Const Δ (.eq
      (ConstructorProjections.apply (constructor raw lower) secondTag secondPayload secondChildren)
      (ConstructorProjections.apply (constructor raw lower) firstTag firstPayload firstChildren)))
    (rawFree : rawInjective.FunctionExtensionalityFree) (sameFree : same.FunctionExtensionalityFree) :
    (compareLowered raw lower firstTag secondTag firstPayload secondPayload firstChildren secondChildren rawInjective same).FunctionExtensionalityFree := by
  unfold compareLowered
  refine ⟨?_,computation_free _ _ _ _ _,sameFree,computation_free _ _ _ _ _⟩
  simpa only [ConstructorProjections.compare,ConstructorProjections.specialize,
    ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree] using rawFree

def reflect
    (raw : Term Const Γ (Raw (number := number) (target := target) (children := children) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source))
    (firstTag secondTag firstIndex secondIndex : Term Const Γ number)
    (firstElement secondElement : Term Const Γ source) (firstShape secondShape : Term Const Γ number)
    (firstChildren secondChildren : Term Const Γ children)
    (rawInjective : ProofSyntax Const Δ (ConstructorProjections.fieldInjective raw))
    (firstRecovery : ProofSyntax Const Δ (.eq (.app raise (.app lower firstElement)) firstElement))
    (secondRecovery : ProofSyntax Const Δ (.eq (.app raise (.app lower secondElement)) secondElement))
    (same : ProofSyntax Const Δ (.eq
      (ConstructorProjections.apply (constructor raw lower) secondTag (pack secondIndex secondElement secondShape) secondChildren)
      (ConstructorProjections.apply (constructor raw lower) firstTag (pack firstIndex firstElement firstShape) firstChildren))) :
    ProofSyntax Const Δ (.and
      (.eq (pack secondIndex secondElement secondShape) (pack firstIndex firstElement firstShape))
      (.eq secondChildren firstChildren)) := by
  let firstPayload := pack firstIndex firstElement firstShape
  let secondPayload := pack secondIndex secondElement secondShape
  have parts := compareLowered raw lower firstTag secondTag firstPayload secondPayload firstChildren secondChildren rawInjective same
  exact .andI
    (.eqTrans (.eqSymm (roundtrip_at lower raise secondIndex secondElement secondShape secondRecovery))
      (.eqTrans (mapPayload_congr raise (mapPayload lower secondPayload) (mapPayload lower firstPayload) (.andEL parts))
        (roundtrip_at lower raise firstIndex firstElement firstShape firstRecovery)))
    (.andER parts)

theorem reflect_free
    (raw : Term Const Γ (Raw (number := number) (target := target) (children := children) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source))
    (firstTag secondTag firstIndex secondIndex : Term Const Γ number)
    (firstElement secondElement : Term Const Γ source) (firstShape secondShape : Term Const Γ number)
    (firstChildren secondChildren : Term Const Γ children)
    (rawInjective : ProofSyntax Const Δ (ConstructorProjections.fieldInjective raw))
    (firstRecovery : ProofSyntax Const Δ (.eq (.app raise (.app lower firstElement)) firstElement))
    (secondRecovery : ProofSyntax Const Δ (.eq (.app raise (.app lower secondElement)) secondElement))
    (same : ProofSyntax Const Δ (.eq
      (ConstructorProjections.apply (constructor raw lower) secondTag (pack secondIndex secondElement secondShape) secondChildren)
      (ConstructorProjections.apply (constructor raw lower) firstTag (pack firstIndex firstElement firstShape) firstChildren)))
    (rawFree : rawInjective.FunctionExtensionalityFree) (firstFree : firstRecovery.FunctionExtensionalityFree)
    (secondFree : secondRecovery.FunctionExtensionalityFree) (sameFree : same.FunctionExtensionalityFree) :
    (reflect raw lower raise firstTag secondTag firstIndex secondIndex firstElement secondElement firstShape secondShape
      firstChildren secondChildren rawInjective firstRecovery secondRecovery same).FunctionExtensionalityFree := by
  unfold reflect
  have partsFree := compareLowered_free raw lower firstTag secondTag
    (pack firstIndex firstElement firstShape) (pack secondIndex secondElement secondShape)
    firstChildren secondChildren rawInjective same rawFree sameFree
  exact ⟨⟨roundtrip_at_free _ _ _ _ _ _ secondFree,
    mapPayload_congr_free _ _ _ _ partsFree,roundtrip_at_free _ _ _ _ _ _ firstFree⟩,partsFree⟩

def fieldRecovery (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source))
    (valid : Term Const Γ (source ⇒ .prop)) (element : Term Const Γ source)
    (law : ProofSyntax Const Δ (GuardedRetraction.law lower raise valid))
    (permitted : ProofSyntax Const Δ (.app valid element)) :
    ProofSyntax Const Δ (.eq (.app raise (.app lower element)) element) := by
  have rule : ProofSyntax Const Δ (.imp (.app valid element) (.eq (.app raise (.app lower element)) element)) := by
    exact ProofSyntax.castIndices rfl (GuardedRetraction.instantiate_law lower raise valid element) (ProofSyntax.allE element law)
  exact .impE rule permitted

theorem fieldRecovery_free (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source))
    (valid : Term Const Γ (source ⇒ .prop)) (element : Term Const Γ source)
    (law : ProofSyntax Const Δ (GuardedRetraction.law lower raise valid))
    (permitted : ProofSyntax Const Δ (.app valid element))
    (lawFree : law.FunctionExtensionalityFree) (permittedFree : permitted.FunctionExtensionalityFree) :
    (fieldRecovery lower raise valid element law permitted).FunctionExtensionalityFree := by
  unfold fieldRecovery
  constructor
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact lawFree
  · exact permittedFree

def reflectGuarded
    (raw : Term Const Γ (Raw (number := number) (target := target) (children := children) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source))
    (valid : Term Const Γ (source ⇒ .prop))
    (firstTag secondTag firstIndex secondIndex : Term Const Γ number)
    (firstElement secondElement : Term Const Γ source) (firstShape secondShape : Term Const Γ number)
    (firstChildren secondChildren : Term Const Γ children)
    (rawInjective : ProofSyntax Const Δ (ConstructorProjections.fieldInjective raw))
    (law : ProofSyntax Const Δ (GuardedRetraction.law lower raise valid))
    (firstValid : ProofSyntax Const Δ (.app valid firstElement)) (secondValid : ProofSyntax Const Δ (.app valid secondElement))
    (same : ProofSyntax Const Δ (.eq
      (ConstructorProjections.apply (constructor raw lower) secondTag (pack secondIndex secondElement secondShape) secondChildren)
      (ConstructorProjections.apply (constructor raw lower) firstTag (pack firstIndex firstElement firstShape) firstChildren))) :
    ProofSyntax Const Δ (.and
      (.eq (pack secondIndex secondElement secondShape) (pack firstIndex firstElement firstShape))
      (.eq secondChildren firstChildren)) :=
  reflect raw lower raise firstTag secondTag firstIndex secondIndex firstElement secondElement firstShape secondShape
    firstChildren secondChildren rawInjective (fieldRecovery lower raise valid firstElement law firstValid)
    (fieldRecovery lower raise valid secondElement law secondValid) same

theorem reflectGuarded_free
    (raw : Term Const Γ (Raw (number := number) (target := target) (children := children) (carrier := carrier)))
    (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source))
    (valid : Term Const Γ (source ⇒ .prop))
    (firstTag secondTag firstIndex secondIndex : Term Const Γ number)
    (firstElement secondElement : Term Const Γ source) (firstShape secondShape : Term Const Γ number)
    (firstChildren secondChildren : Term Const Γ children)
    (rawInjective : ProofSyntax Const Δ (ConstructorProjections.fieldInjective raw))
    (law : ProofSyntax Const Δ (GuardedRetraction.law lower raise valid))
    (firstValid : ProofSyntax Const Δ (.app valid firstElement)) (secondValid : ProofSyntax Const Δ (.app valid secondElement))
    (same : ProofSyntax Const Δ (.eq
      (ConstructorProjections.apply (constructor raw lower) secondTag (pack secondIndex secondElement secondShape) secondChildren)
      (ConstructorProjections.apply (constructor raw lower) firstTag (pack firstIndex firstElement firstShape) firstChildren)))
    (rawFree : rawInjective.FunctionExtensionalityFree) (lawFree : law.FunctionExtensionalityFree)
    (firstFree : firstValid.FunctionExtensionalityFree) (secondFree : secondValid.FunctionExtensionalityFree)
    (sameFree : same.FunctionExtensionalityFree) :
    (reflectGuarded raw lower raise valid firstTag secondTag firstIndex secondIndex firstElement secondElement firstShape secondShape
      firstChildren secondChildren rawInjective law firstValid secondValid same).FunctionExtensionalityFree :=
  reflect_free _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rawFree
    (fieldRecovery_free _ _ _ _ _ _ lawFree firstFree)
    (fieldRecovery_free _ _ _ _ _ _ lawFree secondFree) sameFree

#print axioms computation_free
#print axioms reflect_free
#print axioms reflectGuarded_free
end Mettapedia.Logic.HOL.ConstructorPayloadTransport
