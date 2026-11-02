import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorCaseFromChildren
import Mettapedia.Logic.HOL.CurriedFieldPrograms
import Mettapedia.Logic.HOL.ConstantExpansionProofsFree

/-!
# A computed constructor at the original five source fields

The curried program retains length, leading child, payload, vector and
trailing child in source order. Its body uses the original encoded data and
constructed mixed child array. Retained beta proofs connect application to
that body, and the source allowed condition establishes its generated root
index. Neither raw injectivity nor an equation for an unrelated supplied
constructor is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorConstructorProgram
open Mettapedia.Logic Mettapedia.Logic.HOL
open IndexedContainerNativeVectorMethodReading (Base Const N E V W original constructorCarrier)
open IndexedContainerNativeVectorPositionReading
open IndexedContainerNativeVectorInactivePadding
open IndexedContainerNativeVectorActiveEdge
open IndexedContainerNativeVectorChildGuard
open IndexedContainerNativeVectorScopeTransport
open FiniteConstructorEncoding CurriedPredicates

attribute [local irreducible] IndexedConstructorGuards.ConstructorPrograms.rootIndex_intro

abbrev fields : List (Ty Base) := [N,E,E,V,E]
abbrev RawConstructor := N ⇒ payloadType [[N,E,N]] ⇒ (N ⇒ E) ⇒ E

variable {Γ Ξ : Ctx Base} {Δ : List (Formula Const Γ)}
    (elementSelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ E)))
    (arraySelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ V ⇒ N ⇒ E)))
    (payload : Term Const Γ (E ⇒ .prop)) (construct : Term Const Γ RawConstructor)
    (bottom : Term Const Γ E)

def body : FieldBody Const Γ fields E := fun {Ξ} images arguments =>
  ConstructorProjections.apply (HOL.subst images construct) (weakenCtx Ξ original.zero)
    (encoded (HOL.subst images payload) arguments.1 arguments.2.2.1 (weakenCtx Ξ original.zero))
    ((arrayOperations elementSelection arraySelection).mixed arguments.1 arguments.2.1 arguments.2.2.2.1
      arguments.2.2.2.2.1 (HOL.subst images bottom))

theorem body_natural : NaturalFieldBody (body elementSelection arraySelection payload construct bottom) := by
  intro Ξ Ω earlier later arguments
  simp only [body,ConstructorProjections.apply,HOL.subst,encoded_subst,
    VectorChildArrays.Operations.mixed_subst,subst_weakenCtx,HOL.subst_comp,substituteArguments]
  rw [HOL.subst_comp]
  rfl

def program : Term Const Γ constructorCarrier :=
  abstractFields fields (body elementSelection arraySelection payload construct bottom)

def applySource (function : Term Const Γ constructorCarrier)
    (length : Term Const Γ N) (before tag : Term Const Γ E) (vector : Term Const Γ V)
    (after : Term Const Γ E) : Term Const Γ E :=
  applyFields fields function (length,before,tag,vector,after,PUnit.unit)

def constructed (length : Term Const Γ N) (before tag : Term Const Γ E) (vector : Term Const Γ V)
    (after : Term Const Γ E) : Term Const Γ E :=
  ConstructorProjections.apply construct (weakenCtx Γ original.zero)
    (encoded payload length tag (weakenCtx Γ original.zero))
    ((arrayOperations elementSelection arraySelection).mixed length before vector after bottom)

def computation (length : Term Const Γ N) (before tag : Term Const Γ E) (vector : Term Const Γ V)
    (after : Term Const Γ E) : ProofSyntax Const Δ (.eq
      (applySource (program elementSelection arraySelection payload construct bottom) length before tag vector after)
      (constructed elementSelection arraySelection payload construct bottom length before tag vector after)) := by
  apply ProofSyntax.castIndices rfl ?_
    (abstractFields_beta fields (body elementSelection arraySelection payload construct bottom)
      (body_natural elementSelection arraySelection payload construct bottom)
      (length,before,tag,vector,after,PUnit.unit))
  have identityTerm {type : Ty Base} (term : Term Const Γ type) :
      HOL.subst (fun index => .var index) term = term :=
    ProofSyntax.term_subst_of_identity (fun _ => rfl) term
  simp only [body,identityTerm,applySource,program,constructed]
  rw [identityTerm payload]

theorem computation_free (length : Term Const Γ N) (before tag : Term Const Γ E) (vector : Term Const Γ V)
    (after : Term Const Γ E) :
    (computation (Δ := Δ) elementSelection arraySelection payload construct bottom length before tag vector after).FunctionExtensionalityFree := by
  unfold computation
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact abstractFields_beta_free _ _ _ _

theorem program_subst (images : Subst Const Γ Ξ) :
    HOL.subst images (program elementSelection arraySelection payload construct bottom) =
      program elementSelection arraySelection (HOL.subst images payload) (HOL.subst images construct)
        (HOL.subst images bottom) := by
  rw [program,abstractFields_subst _ _ _ (body_natural elementSelection arraySelection payload construct bottom)]
  apply congrArg (abstractFields fields)
  funext laterContext later arguments
  simp only [body,HOL.subst_comp]
  rfl

@[irreducible] def resultIndex (length : Term Const Γ N) (tag : Term Const Γ E) :
    ProofSyntax Const Δ (.eq (applyFields _ ((constructors payload).result (occurrence payload))
      (sourceArguments payload length tag (weakenCtx Γ original.zero))) .top) :=
  reading.resultProof code (parameterMap payload) (arguments length tag (weakenCtx Γ original.zero))

theorem resultIndex_free (length : Term Const Γ N) (tag : Term Const Γ E) :
    (resultIndex (Δ := Δ) payload length tag).FunctionExtensionalityFree :=
  by
    unfold resultIndex
    exact reading.resultProof_free code (parameterMap payload) (arguments length tag (weakenCtx Γ original.zero))

@[irreducible] def rootIndex (length : Term Const Γ N) (before tag : Term Const Γ E) (vector : Term Const Γ V)
    (after : Term Const Γ E)
    (allowed : ProofSyntax Const Δ (sourceAllowed payload length tag (weakenCtx Γ original.zero))) :
    ProofSyntax Const Δ ((constructors payload).rootIndex construct
      (constructed elementSelection arraySelection payload construct bottom length before tag vector after) .top) :=
  (constructors payload).rootIndex_intro construct (occurrence payload)
    (sourceArguments payload length tag (weakenCtx Γ original.zero))
    ((arrayOperations elementSelection arraySelection).mixed length before vector after bottom) .top allowed
    (resultIndex payload length tag)

set_option backward.isDefEq.respectTransparency true in
theorem rootIndex_free (length : Term Const Γ N) (before tag : Term Const Γ E) (vector : Term Const Γ V)
    (after : Term Const Γ E)
    (allowed : ProofSyntax Const Δ (sourceAllowed payload length tag (weakenCtx Γ original.zero)))
    (free : allowed.FunctionExtensionalityFree) :
    (rootIndex elementSelection arraySelection payload construct bottom length before tag vector after allowed).FunctionExtensionalityFree := by
  unfold rootIndex
  exact (constructors payload).rootIndex_intro_free construct (occurrence payload)
    (sourceArguments payload length tag (weakenCtx Γ original.zero))
    ((arrayOperations elementSelection arraySelection).mixed length before vector after bottom) .top
    allowed (resultIndex payload length tag) free (resultIndex_free payload length tag)

#print axioms computation_free
#print axioms program_subst
#print axioms resultIndex_free
#print axioms rootIndex_free
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorConstructorProgram
