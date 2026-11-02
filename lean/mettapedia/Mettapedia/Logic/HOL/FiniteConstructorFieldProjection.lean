import Mettapedia.Logic.HOL.FiniteConstructorReadout
import Mettapedia.Logic.HOL.ConstructorProjections

/-!
# Field projection from finite constructor payloads

A handler observes whether a selected field equals a candidate. Selection
from this predicate recovers that field on the actual encoded image. The
selection principle is an explicit retained proof input; no unrestricted
decoder law is assumed for the larger payload function space.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.FiniteConstructorFieldProjection
open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
    {type : Ty Base} {Δ : List (Formula Const Γ)}

theorem fieldHandler_subst (images : Subst Const Γ Ξ) {fields : List (Ty Base)}
    (index : Var fields type) (expected : Term Const Γ type) :
    subst images (fieldHandler index expected) = fieldHandler index (subst images expected) := by
  rw [fieldHandler, abstractArguments_subst _ _ _ (fieldBody_natural index expected)]
  apply congrArg (abstractArguments fields)
  funext laterContext later arguments
  simp only [subst_comp]
  rfl

theorem falseHandlers_subst (images : Subst Const Γ Ξ) (signature : List (List (Ty Base))) :
    substituteHandlers images signature (falseHandlers signature) = falseHandlers signature := by
  induction signature with
  | nil => rfl
  | cons fields rest ih =>
    change (subst images (abstractArguments fields (fun _ _ => .bot)),
      substituteHandlers images rest (falseHandlers rest)) =
      (abstractArguments fields (fun _ _ => .bot), falseHandlers rest)
    rw [abstractArguments_subst _ _ _ (by intro; intros; rfl), ih]

theorem withHandler_subst (images : Subst Const Γ Ξ) (signature : List (List (Ty Base)))
    (occurrence : Fin signature.length) (handler : Term Const Γ (handlerType (signature.get occurrence))) :
    substituteHandlers images signature (withHandler signature occurrence handler) =
      withHandler signature occurrence (subst images handler) := by
  induction signature with
  | nil => exact Fin.elim0 occurrence
  | cons fields rest ih =>
    rcases occurrence with ⟨index, bound⟩
    cases index with
    | zero => exact congrArg (fun tail => (subst images handler, tail)) (falseHandlers_subst images rest)
    | succ index =>
      change (subst images (abstractArguments fields (fun _ _ => .bot)),
        substituteHandlers images rest (withHandler rest ⟨index,Nat.lt_of_succ_lt_succ bound⟩ handler)) =
        (abstractArguments fields (fun _ _ => .bot),
          withHandler rest ⟨index,Nat.lt_of_succ_lt_succ bound⟩ (subst images handler))
      rw [abstractArguments_subst _ _ _ (by intro; intros; rfl), ih]

def query (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (index : Var (signature.get occurrence) type) (payload : Term Const Γ (payloadType signature))
    (candidate : Term Const Γ type) : Formula Const Γ :=
  observe signature payload (withHandler signature occurrence (fieldHandler index candidate))

theorem query_subst (images : Subst Const Γ Ξ) (signature : List (List (Ty Base)))
    (occurrence : Fin signature.length) (index : Var (signature.get occurrence) type)
    (payload : Term Const Γ (payloadType signature)) (candidate : Term Const Γ type) :
    subst images (query signature occurrence index payload candidate) =
      query signature occurrence index (subst images payload) (subst images candidate) := by
  simp only [query, observe_subst, withHandler_subst, fieldHandler_subst]

def body (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (index : Var (signature.get occurrence) type) (payload : Term Const Γ (payloadType signature)) :
    Formula Const (type :: Γ) := query signature occurrence index (weaken payload) (.var .vz)

theorem body_instantiate (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (index : Var (signature.get occurrence) type) (payload : Term Const Γ (payloadType signature))
    (candidate : Term Const Γ type) :
    instantiate candidate (body signature occurrence index payload) = query signature occurrence index payload candidate := by
  simp only [body, instantiate, query_subst, subst, Subst.single]
  exact congrArg (fun term => query signature occurrence index term candidate) (instantiate_weaken candidate payload)

def projection (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (index : Var (signature.get occurrence) type) (selection : Term Const Γ (SelectionProofs.Selection type)) :
    Term Const Γ (payloadType signature ⇒ type) :=
  .lam (SelectionProofs.selected (weaken selection) (body signature occurrence index (.var .vz)))

theorem body_subst (images : Subst Const Γ Ξ) (signature : List (List (Ty Base)))
    (occurrence : Fin signature.length) (index : Var (signature.get occurrence) type)
    (payload : Term Const Γ (payloadType signature)) :
    subst (Subst.lift images) (body signature occurrence index payload) =
      body signature occurrence index (subst images payload) := by
  simp only [body, query_subst, subst_weaken, subst, Subst.lift]

theorem projection_subst (images : Subst Const Γ Ξ) (signature : List (List (Ty Base)))
    (occurrence : Fin signature.length) (index : Var (signature.get occurrence) type)
    (selection : Term Const Γ (SelectionProofs.Selection type)) :
    subst images (projection signature occurrence index selection) =
      projection signature occurrence index (subst images selection) := by
  simp only [projection, SelectionProofs.selected, subst, subst_weaken, body_subst, Subst.lift]

def projection_apply (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (index : Var (signature.get occurrence) type) (selection : Term Const Γ (SelectionProofs.Selection type))
    (payload : Term Const Γ (payloadType signature)) :
    ProofSyntax Const Δ (.eq (.app (projection signature occurrence index selection) payload)
      (SelectionProofs.selected selection (body signature occurrence index payload))) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta payload
    (SelectionProofs.selected (weaken selection) (body signature occurrence index (.var .vz))))
  simp only [instantiate, SelectionProofs.selected, subst, body_subst, Subst.single]
  rw [show subst (Subst.single payload) (weaken selection) = selection from instantiate_weaken payload selection]
  rfl

theorem substituteArguments_shift (fields : List (Ty Base))
    (arguments : Arguments Const Γ fields) {bound : Ty Base} :
    substituteArguments (Subst.ofRename (Rename.weaken (σ := bound))) fields arguments =
      weakenArguments bound fields arguments := by
  induction fields with
  | nil => cases arguments; rfl
  | cons field rest ih =>
    change (subst (Subst.ofRename Rename.weaken) arguments.1, _) = _
    exact congrArg₂ Prod.mk (subst_ofRename Rename.weaken arguments.1) (ih arguments.2)

theorem weaken_encode (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (arguments : Arguments Const Γ (signature.get occurrence)) {bound : Ty Base} :
    weaken (σ := bound) (encode signature occurrence arguments) =
      encode signature occurrence (weakenArguments bound (signature.get occurrence) arguments) := by
  simpa only [weaken, subst_ofRename, substituteArguments_shift] using
    (encode_subst (Subst.ofRename (Rename.weaken (σ := bound))) signature occurrence arguments :
      subst (Subst.ofRename Rename.weaken) (encode signature occurrence arguments) = _)

theorem argumentAt_weaken {fields : List (Ty Base)} (index : Var fields type)
    (arguments : Arguments Const Γ fields) {bound : Ty Base} :
    argumentAt index (weakenArguments bound fields arguments) = weaken (argumentAt index arguments) := by
  induction index with
  | vz => rfl
  | vs index ih => exact ih arguments.2

def exists_at (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (index : Var (signature.get occurrence) type) (arguments : Arguments Const Γ (signature.get occurrence)) :
    ProofSyntax Const Δ (.ex (body signature occurrence index (encode signature occurrence arguments))) := by
  apply ProofSyntax.exI (argumentAt index arguments)
  apply ProofSyntax.castIndices rfl (body_instantiate signature occurrence index _ _).symm
  exact .impE (.eqPropER (observe_field signature occurrence index (argumentAt index arguments) arguments))
    (.eqRefl (argumentAt index arguments))

def unique_at (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (index : Var (signature.get occurrence) type) (arguments : Arguments Const Γ (signature.get occurrence)) :
    ProofSyntax Const Δ (.all (.imp (body signature occurrence index (encode signature occurrence arguments))
      (.eq (.var .vz) (weaken (argumentAt index arguments))))) := by
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  have observed := observe_field (Δ := body signature occurrence index (encode signature occurrence arguments) :: weakenHyps Δ)
    signature occurrence index (.var .vz) (weakenArguments type (signature.get occurrence) arguments)
  have checked : ProofSyntax Const (body signature occurrence index (encode signature occurrence arguments) :: weakenHyps Δ)
      (query signature occurrence index (encode signature occurrence (weakenArguments type _ arguments)) (.var .vz)) := by
    apply ProofSyntax.castIndices rfl ?_ (.hyp 0)
    exact congrArg (fun payload => query signature occurrence index payload (.var .vz)) (weaken_encode signature occurrence arguments)
  apply ProofSyntax.castIndices rfl ?_ (.eqSymm (.impE (.eqPropEL observed) checked))
  exact congrArg (Term.eq (.var .vz)) (argumentAt_weaken index arguments)

def projection_at (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (index : Var (signature.get occurrence) type) (selection : Term Const Γ (SelectionProofs.Selection type))
    (arguments : Arguments Const Γ (signature.get occurrence))
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection)) :
    ProofSyntax Const Δ (.eq (.app (projection signature occurrence index selection)
      (encode signature occurrence arguments)) (argumentAt index arguments)) :=
  .eqTrans (projection_apply signature occurrence index selection _)
    (ConstructorProjections.selected_eq selection _ _ choice
      (exists_at signature occurrence index arguments) (unique_at signature occurrence index arguments))

theorem projection_apply_free (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (index : Var (signature.get occurrence) type) (selection : Term Const Γ (SelectionProofs.Selection type))
    (payload : Term Const Γ (payloadType signature)) :
    (projection_apply (Δ := Δ) signature occurrence index selection payload).FunctionExtensionalityFree := by
  simp only [projection_apply, ProofSyntax.functionExtensionalityFree_castIndices,
    ProofSyntax.FunctionExtensionalityFree]

theorem exists_at_free (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (index : Var (signature.get occurrence) type) (arguments : Arguments Const Γ (signature.get occurrence)) :
    (exists_at (Δ := Δ) signature occurrence index arguments).FunctionExtensionalityFree := by
  simp only [exists_at, ProofSyntax.functionExtensionalityFree_castIndices,
    ProofSyntax.FunctionExtensionalityFree]
  exact ⟨observe_field_free signature occurrence index _ arguments, True.intro⟩

theorem unique_at_free (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (index : Var (signature.get occurrence) type) (arguments : Arguments Const Γ (signature.get occurrence)) :
    (unique_at (Δ := Δ) signature occurrence index arguments).FunctionExtensionalityFree := by
  simp only [unique_at, ProofSyntax.functionExtensionalityFree_castIndices,
    ProofSyntax.FunctionExtensionalityFree]
  exact ⟨observe_field_free signature occurrence index _ _, True.intro⟩

theorem projection_at_free (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (index : Var (signature.get occurrence) type) (selection : Term Const Γ (SelectionProofs.Selection type))
    (arguments : Arguments Const Γ (signature.get occurrence))
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (choiceFree : choice.FunctionExtensionalityFree) :
    (projection_at signature occurrence index selection arguments choice).FunctionExtensionalityFree := by
  exact ⟨projection_apply_free _ _ _ _ _,
    ConstructorProjections.selected_eq_free selection _ _ choice _ _ choiceFree
      (exists_at_free _ _ _ _) (unique_at_free _ _ _ _)⟩

#print axioms projection_at
#print axioms projection_at_free

end Mettapedia.Logic.HOL.FiniteConstructorFieldProjection
