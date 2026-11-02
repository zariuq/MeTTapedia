import Mettapedia.Logic.HOL.FunctionArrayPrepend
import Mettapedia.Logic.HOL.VectorRecursionProofs
import Mettapedia.Logic.HOL.IndexedVectorPredicate

/-!
# Function arrays containing a vector followed by a supplied suffix

The array is an actual HOL term built from the existing selected natural and
vector recursors. Element-valued prepend and array-valued vector recursion
retain their distinct selection and recursion instances. Constructor equations
are derived from the original head/tail projections. A mixed child array has
one leading child, the vector's children, one trailing child and constant padding.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.VectorChildArrays
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

structure Operations (Const : Ty Base → Type v) extends IndexedVectorPredicate.Signature Const where
  head : ClosedTerm Const (vector ⇒ element)
  tail : ClosedTerm Const (vector ⇒ vector)
  elementSelection : ClosedTerm Const (SelectionProofs.Selection (number ⇒ element))
  arraySelection : ClosedTerm Const (SelectionProofs.Selection (number ⇒ vector ⇒ number ⇒ element))

namespace Operations
variable (ops : Operations Const) {Γ Ξ : Ctx Base}

abbrev ArrayType := ops.number ⇒ ops.element

def prepend (first : Term Const Γ ops.element) (rest : Term Const Γ ops.ArrayType) :
    Term Const Γ ops.ArrayType :=
  FunctionArrayPrepend.prepend (weakenCtx Γ ops.elementSelection)
    (weakenCtx Γ ops.zero) (weakenCtx Γ ops.successor) first rest

@[simp] theorem prepend_subst (images : Subst Const Γ Ξ)
    (first : Term Const Γ ops.element) (rest : Term Const Γ ops.ArrayType) :
    HOL.subst images (ops.prepend first rest) = ops.prepend (HOL.subst images first) (HOL.subst images rest) := by
  simp only [prepend, FunctionArrayPrepend.prepend_subst, subst_weakenCtx]

def afterHead (head : Term Const Γ ops.element) :
    Term Const Γ (ops.vector ⇒ ops.ArrayType ⇒ ops.ArrayType) :=
  .lam (.lam (ops.prepend (weaken (weaken head)) (.var .vz)))

@[simp] theorem afterHead_subst (images : Subst Const Γ Ξ) (head : Term Const Γ ops.element) :
    HOL.subst images (ops.afterHead head) = ops.afterHead (HOL.subst images head) := by
  simp only [afterHead, HOL.subst, prepend_subst, subst_weaken, Subst.lift]

def afterIndex : Term Const Γ (ops.element ⇒ ops.vector ⇒ ops.ArrayType ⇒ ops.ArrayType) :=
  .lam (ops.afterHead (.var .vz))

@[simp] theorem afterIndex_subst (images : Subst Const Γ Ξ) :
    HOL.subst images (ops.afterIndex (Γ := Γ)) = ops.afterIndex (Γ := Ξ) := by
  simp only [afterIndex, HOL.subst, afterHead_subst, Subst.lift]

def method : Term Const Γ (VectorRecursionProofs.Method ops.number ops.element ops.vector ops.ArrayType) :=
  .lam ops.afterIndex

@[simp] theorem method_subst (images : Subst Const Γ Ξ) :
    HOL.subst images (ops.method (Γ := Γ)) = ops.method (Γ := Ξ) := by
  simp only [method, HOL.subst, afterIndex_subst]

def recursor (rest : Term Const Γ ops.ArrayType) : Term Const Γ (ops.number ⇒ ops.vector ⇒ ops.ArrayType) :=
  VectorRecursionProofs.recursor (weakenCtx Γ ops.arraySelection) (weakenCtx Γ ops.zero)
    (weakenCtx Γ ops.successor) (weakenCtx Γ ops.head) (weakenCtx Γ ops.tail) rest ops.method

@[simp] theorem recursor_subst (images : Subst Const Γ Ξ) (rest : Term Const Γ ops.ArrayType) :
    HOL.subst images (ops.recursor rest) = ops.recursor (HOL.subst images rest) := by
  simp only [recursor, VectorRecursionProofs.subst_recursor, subst_weakenCtx, method_subst]

def suffix (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector)
    (rest : Term Const Γ ops.ArrayType) : Term Const Γ ops.ArrayType :=
  .app (.app (ops.recursor rest) index) vector

@[simp] theorem suffix_subst (images : Subst Const Γ Ξ)
    (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector) (rest : Term Const Γ ops.ArrayType) :
    HOL.subst images (ops.suffix index vector rest) =
      ops.suffix (HOL.subst images index) (HOL.subst images vector) (HOL.subst images rest) := by
  simp only [suffix, HOL.subst, recursor_subst]

def padding (bottom : Term Const Γ ops.element) : Term Const Γ ops.ArrayType := .lam (weaken bottom)

@[simp] theorem padding_subst (images : Subst Const Γ Ξ) (bottom : Term Const Γ ops.element) :
    HOL.subst images (ops.padding bottom) = ops.padding (HOL.subst images bottom) := by
  simp only [padding, HOL.subst, subst_weaken]

def mixed (index : Term Const Γ ops.number) (before : Term Const Γ ops.element)
    (vector : Term Const Γ ops.vector) (after bottom : Term Const Γ ops.element) :
    Term Const Γ ops.ArrayType :=
  ops.prepend before (ops.suffix index vector (ops.prepend after (ops.padding bottom)))

@[simp] theorem mixed_subst (images : Subst Const Γ Ξ)
    (index : Term Const Γ ops.number) (before : Term Const Γ ops.element)
    (vector : Term Const Γ ops.vector) (after bottom : Term Const Γ ops.element) :
    HOL.subst images (ops.mixed index before vector after bottom) =
      ops.mixed (HOL.subst images index) (HOL.subst images before) (HOL.subst images vector)
        (HOL.subst images after) (HOL.subst images bottom) := by
  simp only [mixed, prepend_subst, suffix_subst, padding_subst]

@[simp] theorem mixed_rename (rho : Rename Base Γ Ξ)
    (index : Term Const Γ ops.number) (before : Term Const Γ ops.element)
    (vector : Term Const Γ ops.vector) (after bottom : Term Const Γ ops.element) :
    HOL.rename rho (ops.mixed index before vector after bottom) =
      ops.mixed (HOL.rename rho index) (HOL.rename rho before) (HOL.rename rho vector)
        (HOL.rename rho after) (HOL.rename rho bottom) := by
  simpa only [subst_ofRename] using ops.mixed_subst (Subst.ofRename rho) index before vector after bottom

variable {Δ : List (Formula Const Γ)}

def method_apply (index : Term Const Γ ops.number) (head : Term Const Γ ops.element)
    (tail : Term Const Γ ops.vector) (recursive : Term Const Γ ops.ArrayType) :
    ProofSyntax Const Δ (.eq (.app (.app (.app (.app ops.method index) head) tail) recursive)
      (ops.prepend head recursive)) := by
  have first : ProofSyntax Const Δ (.eq (.app ops.method index) ops.afterIndex) := by
    apply ProofSyntax.castIndices rfl ?_ (.beta index ops.afterIndex)
    simp only [method, instantiate, afterIndex_subst]
  have second : ProofSyntax Const Δ (.eq (.app ops.afterIndex head) (ops.afterHead head)) := by
    apply ProofSyntax.castIndices rfl ?_ (.beta head (ops.afterHead (.var .vz)))
    simp only [afterIndex, instantiate, afterHead_subst, HOL.subst, Subst.single]
  have third : ProofSyntax Const Δ (.eq (.app (ops.afterHead head) tail)
      (.lam (ops.prepend (weaken head) (.var .vz)))) := by
    have cancel : HOL.subst (Subst.single tail) (weaken head) = head := instantiate_weaken tail head
    apply ProofSyntax.castIndices rfl ?_ (.beta tail (.lam (ops.prepend (weaken (weaken head)) (.var .vz))))
    simp only [afterHead, instantiate, HOL.subst, prepend_subst, subst_weaken, Subst.lift, cancel]
  have fourth : ProofSyntax Const Δ (.eq
      (.app (.lam (ops.prepend (weaken head) (.var .vz))) recursive) (ops.prepend head recursive)) := by
    have cancel : HOL.subst (Subst.single recursive) (weaken head) = head := instantiate_weaken recursive head
    apply ProofSyntax.castIndices rfl ?_ (.beta recursive (ops.prepend (weaken head) (.var .vz)))
    simp only [instantiate, prepend_subst, cancel, HOL.subst, Subst.single]
  exact .eqTrans (.eqApp recursive (.eqApp tail (.eqApp head first)))
    (.eqTrans (.eqApp recursive (.eqApp tail second)) (.eqTrans (.eqApp recursive third) fourth))

theorem method_apply_free (index : Term Const Γ ops.number) (head : Term Const Γ ops.element)
    (tail : Term Const Γ ops.vector) (recursive : Term Const Γ ops.ArrayType) :
    (ops.method_apply (Δ := Δ) index head tail recursive).FunctionExtensionalityFree := by
  simp [method_apply, ProofSyntax.FunctionExtensionalityFree]

def suffix_zero (vector : Term Const Γ ops.vector) (rest : Term Const Γ ops.ArrayType)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ ops.arraySelection)))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement (weakenCtx Γ ops.zero)
      (weakenCtx Γ ops.successor) (ops.vector ⇒ ops.ArrayType))) :
    ProofSyntax Const Δ (.eq (ops.suffix (weakenCtx Γ ops.zero) vector rest) rest) :=
  VectorRecursionProofs.atZero (weakenCtx Γ ops.arraySelection) (weakenCtx Γ ops.zero)
    (weakenCtx Γ ops.successor) (weakenCtx Γ ops.head) (weakenCtx Γ ops.tail) rest ops.method vector choice recursion

def suffix_cons (index : Term Const Γ ops.number) (head : Term Const Γ ops.element)
    (tail : Term Const Γ ops.vector) (rest : Term Const Γ ops.ArrayType)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ ops.arraySelection)))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement (weakenCtx Γ ops.zero)
      (weakenCtx Γ ops.successor) (ops.vector ⇒ ops.ArrayType)))
    (headProof : ProofSyntax Const Δ (.eq (.app (weakenCtx Γ ops.head)
      (ops.toSignature.consValue index head tail)) head))
    (tailProof : ProofSyntax Const Δ (.eq (.app (weakenCtx Γ ops.tail)
      (ops.toSignature.consValue index head tail)) tail)) :
    ProofSyntax Const Δ (.eq (ops.suffix (.app (weakenCtx Γ ops.successor) index)
      (ops.toSignature.consValue index head tail) rest) (ops.prepend head (ops.suffix index tail rest))) :=
  .eqTrans (VectorRecursionProofs.atCons (weakenCtx Γ ops.arraySelection) (weakenCtx Γ ops.zero)
    (weakenCtx Γ ops.successor) (weakenCtx Γ ops.head) (weakenCtx Γ ops.tail) (weakenCtx Γ ops.cons)
    rest ops.method index head tail choice recursion headProof tailProof)
    (ops.method_apply index head tail (ops.suffix index tail rest))

theorem suffix_zero_free (vector : Term Const Γ ops.vector) (rest : Term Const Γ ops.ArrayType)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ ops.arraySelection)))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement (weakenCtx Γ ops.zero)
      (weakenCtx Γ ops.successor) (ops.vector ⇒ ops.ArrayType)))
    (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree) :
    (ops.suffix_zero vector rest choice recursion).FunctionExtensionalityFree :=
  VectorRecursionProofs.atZero_free _ _ _ _ _ _ _ _ choice recursion choiceFree recursionFree

theorem suffix_cons_free (index : Term Const Γ ops.number) (head : Term Const Γ ops.element)
    (tail : Term Const Γ ops.vector) (rest : Term Const Γ ops.ArrayType)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ ops.arraySelection)))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement (weakenCtx Γ ops.zero)
      (weakenCtx Γ ops.successor) (ops.vector ⇒ ops.ArrayType)))
    (headProof : ProofSyntax Const Δ (.eq (.app (weakenCtx Γ ops.head)
      (ops.toSignature.consValue index head tail)) head))
    (tailProof : ProofSyntax Const Δ (.eq (.app (weakenCtx Γ ops.tail)
      (ops.toSignature.consValue index head tail)) tail))
    (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree)
    (headFree : headProof.FunctionExtensionalityFree) (tailFree : tailProof.FunctionExtensionalityFree) :
    (ops.suffix_cons index head tail rest choice recursion headProof tailProof).FunctionExtensionalityFree :=
  ⟨VectorRecursionProofs.atCons_free _ _ _ _ _ _ _ _ _ _ _ choice recursion headProof tailProof
    choiceFree recursionFree headFree tailFree, ops.method_apply_free _ _ _ _⟩

def prepend_zero (first : Term Const Γ ops.element) (rest : Term Const Γ ops.ArrayType)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ ops.elementSelection)))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement (weakenCtx Γ ops.zero)
      (weakenCtx Γ ops.successor) ops.element)) :
    ProofSyntax Const Δ (.eq (.app (ops.prepend first rest) (weakenCtx Γ ops.zero)) first) :=
  FunctionArrayPrepend.atZero _ _ _ first rest choice recursion

def prepend_successor (first : Term Const Γ ops.element) (rest : Term Const Γ ops.ArrayType)
    (index : Term Const Γ ops.number)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ ops.elementSelection)))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement (weakenCtx Γ ops.zero)
      (weakenCtx Γ ops.successor) ops.element)) :
    ProofSyntax Const Δ (.eq (.app (ops.prepend first rest) (.app (weakenCtx Γ ops.successor) index))
      (.app rest index)) :=
  FunctionArrayPrepend.atSuccessor _ _ _ first rest index choice recursion

theorem prepend_zero_free (first : Term Const Γ ops.element) (rest : Term Const Γ ops.ArrayType)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ ops.elementSelection)))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement (weakenCtx Γ ops.zero)
      (weakenCtx Γ ops.successor) ops.element))
    (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree) :
    (ops.prepend_zero first rest choice recursion).FunctionExtensionalityFree :=
  FunctionArrayPrepend.atZero_free _ _ _ first rest choice recursion choiceFree recursionFree

theorem prepend_successor_free (first : Term Const Γ ops.element) (rest : Term Const Γ ops.ArrayType)
    (index : Term Const Γ ops.number)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ ops.elementSelection)))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement (weakenCtx Γ ops.zero)
      (weakenCtx Γ ops.successor) ops.element))
    (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree) :
    (ops.prepend_successor first rest index choice recursion).FunctionExtensionalityFree :=
  FunctionArrayPrepend.atSuccessor_free _ _ _ first rest index choice recursion choiceFree recursionFree

def padding_apply (bottom : Term Const Γ ops.element) (index : Term Const Γ ops.number) :
    ProofSyntax Const Δ (.eq (.app (ops.padding bottom) index) bottom) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta index (weaken bottom))
  simp only [padding, instantiate_weaken]

theorem padding_apply_free (bottom : Term Const Γ ops.element) (index : Term Const Γ ops.number) :
    (ops.padding_apply (Δ := Δ) bottom index).FunctionExtensionalityFree := by
  simp [padding_apply, ProofSyntax.FunctionExtensionalityFree]

#print axioms mixed_subst
#print axioms suffix_cons_free
end Operations
end Mettapedia.Logic.HOL.VectorChildArrays
