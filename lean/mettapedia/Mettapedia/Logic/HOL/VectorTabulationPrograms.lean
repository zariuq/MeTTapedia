import Mettapedia.Logic.HOL.IndexedVectorPredicate
import Mettapedia.Logic.HOL.NaturalRecursionProofs
import Mettapedia.Logic.HOL.CurriedGuardProgramProofs

/-!
# Two retained natural-recursion programs for native vector tabulation

Both programs construct actual values of the supplied vector carrier. The
shifted-array program recurses at `(number ⇒ element) ⇒ vector`. The offset
program keeps the original array ambient and recurses at `number ⇒ vector`.
Their distinct selection and recursion instances remain explicit. The
equations establish program computation, without a vector guard, an inverse
representation theorem, a cost comparison, or whole-function extensionality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.VectorTabulation
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
  (signature : IndexedVectorPredicate.Signature Const) {Γ Ξ : Ctx Base}

abbrev Array := signature.number ⇒ signature.element

namespace Shifted

abbrev Result := Array signature ⇒ signature.vector
abbrev Selection := SelectionProofs.Selection (signature.number ⇒ Result signature)

def shift (array : Term Const Γ (Array signature)) : Term Const Γ (Array signature) :=
  .lam (.app (weaken array) (.app (weakenCtx _ signature.successor) (.var .vz)))

@[simp] theorem shift_subst (images : Subst Const Γ Ξ) (array : Term Const Γ (Array signature)) :
    HOL.subst images (shift signature array) = shift signature (HOL.subst images array) := by
  simp only [shift, HOL.subst, subst_weaken, subst_weakenCtx, Subst.lift]

def start : Term Const Γ (Result signature) := .lam (weakenCtx _ signature.nil)

def method : Term Const Γ (NaturalRecursionProofs.Method signature.number (Result signature)) :=
  .lam (.lam (.lam (signature.consValue (.var (.vs .vz))
    (.app (.var .vz) (weakenCtx _ signature.zero))
    (.app (.var (.vs (.vs .vz))) (shift signature (.var .vz))))))

@[simp] theorem start_subst (images : Subst Const Γ Ξ) :
    HOL.subst images (start (Γ := Γ) signature) = start (Γ := Ξ) signature := by
  simp only [start, HOL.subst, subst_weakenCtx]

@[simp] theorem method_subst (images : Subst Const Γ Ξ) :
    HOL.subst images (method (Γ := Γ) signature) = method (Γ := Ξ) signature := by
  simp only [method, HOL.subst, signature.subst_consValue, shift_subst, subst_weakenCtx, Subst.lift]
  rfl

def recursor (selection : ClosedTerm Const (Selection signature)) :
    Term Const Γ (signature.number ⇒ Result signature) :=
  NaturalRecursionProofs.recursor (weakenCtx Γ selection) (weakenCtx Γ signature.zero)
    (weakenCtx Γ signature.successor) (start signature) (method signature)

@[simp] theorem recursor_subst (selection : ClosedTerm Const (Selection signature)) (images : Subst Const Γ Ξ) :
    HOL.subst images (recursor (Γ := Γ) signature selection) = recursor (Γ := Ξ) signature selection := by
  simp [recursor, NaturalRecursionProofs.recursor, SelectionProofs.selected, HOL.subst, subst_weakenCtx]

def tabulate (selection : ClosedTerm Const (Selection signature))
    (length : Term Const Γ signature.number) (array : Term Const Γ (Array signature)) :
    Term Const Γ signature.vector := .app (.app (recursor signature selection) length) array

@[simp] theorem tabulate_subst (selection : ClosedTerm Const (Selection signature)) (images : Subst Const Γ Ξ)
    (length : Term Const Γ signature.number) (array : Term Const Γ (Array signature)) :
    HOL.subst images (tabulate signature selection length array) =
      tabulate signature selection (HOL.subst images length) (HOL.subst images array) := by
  simp only [tabulate, HOL.subst, recursor_subst]

variable {Δ : List (Formula Const Γ)}

def shift_apply (array : Term Const Γ (Array signature)) (position : Term Const Γ signature.number) :
    ProofSyntax Const Δ (.eq (.app (shift signature array) position)
      (.app array (.app (weakenCtx Γ signature.successor) position))) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta position
    (.app (weaken array) (.app (weakenCtx _ signature.successor) (.var .vz))))
  simp only [shift, instantiate, HOL.subst, subst_weakenCtx, Subst.single, PredicateFixedPoint.subst_single_weaken]

def start_apply (array : Term Const Γ (Array signature)) :
    ProofSyntax Const Δ (.eq (.app (start signature) array) (weakenCtx Γ signature.nil)) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta array (weakenCtx _ signature.nil))
  simp only [start, instantiate, subst_weakenCtx]

def method_apply (previous : Term Const Γ (Result signature)) (length : Term Const Γ signature.number)
    (array : Term Const Γ (Array signature)) :
    ProofSyntax Const Δ (.eq (.app (.app (.app (method signature) previous) length) array)
      (signature.consValue length (.app array (weakenCtx Γ signature.zero))
        (.app previous (shift signature array)))) := by
  apply ProofSyntax.castIndices rfl ?_ (CurriedGuardProgramProofs.beta3
    (signature.consValue (.var (.vs .vz)) (.app (.var .vz) (weakenCtx _ signature.zero))
      (.app (.var (.vs (.vs .vz))) (shift signature (.var .vz)))) previous length array)
  simp [method, instantiate, signature.subst_consValue, HOL.subst, shift_subst,
    subst_weakenCtx, Subst.single, Subst.lift, weaken, HOL.subst_rename, HOL.subst_comp, Rename.weaken]
  simp only [ProofSyntax.term_subst_of_identity (fun _ => rfl)]
  apply congrArg (fun value : Term Const Γ (Result signature) =>
    signature.consValue length (.app array (weakenCtx Γ signature.zero)) (.app value (shift signature array)))
  exact ProofSyntax.term_subst_of_identity (fun _ => rfl) previous

variable (selection : ClosedTerm Const (Selection signature))
  (choice : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ selection)))
  (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement
    (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor) (Result signature)))

def atZero (array : Term Const Γ (Array signature)) :
    ProofSyntax Const Δ (.eq (tabulate signature selection (weakenCtx Γ signature.zero) array)
      (weakenCtx Γ signature.nil)) :=
  .eqTrans (.eqApp array (NaturalRecursionProofs.atZero (weakenCtx Γ selection)
    (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor) (start signature) (method signature) choice recursion))
    (start_apply signature array)

def atSuccessor (length : Term Const Γ signature.number) (array : Term Const Γ (Array signature)) :
    ProofSyntax Const Δ (.eq (tabulate signature selection (.app (weakenCtx Γ signature.successor) length) array)
      (signature.consValue length (.app array (weakenCtx Γ signature.zero))
        (tabulate signature selection length (shift signature array)))) :=
  .eqTrans (.eqApp array (NaturalRecursionProofs.atSuccessor (weakenCtx Γ selection)
    (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor) (start signature) (method signature) length choice recursion))
    (method_apply signature (.app (recursor signature selection) length) length array)

theorem shift_apply_free (array : Term Const Γ (Array signature)) (position : Term Const Γ signature.number) :
    (shift_apply (Δ := Δ) signature array position).FunctionExtensionalityFree := by
  unfold shift_apply
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

theorem start_apply_free (array : Term Const Γ (Array signature)) :
    (start_apply (Δ := Δ) signature array).FunctionExtensionalityFree := by
  unfold start_apply
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

theorem method_apply_free (previous : Term Const Γ (Result signature)) (length : Term Const Γ signature.number)
    (array : Term Const Γ (Array signature)) :
    (method_apply (Δ := Δ) signature previous length array).FunctionExtensionalityFree := by
  unfold method_apply
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact CurriedGuardProgramProofs.beta3_free _ _ _ _

theorem atZero_free (array : Term Const Γ (Array signature))
    (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree) :
    (atZero signature selection choice recursion array).FunctionExtensionalityFree := by
  refine ⟨?_, start_apply_free _ _⟩
  exact NaturalRecursionProofs.computation_free _ _ _ _ _ choice recursion choiceFree recursionFree

theorem atSuccessor_free (length : Term Const Γ signature.number) (array : Term Const Γ (Array signature))
    (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree) :
    (atSuccessor signature selection choice recursion length array).FunctionExtensionalityFree := by
  refine ⟨?_, method_apply_free _ _ _ _⟩
  simpa only [NaturalRecursionProofs.atSuccessor, ProofSyntax.functionExtensionalityFree_castIndices,
    ProofSyntax.FunctionExtensionalityFree] using
    NaturalRecursionProofs.computation_free (weakenCtx Γ selection) (weakenCtx Γ signature.zero)
      (weakenCtx Γ signature.successor) (start signature) (method signature) choice recursion choiceFree recursionFree

end Shifted

namespace Offset
abbrev Result := signature.number ⇒ signature.vector
abbrev Selection := SelectionProofs.Selection (signature.number ⇒ Result signature)

def start : Term Const Γ (Result signature) := .lam (weakenCtx _ signature.nil)

def method (array : Term Const Γ (Array signature)) :
    Term Const Γ (NaturalRecursionProofs.Method signature.number (Result signature)) :=
  .lam (.lam (.lam (signature.consValue (.var (.vs .vz))
    (.app (weaken (weaken (weaken array))) (.var .vz))
    (.app (.var (.vs (.vs .vz))) (.app (weakenCtx _ signature.successor) (.var .vz))))))

@[simp] theorem start_subst (images : Subst Const Γ Ξ) :
    HOL.subst images (start (Γ := Γ) signature) = start (Γ := Ξ) signature := by
  simp only [start, HOL.subst, subst_weakenCtx]

@[simp] theorem method_subst (images : Subst Const Γ Ξ) (array : Term Const Γ (Array signature)) :
    HOL.subst images (method signature array) = method signature (HOL.subst images array) := by
  simp only [method, HOL.subst, signature.subst_consValue, subst_weaken, subst_weakenCtx, Subst.lift]
  rfl

def recursor (selection : ClosedTerm Const (Selection signature)) (array : Term Const Γ (Array signature)) :
    Term Const Γ (signature.number ⇒ Result signature) :=
  NaturalRecursionProofs.recursor (weakenCtx Γ selection) (weakenCtx Γ signature.zero)
    (weakenCtx Γ signature.successor) (start signature) (method signature array)

@[simp] theorem recursor_subst (selection : ClosedTerm Const (Selection signature)) (images : Subst Const Γ Ξ)
    (array : Term Const Γ (Array signature)) :
    HOL.subst images (recursor signature selection array) = recursor signature selection (HOL.subst images array) := by
  simp [recursor, NaturalRecursionProofs.recursor, SelectionProofs.selected, HOL.subst, subst_weakenCtx]

def fromOffset (selection : ClosedTerm Const (Selection signature)) (length : Term Const Γ signature.number)
    (array : Term Const Γ (Array signature)) (offset : Term Const Γ signature.number) :
    Term Const Γ signature.vector := .app (.app (recursor signature selection array) length) offset

def tabulate (selection : ClosedTerm Const (Selection signature)) (length : Term Const Γ signature.number)
    (array : Term Const Γ (Array signature)) : Term Const Γ signature.vector :=
  fromOffset signature selection length array (weakenCtx Γ signature.zero)

@[simp] theorem at_subst (selection : ClosedTerm Const (Selection signature)) (images : Subst Const Γ Ξ)
    (length : Term Const Γ signature.number) (array : Term Const Γ (Array signature))
    (offset : Term Const Γ signature.number) :
    HOL.subst images (fromOffset signature selection length array offset) =
      fromOffset signature selection (HOL.subst images length) (HOL.subst images array) (HOL.subst images offset) := by
  simp only [fromOffset, HOL.subst, recursor_subst]

@[simp] theorem tabulate_subst (selection : ClosedTerm Const (Selection signature)) (images : Subst Const Γ Ξ)
    (length : Term Const Γ signature.number) (array : Term Const Γ (Array signature)) :
    HOL.subst images (tabulate signature selection length array) =
      tabulate signature selection (HOL.subst images length) (HOL.subst images array) := by
  simp only [tabulate, at_subst, subst_weakenCtx]

variable {Δ : List (Formula Const Γ)}

def start_apply (offset : Term Const Γ signature.number) :
    ProofSyntax Const Δ (.eq (.app (start signature) offset) (weakenCtx Γ signature.nil)) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta offset (weakenCtx _ signature.nil))
  simp only [start, instantiate, subst_weakenCtx]

def method_apply (array : Term Const Γ (Array signature)) (previous : Term Const Γ (Result signature))
    (length offset : Term Const Γ signature.number) :
    ProofSyntax Const Δ (.eq (.app (.app (.app (method signature array) previous) length) offset)
      (signature.consValue length (.app array offset)
        (.app previous (.app (weakenCtx Γ signature.successor) offset)))) := by
  apply ProofSyntax.castIndices rfl ?_ (CurriedGuardProgramProofs.beta3
    (signature.consValue (.var (.vs .vz)) (.app (weaken (weaken (weaken array))) (.var .vz))
      (.app (.var (.vs (.vs .vz))) (.app (weakenCtx _ signature.successor) (.var .vz))))
    previous length offset)
  simp [method, instantiate, signature.subst_consValue, HOL.subst,
    subst_weakenCtx, Subst.single, Subst.lift, weaken, HOL.subst_rename, HOL.subst_comp, Rename.weaken]
  simp only [ProofSyntax.term_subst_of_identity (fun _ => rfl)]
  apply congrArg₂ (signature.consValue length)
  · apply congrArg (fun value : Term Const Γ (Array signature) => Term.app value offset)
    exact ProofSyntax.term_subst_of_identity (fun _ => rfl) array
  · apply congrArg (fun value : Term Const Γ (Result signature) =>
      Term.app value (.app (weakenCtx Γ signature.successor) offset))
    exact ProofSyntax.term_subst_of_identity (fun _ => rfl) previous

variable (selection : ClosedTerm Const (Selection signature))
  (choice : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ selection)))
  (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement
    (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor) (Result signature)))

def atZero (array : Term Const Γ (Array signature)) (offset : Term Const Γ signature.number) :
    ProofSyntax Const Δ (.eq (fromOffset signature selection (weakenCtx Γ signature.zero) array offset)
      (weakenCtx Γ signature.nil)) :=
  .eqTrans (.eqApp offset (NaturalRecursionProofs.atZero (weakenCtx Γ selection)
    (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor) (start signature) (method signature array) choice recursion))
    (start_apply signature offset)

def atSuccessor (length : Term Const Γ signature.number) (array : Term Const Γ (Array signature))
    (offset : Term Const Γ signature.number) :
    ProofSyntax Const Δ (.eq (fromOffset signature selection (.app (weakenCtx Γ signature.successor) length) array offset)
      (signature.consValue length (.app array offset)
        (fromOffset signature selection length array (.app (weakenCtx Γ signature.successor) offset)))) :=
  .eqTrans (.eqApp offset (NaturalRecursionProofs.atSuccessor (weakenCtx Γ selection)
    (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor) (start signature) (method signature array) length choice recursion))
    (method_apply signature array (.app (recursor signature selection array) length) length offset)

theorem start_apply_free (offset : Term Const Γ signature.number) :
    (start_apply (Δ := Δ) signature offset).FunctionExtensionalityFree := by
  unfold start_apply
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

theorem method_apply_free (array : Term Const Γ (Array signature)) (previous : Term Const Γ (Result signature))
    (length offset : Term Const Γ signature.number) :
    (method_apply (Δ := Δ) signature array previous length offset).FunctionExtensionalityFree := by
  unfold method_apply
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact CurriedGuardProgramProofs.beta3_free _ _ _ _

theorem atZero_free (array : Term Const Γ (Array signature)) (offset : Term Const Γ signature.number)
    (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree) :
    (atZero signature selection choice recursion array offset).FunctionExtensionalityFree := by
  refine ⟨?_, start_apply_free _ _⟩
  exact NaturalRecursionProofs.computation_free _ _ _ _ _ choice recursion choiceFree recursionFree

theorem atSuccessor_free (length : Term Const Γ signature.number) (array : Term Const Γ (Array signature))
    (offset : Term Const Γ signature.number)
    (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree) :
    (atSuccessor signature selection choice recursion length array offset).FunctionExtensionalityFree := by
  refine ⟨?_, method_apply_free _ _ _ _ _⟩
  simpa only [NaturalRecursionProofs.atSuccessor, ProofSyntax.functionExtensionalityFree_castIndices,
    ProofSyntax.FunctionExtensionalityFree] using
    NaturalRecursionProofs.computation_free (weakenCtx Γ selection) (weakenCtx Γ signature.zero)
      (weakenCtx Γ signature.successor) (start signature) (method signature array) choice recursion choiceFree recursionFree

end Offset

#print axioms Shifted.atSuccessor
#print axioms Shifted.atSuccessor_free
#print axioms Offset.atSuccessor
#print axioms Offset.atSuccessor_free
end Mettapedia.Logic.HOL.VectorTabulation
