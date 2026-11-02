import Mettapedia.Logic.HOL.NaturalRecursionProofs

/-!
# Prepending to a natural-indexed function array

The actual HOL term is a selected natural recursor. Its method ignores the
previous result and reads the supplied suffix at the predecessor index.
Both equations retain selection and recursion at the element result type.
No array equation, predecessor function or number no-confusion law is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.FunctionArrayPrepend

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
    {number element : Ty Base}

def method (rest : Term Const Γ (number ⇒ element)) :
    Term Const Γ (NaturalRecursionProofs.Method number element) :=
  .lam (.lam (.app (weaken (weaken rest)) (.var .vz)))

@[simp] theorem method_subst (images : Subst Const Γ Ξ)
    (rest : Term Const Γ (number ⇒ element)) :
    HOL.subst images (method rest) = method (HOL.subst images rest) := by
  simp only [method, HOL.subst, subst_weaken, Subst.lift]

def prepend (selection : Term Const Γ (SelectionProofs.Selection (number ⇒ element)))
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (first : Term Const Γ element) (rest : Term Const Γ (number ⇒ element)) :
    Term Const Γ (number ⇒ element) :=
  NaturalRecursionProofs.recursor selection zero successor first (method rest)

@[simp] theorem prepend_subst (images : Subst Const Γ Ξ)
    (selection : Term Const Γ (SelectionProofs.Selection (number ⇒ element)))
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (first : Term Const Γ element) (rest : Term Const Γ (number ⇒ element)) :
    HOL.subst images (prepend selection zero successor first rest) =
      prepend (HOL.subst images selection) (HOL.subst images zero) (HOL.subst images successor)
        (HOL.subst images first) (HOL.subst images rest) := by
  simp [prepend, NaturalRecursionProofs.recursor, SelectionProofs.selected, HOL.subst]

@[simp] theorem prepend_rename (rho : Rename Base Γ Ξ)
    (selection : Term Const Γ (SelectionProofs.Selection (number ⇒ element)))
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (first : Term Const Γ element) (rest : Term Const Γ (number ⇒ element)) :
    HOL.rename rho (prepend selection zero successor first rest) =
      prepend (HOL.rename rho selection) (HOL.rename rho zero) (HOL.rename rho successor)
        (HOL.rename rho first) (HOL.rename rho rest) := by
  simpa only [subst_ofRename] using prepend_subst (Subst.ofRename rho) selection zero successor first rest

variable {Δ : List (Formula Const Γ)}

def method_apply (rest : Term Const Γ (number ⇒ element))
    (previous : Term Const Γ element) (index : Term Const Γ number) :
    ProofSyntax Const Δ (.eq (.app (.app (method rest) previous) index) (.app rest index)) := by
  have first : ProofSyntax Const Δ (.eq (.app (method rest) previous)
      (.lam (.app (weaken rest) (.var .vz)))) := by
    have cancel : HOL.subst (Subst.single previous) (weaken rest) = rest :=
      instantiate_weaken previous rest
    apply ProofSyntax.castIndices rfl ?_
      (.beta previous (.lam (.app (weaken (weaken rest)) (.var .vz))))
    simp only [method, instantiate, HOL.subst, subst_weaken, Subst.lift, cancel]
  have second : ProofSyntax Const Δ (.eq
      (.app (.lam (.app (weaken rest) (.var .vz))) index) (.app rest index)) := by
    have cancel : HOL.subst (Subst.single index) (weaken rest) = rest :=
      instantiate_weaken index rest
    apply ProofSyntax.castIndices rfl ?_ (.beta index (.app (weaken rest) (.var .vz)))
    simp only [instantiate, HOL.subst, cancel, Subst.single]
  exact .eqTrans (.eqApp index first) second

theorem method_apply_free (rest : Term Const Γ (number ⇒ element))
    (previous : Term Const Γ element) (index : Term Const Γ number) :
    (method_apply (Δ := Δ) rest previous index).FunctionExtensionalityFree := by
  simp [method_apply, ProofSyntax.FunctionExtensionalityFree]

def atZero (selection : Term Const Γ (SelectionProofs.Selection (number ⇒ element)))
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (first : Term Const Γ element) (rest : Term Const Γ (number ⇒ element))
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement zero successor element)) :
    ProofSyntax Const Δ (.eq (.app (prepend selection zero successor first rest) zero) first) :=
  NaturalRecursionProofs.atZero selection zero successor first (method rest) choice recursion

def atSuccessor (selection : Term Const Γ (SelectionProofs.Selection (number ⇒ element)))
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (first : Term Const Γ element) (rest : Term Const Γ (number ⇒ element))
    (index : Term Const Γ number)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement zero successor element)) :
    ProofSyntax Const Δ (.eq (.app (prepend selection zero successor first rest) (.app successor index))
      (.app rest index)) :=
  .eqTrans (NaturalRecursionProofs.atSuccessor selection zero successor first (method rest) index choice recursion)
    (method_apply rest (.app (prepend selection zero successor first rest) index) index)

theorem atZero_free (selection : Term Const Γ (SelectionProofs.Selection (number ⇒ element)))
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (first : Term Const Γ element) (rest : Term Const Γ (number ⇒ element))
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement zero successor element))
    (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree) :
    (atZero selection zero successor first rest choice recursion).FunctionExtensionalityFree :=
  NaturalRecursionProofs.computation_free selection zero successor first (method rest)
    choice recursion choiceFree recursionFree

theorem atSuccessor_free (selection : Term Const Γ (SelectionProofs.Selection (number ⇒ element)))
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (first : Term Const Γ element) (rest : Term Const Γ (number ⇒ element))
    (index : Term Const Γ number)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement zero successor element))
    (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree) :
    (atSuccessor selection zero successor first rest index choice recursion).FunctionExtensionalityFree := by
  unfold atSuccessor
  refine ⟨?_, method_apply_free _ _ _⟩
  simpa [NaturalRecursionProofs.atSuccessor, ProofSyntax.FunctionExtensionalityFree] using
    NaturalRecursionProofs.computation_free selection zero successor first (method rest)
      choice recursion choiceFree recursionFree

#print axioms prepend_subst
#print axioms atSuccessor_free
end Mettapedia.Logic.HOL.FunctionArrayPrepend
