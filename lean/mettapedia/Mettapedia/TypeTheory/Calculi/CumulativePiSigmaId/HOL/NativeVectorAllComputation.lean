import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorAllReading

/-!
# Retained computation of the actual Vector All reading

The original four-argument cons method reduces by explicit beta proofs.
The vector recursor supplies nil/cons equations under its existing selection,
natural-recursion and projection premises. The recursive predicate and vector
tail remain open. No datatype equation or identity reflection is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Computation

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
open Reading
local infixr:60 " ⇒ " => HOL.Ty.arr
universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}
    (original : NativeVectorComputationRows.Operations Base Const)
    {evidence : HOL.Ty Base} (pairs : HOL.PredicateSigma.Operations Const evidence)
    (witness : HOL.ClosedTerm Const evidence)
    (selection : HOL.ClosedTerm Const
      (HOL.SelectionProofs.Selection (original.number ⇒ original.vector ⇒ (evidence ⇒ .prop))))
    {Γ Ξ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)}

def combine (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (head : HOL.Term Const Γ original.element) (recursive : HOL.Term Const Γ (evidence ⇒ .prop)) :
    HOL.Term Const Γ (evidence ⇒ .prop) :=
  .app (.app (HOL.weakenCtx Γ (StructuralProfile.sigmaCode pairs)) (.app predicate head))
    (.lam (HOL.weaken recursive))

@[simp] theorem subst_combine (images : HOL.Subst Const Γ Ξ)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (head : HOL.Term Const Γ original.element) (recursive : HOL.Term Const Γ (evidence ⇒ .prop)) :
    HOL.subst images (combine original pairs predicate head recursive) =
      combine original pairs (HOL.subst images predicate) (HOL.subst images head) (HOL.subst images recursive) := by
  simp only [combine, HOL.subst, HOL.subst_weakenCtx, HOL.subst_weaken]

def cons_apply (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (head : HOL.Term Const Γ original.element)
    (tail : HOL.Term Const Γ original.vector) (recursive : HOL.Term Const Γ (evidence ⇒ .prop)) :
    HOL.ProofSyntax Const Δ (.eq
      (.app (.app (.app (.app (consCode original pairs selection predicate) index) head) tail) recursive)
      (combine original pairs predicate head recursive)) := by
  have first : HOL.ProofSyntax Const Δ (.eq
      (.app (consCode original pairs selection predicate) index)
      (.lam (.lam (.lam (combine original pairs
        (HOL.weaken (HOL.weaken (HOL.weaken predicate))) (.var (.vs (.vs .vz))) (.var .vz)))))) := by
    have cancel : HOL.subst (HOL.Subst.single index) (HOL.weaken predicate) = predicate :=
      HOL.instantiate_weaken index predicate
    refine HOL.ProofSyntax.castIndices rfl ?_ (.beta
      (τ := original.element ⇒ original.vector ⇒ (evidence ⇒ .prop) ⇒ evidence ⇒ .prop) index
      (.lam (.lam (.lam (combine original pairs
        (HOL.weaken (HOL.weaken (HOL.weaken (HOL.weaken predicate)))) (.var (.vs (.vs .vz))) (.var .vz))))))
    simp only [consCode, combine, HOL.instantiate, HOL.subst, HOL.subst_weakenCtx, HOL.subst_weaken,
      HOL.Subst.lift, cancel]
    rfl
  have second : HOL.ProofSyntax Const Δ (.eq
      (τ := original.vector ⇒ (evidence ⇒ .prop) ⇒ evidence ⇒ .prop)
      (.app (.lam (.lam (.lam (combine original pairs
        (HOL.weaken (HOL.weaken (HOL.weaken predicate))) (.var (.vs (.vs .vz))) (.var .vz))))) head)
      (.lam (.lam (combine original pairs (HOL.weaken (HOL.weaken predicate))
        (HOL.weaken (HOL.weaken head)) (.var .vz))))) := by
    have cancel : HOL.subst (HOL.Subst.single head) (HOL.weaken predicate) = predicate :=
      HOL.instantiate_weaken head predicate
    apply HOL.ProofSyntax.castIndices rfl ?_ (.beta
      (τ := original.vector ⇒ (evidence ⇒ .prop) ⇒ evidence ⇒ .prop) head
      (.lam (.lam (combine original pairs (HOL.weaken (HOL.weaken (HOL.weaken predicate)))
        (.var (.vs (.vs .vz))) (.var .vz)))))
    simp only [HOL.instantiate, HOL.subst, subst_combine, HOL.subst_weaken, HOL.Subst.lift, HOL.Subst.single, cancel]
    rfl
  have third : HOL.ProofSyntax Const Δ (.eq
      (.app (.lam (.lam (combine original pairs (HOL.weaken (HOL.weaken predicate))
        (HOL.weaken (HOL.weaken head)) (.var .vz)))) tail)
      (.lam (combine original pairs (HOL.weaken predicate) (HOL.weaken head) (.var .vz)))) := by
    have cancelPredicate : HOL.subst (HOL.Subst.single tail) (HOL.weaken predicate) = predicate :=
      HOL.instantiate_weaken tail predicate
    have cancelHead : HOL.subst (HOL.Subst.single tail) (HOL.weaken head) = head :=
      HOL.instantiate_weaken tail head
    apply HOL.ProofSyntax.castIndices rfl ?_ (.beta
      (τ := (evidence ⇒ .prop) ⇒ evidence ⇒ .prop) tail
      (.lam (combine original pairs (HOL.weaken (HOL.weaken predicate))
        (HOL.weaken (HOL.weaken head)) (.var .vz))))
    simp only [HOL.instantiate, HOL.subst, subst_combine, HOL.subst_weaken, HOL.Subst.lift,
      cancelPredicate, cancelHead]
  have fourth : HOL.ProofSyntax Const Δ (.eq
      (.app (.lam (combine original pairs (HOL.weaken predicate) (HOL.weaken head) (.var .vz))) recursive)
      (combine original pairs predicate head recursive)) := by
    apply HOL.ProofSyntax.castIndices rfl ?_ (.beta recursive
      (combine original pairs (HOL.weaken predicate) (HOL.weaken head) (.var .vz)))
    have cancelPredicate : HOL.subst (HOL.Subst.single recursive) (HOL.weaken predicate) = predicate :=
      HOL.instantiate_weaken recursive predicate
    have cancelHead : HOL.subst (HOL.Subst.single recursive) (HOL.weaken head) = head :=
      HOL.instantiate_weaken recursive head
    simp only [HOL.instantiate, subst_combine, cancelPredicate, cancelHead, HOL.subst, HOL.Subst.single]
  exact .eqTrans (.eqApp recursive (.eqApp tail (.eqApp head first)))
    (.eqTrans (.eqApp recursive (.eqApp tail second)) (.eqTrans (.eqApp recursive third) fourth))

theorem cons_apply_free (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (head : HOL.Term Const Γ original.element)
    (tail : HOL.Term Const Γ original.vector) (recursive : HOL.Term Const Γ (evidence ⇒ .prop)) :
    (cons_apply (Δ := Δ) original pairs selection predicate index head tail recursive).FunctionExtensionalityFree := by
  simp [cons_apply, HOL.ProofSyntax.FunctionExtensionalityFree]

def nil_code (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (choice : HOL.ProofSyntax Const Δ (HOL.SelectionProofs.principle (HOL.weakenCtx Γ selection)))
    (recursion : HOL.ProofSyntax Const Δ (HOL.NaturalRecursionProofs.statement
      (HOL.weakenCtx Γ original.zero) (HOL.weakenCtx Γ original.successor)
      (original.vector ⇒ evidence ⇒ .prop))) :
    HOL.ProofSyntax Const Δ (.eq
      (allCode original pairs witness selection A predicate (HOL.weakenCtx Γ original.zero)
        (.app (HOL.weakenCtx Γ (operations original selection).nilCode) A))
      (unitCode original witness)) := by
  apply HOL.ProofSyntax.castIndices rfl ?_
    ((operations original selection).nilIota A (motiveCode original selection) (unitCode original witness)
      (consCode original pairs selection predicate) choice recursion)
  simp only [allCode, NativeVectorComputationRows.Operations.weaken_eliminator]
  rfl

def cons_code (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (head : HOL.Term Const Γ original.element)
    (tail : HOL.Term Const Γ original.vector)
    (choice : HOL.ProofSyntax Const Δ (HOL.SelectionProofs.principle (HOL.weakenCtx Γ selection)))
    (recursion : HOL.ProofSyntax Const Δ (HOL.NaturalRecursionProofs.statement
      (HOL.weakenCtx Γ original.zero) (HOL.weakenCtx Γ original.successor)
      (original.vector ⇒ evidence ⇒ .prop)))
    (headLaw : HOL.ProofSyntax Const Δ (operations original selection).headLaw)
    (tailLaw : HOL.ProofSyntax Const Δ (operations original selection).tailLaw) :
    HOL.ProofSyntax Const Δ (.eq
      (allCode original pairs witness selection A predicate (.app (HOL.weakenCtx Γ original.successor) index)
        (.app (.app (.app (.app (HOL.weakenCtx Γ (operations original selection).consCode) A) index) head) tail))
      (combine original pairs predicate head (allCode original pairs witness selection A predicate index tail))) := by
  have iota := (operations original selection).consIota A (motiveCode original selection) (unitCode original witness)
    (consCode original pairs selection predicate) index head tail choice recursion headLaw tailLaw
  apply HOL.ProofSyntax.castIndices rfl ?_
    (.eqTrans iota (cons_apply original pairs selection predicate index head tail
      (.app (.app (.app (.app (.app (.app (operations original selection).eliminator A)
        (motiveCode original selection)) (unitCode original witness))
        (consCode original pairs selection predicate)) index) tail)))
  simp only [allCode, NativeVectorComputationRows.Operations.weaken_eliminator]
  rfl

def nil_guard (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (choice : HOL.ProofSyntax Const Δ (HOL.SelectionProofs.principle (HOL.weakenCtx Γ selection)))
    (recursion : HOL.ProofSyntax Const Δ (HOL.NaturalRecursionProofs.statement
      (HOL.weakenCtx Γ original.zero) (HOL.weakenCtx Γ original.successor)
      (original.vector ⇒ evidence ⇒ .prop))) :
    HOL.ProofSyntax Const Δ (.eq
      (allCode original pairs witness selection A predicate (HOL.weakenCtx Γ original.zero)
        (.app (HOL.weakenCtx Γ (operations original selection).nilCode) A))
      (StructuralProfile.identityPredicate witness (fullCode original.number)
        (HOL.weakenCtx Γ original.zero) (HOL.weakenCtx Γ original.zero))) :=
  .eqTrans (nil_code original pairs witness selection A predicate choice recursion)
    (StructuralProfile.identity_apply witness _ _ _)

def cons_guard (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (head : HOL.Term Const Γ original.element)
    (tail : HOL.Term Const Γ original.vector)
    (choice : HOL.ProofSyntax Const Δ (HOL.SelectionProofs.principle (HOL.weakenCtx Γ selection)))
    (recursion : HOL.ProofSyntax Const Δ (HOL.NaturalRecursionProofs.statement
      (HOL.weakenCtx Γ original.zero) (HOL.weakenCtx Γ original.successor)
      (original.vector ⇒ evidence ⇒ .prop)))
    (headLaw : HOL.ProofSyntax Const Δ (operations original selection).headLaw)
    (tailLaw : HOL.ProofSyntax Const Δ (operations original selection).tailLaw) :
    HOL.ProofSyntax Const Δ (.eq
      (allCode original pairs witness selection A predicate (.app (HOL.weakenCtx Γ original.successor) index)
        (.app (.app (.app (.app (HOL.weakenCtx Γ (operations original selection).consCode) A) index) head) tail))
      (HOL.PredicateSigma.sigma pairs (.app predicate head)
        (.lam (HOL.weaken (allCode original pairs witness selection A predicate index tail))))) :=
  .eqTrans (cons_code original pairs witness selection A predicate index head tail choice recursion headLaw tailLaw)
    (StructuralProfile.sigma_apply pairs _ _)

theorem nil_code_free (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (choice : HOL.ProofSyntax Const Δ (HOL.SelectionProofs.principle (HOL.weakenCtx Γ selection)))
    (recursion : HOL.ProofSyntax Const Δ (HOL.NaturalRecursionProofs.statement
      (HOL.weakenCtx Γ original.zero) (HOL.weakenCtx Γ original.successor)
      (original.vector ⇒ evidence ⇒ .prop)))
    (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree) :
    (nil_code original pairs witness selection A predicate choice recursion).FunctionExtensionalityFree := by
  simp [nil_code, NativeVectorComputationRows.Operations.nilIota,
    NativeVectorComputationRows.Operations.eliminator_apply,
    HOL.ProofSyntax.FunctionExtensionalityFree, HOL.VectorRecursionProofs.atZero_free, choiceFree, recursionFree]

theorem cons_code_free (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (head : HOL.Term Const Γ original.element)
    (tail : HOL.Term Const Γ original.vector)
    (choice : HOL.ProofSyntax Const Δ (HOL.SelectionProofs.principle (HOL.weakenCtx Γ selection)))
    (recursion : HOL.ProofSyntax Const Δ (HOL.NaturalRecursionProofs.statement
      (HOL.weakenCtx Γ original.zero) (HOL.weakenCtx Γ original.successor)
      (original.vector ⇒ evidence ⇒ .prop)))
    (headLaw : HOL.ProofSyntax Const Δ (operations original selection).headLaw)
    (tailLaw : HOL.ProofSyntax Const Δ (operations original selection).tailLaw)
    (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree)
    (headFree : headLaw.FunctionExtensionalityFree) (tailFree : tailLaw.FunctionExtensionalityFree) :
    (cons_code original pairs witness selection A predicate index head tail choice recursion headLaw tailLaw).FunctionExtensionalityFree := by
  simp [cons_code, NativeVectorComputationRows.Operations.consIota,
    NativeVectorComputationRows.Operations.eliminator_apply, NativeVectorComputationRows.Operations.cons_apply,
    NativeVectorComputationRows.Operations.head_at, NativeVectorComputationRows.Operations.tail_at,
    HOL.ProofSyntax.FunctionExtensionalityFree, HOL.VectorRecursionProofs.atCons_free,
    cons_apply_free, choiceFree, recursionFree, headFree, tailFree]

theorem nil_guard_free (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (choice : HOL.ProofSyntax Const Δ (HOL.SelectionProofs.principle (HOL.weakenCtx Γ selection)))
    (recursion : HOL.ProofSyntax Const Δ (HOL.NaturalRecursionProofs.statement
      (HOL.weakenCtx Γ original.zero) (HOL.weakenCtx Γ original.successor)
      (original.vector ⇒ evidence ⇒ .prop)))
    (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree) :
    (nil_guard original pairs witness selection A predicate choice recursion).FunctionExtensionalityFree := by
  simp only [nil_guard, HOL.ProofSyntax.FunctionExtensionalityFree,
    StructuralProfile.identity_apply_free, and_true]
  exact nil_code_free original pairs witness selection A predicate choice recursion choiceFree recursionFree

theorem cons_guard_free (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (head : HOL.Term Const Γ original.element)
    (tail : HOL.Term Const Γ original.vector)
    (choice : HOL.ProofSyntax Const Δ (HOL.SelectionProofs.principle (HOL.weakenCtx Γ selection)))
    (recursion : HOL.ProofSyntax Const Δ (HOL.NaturalRecursionProofs.statement
      (HOL.weakenCtx Γ original.zero) (HOL.weakenCtx Γ original.successor)
      (original.vector ⇒ evidence ⇒ .prop)))
    (headLaw : HOL.ProofSyntax Const Δ (operations original selection).headLaw)
    (tailLaw : HOL.ProofSyntax Const Δ (operations original selection).tailLaw)
    (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree)
    (headFree : headLaw.FunctionExtensionalityFree) (tailFree : tailLaw.FunctionExtensionalityFree) :
    (cons_guard original pairs witness selection A predicate index head tail choice recursion headLaw tailLaw).FunctionExtensionalityFree := by
  simp only [cons_guard, HOL.ProofSyntax.FunctionExtensionalityFree, StructuralProfile.sigma_apply_free, and_true]
  exact cons_code_free original pairs witness selection A predicate index head tail choice recursion headLaw tailLaw
    choiceFree recursionFree headFree tailFree

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Computation
