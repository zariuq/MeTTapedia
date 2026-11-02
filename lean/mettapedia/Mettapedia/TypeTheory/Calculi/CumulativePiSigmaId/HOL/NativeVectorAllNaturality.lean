import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorAllEvidence

/-!
# Context transport of the actual All predicate program

Substitution changes the element predicate, motive and original index/vector
arguments while retaining the closed recursor, witness and pairing operations.
The argument-congruence program preserves the supplied equality receipts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Reading

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
local infixr:60 " ⇒ " => HOL.Ty.arr
universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v} {evidence : HOL.Ty Base}
    (original : NativeVectorComputationRows.Operations Base Const)
    (pairs : HOL.PredicateSigma.Operations Const evidence) (witness : HOL.ClosedTerm Const evidence)
    (selection : HOL.ClosedTerm Const
      (HOL.SelectionProofs.Selection (original.number ⇒ original.vector ⇒ evidence ⇒ .prop)))
    {Γ Ξ : HOL.Ctx Base}

theorem subst_fullCode (images : HOL.Subst Const Γ Ξ) (type : HOL.Ty Base) :
    HOL.subst images (fullCode (Const := Const) (Γ := Γ) type) = fullCode (Γ := Ξ) type := by
  simp only [fullCode, HOL.subst_weakenCtx]

theorem subst_motiveCode (images : HOL.Subst Const Γ Ξ) :
    HOL.subst images (motiveCode original selection (Γ := Γ)) = motiveCode original selection (Γ := Ξ) := by
  simp only [motiveCode, HOL.subst, subst_fullCode]

theorem subst_unitCode (images : HOL.Subst Const Γ Ξ) :
    HOL.subst images (unitCode original witness (Γ := Γ)) = unitCode original witness (Γ := Ξ) := by
  simp only [unitCode, HOL.subst, HOL.subst_weakenCtx, subst_fullCode]

theorem subst_consCode (images : HOL.Subst Const Γ Ξ)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop)) :
    HOL.subst images (consCode original pairs selection predicate) =
      consCode original pairs selection (HOL.subst images predicate) := by
  simp only [consCode, HOL.subst, HOL.subst_weakenCtx, HOL.subst_weaken, HOL.Subst.lift]
  rfl

theorem subst_allCode (images : HOL.Subst Const Γ Ξ)
    (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (value : HOL.Term Const Γ original.vector) :
    HOL.subst images (allCode original pairs witness selection A predicate index value) =
      allCode original pairs witness selection (HOL.subst images A) (HOL.subst images predicate)
        (HOL.subst images index) (HOL.subst images value) := by
  simp only [allCode, HOL.subst, HOL.subst_weakenCtx, subst_motiveCode, subst_unitCode, subst_consCode]

theorem rename_allCode (rho : HOL.Rename Base Γ Ξ)
    (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (value : HOL.Term Const Γ original.vector) :
    HOL.rename rho (allCode original pairs witness selection A predicate index value) =
      allCode original pairs witness selection (HOL.rename rho A) (HOL.rename rho predicate)
        (HOL.rename rho index) (HOL.rename rho value) := by
  simpa only [HOL.subst_ofRename] using subst_allCode original pairs witness selection
    (HOL.Subst.ofRename rho) A predicate index value

theorem rename_choiceLaw (rho : HOL.Rename Base Γ Ξ) :
    HOL.rename rho (HOL.SelectionProofs.principle (HOL.weakenCtx Γ selection)) =
      HOL.SelectionProofs.principle (HOL.weakenCtx Ξ selection) := by
  have mapped := (operations original selection).assumptions_substitute (HOL.Subst.ofRename rho)
  have first := congrArg List.head? mapped
  exact Option.some.inj (by simpa only [NativeVectorComputationRows.Operations.assumptions,
    List.map_cons, List.head?_cons, HOL.subst_ofRename, operations, typeOperations] using first)

include selection in
theorem rename_recursionLaw (rho : HOL.Rename Base Γ Ξ) :
    HOL.rename rho (HOL.NaturalRecursionProofs.statement (HOL.weakenCtx Γ original.zero)
      (HOL.weakenCtx Γ original.successor) (original.vector ⇒ evidence ⇒ .prop)) =
      HOL.NaturalRecursionProofs.statement (HOL.weakenCtx Ξ original.zero)
        (HOL.weakenCtx Ξ original.successor) (original.vector ⇒ evidence ⇒ .prop) := by
  have mapped := (operations original selection).assumptions_substitute (HOL.Subst.ofRename rho)
  have second := congrArg (fun statements => (statements.drop 1).head?) mapped
  exact Option.some.inj (by simpa only [NativeVectorComputationRows.Operations.assumptions,
    List.map_cons, List.drop_succ_cons, List.drop_zero, List.head?_cons, HOL.subst_ofRename,
    operations, typeOperations] using second)

theorem rename_headLaw (rho : HOL.Rename Base Γ Ξ) :
    HOL.rename rho ((operations original selection).headLaw (Γ := Γ)) =
      (operations original selection).headLaw (Γ := Ξ) := by
  have mapped := (operations original selection).assumptions_substitute (HOL.Subst.ofRename rho)
  have third := congrArg (fun statements => (statements.drop 2).head?) mapped
  exact Option.some.inj (by simpa only [NativeVectorComputationRows.Operations.assumptions,
    List.map_cons, List.drop_succ_cons, List.drop_zero, List.head?_cons, HOL.subst_ofRename] using third)

theorem rename_tailLaw (rho : HOL.Rename Base Γ Ξ) :
    HOL.rename rho ((operations original selection).tailLaw (Γ := Γ)) =
      (operations original selection).tailLaw (Γ := Ξ) := by
  have mapped := (operations original selection).assumptions_substitute (HOL.Subst.ofRename rho)
  have fourth := congrArg (fun statements => (statements.drop 3).head?) mapped
  exact Option.some.inj (by simpa only [NativeVectorComputationRows.Operations.assumptions,
    List.map_cons, List.drop_succ_cons, List.drop_zero, List.head?_cons, HOL.subst_ofRename] using fourth)

def arguments_equal {assumptions : List (HOL.Formula Const Γ)}
    (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (firstIndex secondIndex : HOL.Term Const Γ original.number)
    (firstValue secondValue : HOL.Term Const Γ original.vector)
    (indexEquality : HOL.ProofSyntax Const assumptions (.eq firstIndex secondIndex))
    (valueEquality : HOL.ProofSyntax Const assumptions (.eq firstValue secondValue)) :
    HOL.ProofSyntax Const assumptions (.eq
      (allCode original pairs witness selection A predicate firstIndex firstValue)
      (allCode original pairs witness selection A predicate secondIndex secondValue)) :=
  .appCongr (.eqAppArg
    (.app (.app (.app (.app (HOL.weakenCtx Γ (operations original selection).eliminator) A)
      (motiveCode original selection)) (unitCode original witness)) (consCode original pairs selection predicate))
    indexEquality) valueEquality

theorem arguments_equal_free {assumptions : List (HOL.Formula Const Γ)}
    (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (firstIndex secondIndex : HOL.Term Const Γ original.number)
    (firstValue secondValue : HOL.Term Const Γ original.vector)
    (indexEquality : HOL.ProofSyntax Const assumptions (.eq firstIndex secondIndex))
    (valueEquality : HOL.ProofSyntax Const assumptions (.eq firstValue secondValue))
    (indexFree : indexEquality.FunctionExtensionalityFree) (valueFree : valueEquality.FunctionExtensionalityFree) :
    (arguments_equal original pairs witness selection A predicate firstIndex secondIndex firstValue secondValue
      indexEquality valueEquality).FunctionExtensionalityFree := by
  simpa only [arguments_equal, HOL.ProofSyntax.appCongr, HOL.ProofSyntax.FunctionExtensionalityFree]
    using And.intro indexFree valueFree

#print axioms subst_allCode
#print axioms arguments_equal_free

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Reading
