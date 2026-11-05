import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeSourceCaseGuardReadback
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorAllExistence

/-!
# Applying the original guarded case methods

The retained product eliminations consume the actual source input guards.
The branch keeps its length, Vector and supplied All witness distinct.
Existential elimination scopes that witness locally; it does not choose a
global evidence function or assume the desired parent predicate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeSourceCaseApplications
open Mettapedia.Logic Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
namespace Guard
export IndexedVectorTreeSourceCaseGuardReadback (solvedCaseGuardFor branchCaseGuardFor)
end Guard
open IndexedVectorTreeSourceCaseGuardReadback.Native
variable {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
  (answer family : Term Const Γ (E ⇒ .prop)) (motive : Term Const Γ (E ⇒ W ⇒ .prop))
  (solved : Term Const Γ (E ⇒ E)) (branch : Term Const Γ (N ⇒ V ⇒ E))
  (solvedCase : Term Const Γ (E ⇒ W)) (branchCase : Term Const Γ (N ⇒ V ⇒ W ⇒ W))

private def solvedResult : Term Const (E :: Γ) (W ⇒ .prop) :=
  .app (weaken motive) (.app (weaken solved) (.var .vz))

@[irreducible] def solvedApply (field : Term Const Γ E)
    (caseGuard : ProofSyntax Const Δ (.app (Guard.solvedCaseGuardFor answer motive solved) solvedCase))
    (fieldGuard : ProofSyntax Const Δ (.app answer field)) :
    ProofSyntax Const Δ (.app (.app motive (.app solved field)) (.app solvedCase field)) :=
  .castIndices rfl (by
    simp only [solvedResult,instantiate,HOL.subst,Subst.single,PredicateFixedPoint.subst_single_weaken])
    (PredicateProducts.eliminate answer (solvedResult motive solved) solvedCase field caseGuard fieldGuard)

theorem solvedApply_free (field : Term Const Γ E)
    (caseGuard : ProofSyntax Const Δ (.app (Guard.solvedCaseGuardFor answer motive solved) solvedCase))
    (fieldGuard : ProofSyntax Const Δ (.app answer field))
    (caseFree : caseGuard.FunctionExtensionalityFree) (fieldFree : fieldGuard.FunctionExtensionalityFree) :
    (solvedApply answer motive solved solvedCase field caseGuard fieldGuard).FunctionExtensionalityFree := by
  unfold solvedApply
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact PredicateProducts.eliminate_free _ _ _ _ _ _ caseFree fieldFree

private def afterVector (n : Term Const Γ N) (vector : Term Const Γ V) : Term Const Γ ((W ⇒ W) ⇒ .prop) :=
  PredicateProducts.pi (NativeVectorAll.Reading.allCode original pairs witness selection family motive n vector)
    (.app (weaken motive) (.app (.app (weaken branch) (weaken n)) (weaken vector)))

private def afterNumber (n : Term Const Γ N) : Term Const Γ ((V ⇒ W ⇒ W) ⇒ .prop) :=
  PredicateProducts.pi (NativeVectorAll.Reading.vectorCode original selection family n)
    (PredicateProducts.pi
      (NativeVectorAll.Reading.allCode original pairs witness selection (weaken family) (weaken motive) (weaken n) (.var .vz))
      (.app (weaken (weaken motive))
        (.app (.app (weaken (weaken branch)) (weaken (weaken n))) (.var (.vs .vz)))))

private def numberResult : Term Const (N :: Γ) ((V ⇒ W ⇒ W) ⇒ .prop) :=
  PredicateProducts.pi
    (NativeVectorAll.Reading.vectorCode original selection (weaken family) (.var .vz))
    (PredicateProducts.pi
      (NativeVectorAll.Reading.allCode original pairs witness selection (weaken (weaken family))
        (weaken (weaken motive)) (.var (.vs .vz)) (.var .vz))
      (.app (weaken (weaken (weaken motive)))
        (.app (.app (weaken (weaken (weaken branch))) (.var (.vs (.vs .vz)))) (.var (.vs .vz)))))

private def vectorResult (n : Term Const Γ N) : Term Const (V :: Γ) ((W ⇒ W) ⇒ .prop) :=
  PredicateProducts.pi
    (NativeVectorAll.Reading.allCode original pairs witness selection (weaken family) (weaken motive) (weaken n) (.var .vz))
    (.app (weaken (weaken motive))
      (.app (.app (weaken (weaken branch)) (weaken (weaken n))) (.var (.vs .vz))))

private theorem numberResult_instantiate (n : Term Const Γ N) :
    instantiate n (numberResult family motive branch) = afterNumber family motive branch n := by
  simp only [numberResult,afterNumber,instantiate,PredicateProducts.subst_pi,
    NativeVectorAll.Reading.vectorCode,NativeVectorAll.Reading.subst_allCode,HOL.subst,
    subst_weakenCtx,subst_weaken,Subst.single,Subst.lift,PredicateFixedPoint.subst_single_weaken]
  rfl

private theorem vectorResult_instantiate (n : Term Const Γ N) (vector : Term Const Γ V) :
    instantiate vector (vectorResult family motive branch n) = afterVector family motive branch n vector := by
  simp only [vectorResult,afterVector,instantiate,PredicateProducts.subst_pi,
    NativeVectorAll.Reading.subst_allCode,HOL.subst,subst_weaken,Subst.single,Subst.lift,
    PredicateFixedPoint.subst_single_weaken]
  rfl

@[irreducible] private def applyNumber (n : Term Const Γ N)
    (caseGuard : ProofSyntax Const Δ (.app (Guard.branchCaseGuardFor family motive branch) branchCase)) :
    ProofSyntax Const Δ (.app (afterNumber family motive branch n) (.app branchCase n)) :=
  .castIndices rfl (congrArg (fun predicate => Term.app predicate (.app branchCase n))
    (numberResult_instantiate family motive branch n))
    (PredicateProducts.eliminate (PredicateProducts.full N) (numberResult family motive branch) branchCase n caseGuard
      (.impE (.eqPropER (.beta n .top)) .topI))

@[irreducible] private def applyVector (n : Term Const Γ N) (vector : Term Const Γ V)
    (caseGuard : ProofSyntax Const Δ (.app (Guard.branchCaseGuardFor family motive branch) branchCase))
    (vectorGuard : ProofSyntax Const Δ (.app (NativeVectorAll.Reading.vectorCode original selection family n) vector)) :
    ProofSyntax Const Δ (.app (afterVector family motive branch n vector) (.app (.app branchCase n) vector)) :=
  .castIndices rfl (congrArg (fun predicate => Term.app predicate (.app (.app branchCase n) vector))
    (vectorResult_instantiate family motive branch n vector))
    (PredicateProducts.eliminate (NativeVectorAll.Reading.vectorCode original selection family n)
      (vectorResult family motive branch n) (.app branchCase n) vector
      (applyNumber family motive branch branchCase n caseGuard) vectorGuard)

private theorem applyNumber_free (n : Term Const Γ N)
    (caseGuard : ProofSyntax Const Δ (.app (Guard.branchCaseGuardFor family motive branch) branchCase))
    (free : caseGuard.FunctionExtensionalityFree) :
    (applyNumber family motive branch branchCase n caseGuard).FunctionExtensionalityFree := by
  unfold applyNumber
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact PredicateProducts.eliminate_free _ _ _ _ _ _ free (by trivial)

private theorem applyVector_free (n : Term Const Γ N) (vector : Term Const Γ V)
    (caseGuard : ProofSyntax Const Δ (.app (Guard.branchCaseGuardFor family motive branch) branchCase))
    (vectorGuard : ProofSyntax Const Δ (.app (NativeVectorAll.Reading.vectorCode original selection family n) vector))
    (caseFree : caseGuard.FunctionExtensionalityFree) (vectorFree : vectorGuard.FunctionExtensionalityFree) :
    (applyVector family motive branch branchCase n vector caseGuard vectorGuard).FunctionExtensionalityFree := by
  unfold applyVector
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact PredicateProducts.eliminate_free _ _ _ _ _ _
    (applyNumber_free family motive branch branchCase n caseGuard caseFree) vectorFree

@[irreducible] def branchApply (n : Term Const Γ N) (vector : Term Const Γ V) (evidence : Term Const Γ W)
    (caseGuard : ProofSyntax Const Δ (.app (Guard.branchCaseGuardFor family motive branch) branchCase))
    (vectorGuard : ProofSyntax Const Δ (.app (NativeVectorAll.Reading.vectorCode original selection family n) vector))
    (allGuard : ProofSyntax Const Δ (.app (NativeVectorAll.Reading.allCode original pairs witness selection family motive n vector) evidence)) :
    ProofSyntax Const Δ (.app (.app motive (.app (.app branch n) vector)) (.app (.app (.app branchCase n) vector) evidence)) :=
  .castIndices rfl (by
    simp only [instantiate,HOL.subst,PredicateFixedPoint.subst_single_weaken])
    (PredicateProducts.eliminate (NativeVectorAll.Reading.allCode original pairs witness selection family motive n vector)
      (.app (weaken motive) (.app (.app (weaken branch) (weaken n)) (weaken vector)))
      (.app (.app branchCase n) vector) evidence (applyVector family motive branch branchCase n vector caseGuard vectorGuard) allGuard)

theorem branchApply_free (n : Term Const Γ N) (vector : Term Const Γ V) (evidence : Term Const Γ W)
    (caseGuard : ProofSyntax Const Δ (.app (Guard.branchCaseGuardFor family motive branch) branchCase))
    (vectorGuard : ProofSyntax Const Δ (.app (NativeVectorAll.Reading.vectorCode original selection family n) vector))
    (allGuard : ProofSyntax Const Δ (.app (NativeVectorAll.Reading.allCode original pairs witness selection family motive n vector) evidence))
    (caseFree : caseGuard.FunctionExtensionalityFree) (vectorFree : vectorGuard.FunctionExtensionalityFree)
    (allFree : allGuard.FunctionExtensionalityFree) :
    (branchApply family motive branch branchCase n vector evidence caseGuard vectorGuard allGuard).FunctionExtensionalityFree := by
  unfold branchApply
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact PredicateProducts.eliminate_free _ _ _ _ _ _
    (applyVector_free family motive branch branchCase n vector caseGuard vectorGuard caseFree vectorFree) allFree

def parentExists (n : Term Const Γ N) (vector : Term Const Γ V) : Formula Const Γ :=
  CurriedPredicates.existsValue [] (.app motive (.app (.app branch n) vector))

private def allArgument (n : Term Const Γ N) (vector : Term Const Γ V) : Formula Const (W :: Γ) :=
  .app (weaken (NativeVectorAll.Reading.allCode original pairs witness selection family motive n vector)) (.var .vz)

private theorem vectorCode_rename {Ξ : Ctx Base} (rho : Rename Base Γ Ξ)
    (predicate : Term Const Γ (E ⇒ .prop)) (n : Term Const Γ N) :
    HOL.rename rho (NativeVectorAll.Reading.vectorCode original selection predicate n) =
      NativeVectorAll.Reading.vectorCode original selection (HOL.rename rho predicate) (HOL.rename rho n) := by
  simp only [NativeVectorAll.Reading.vectorCode,HOL.rename,rename_weakenCtx]

private theorem existsValue_rename {Ξ : Ctx Base} (rho : Rename Base Γ Ξ) (predicate : Term Const Γ (W ⇒ .prop)) :
    HOL.rename rho (CurriedPredicates.existsValue [] predicate) =
      CurriedPredicates.existsValue [] (HOL.rename rho predicate) := by
  simpa only [subst_ofRename] using CurriedPredicates.existsValue_subst (Subst.ofRename rho) [] predicate

@[irreducible] private def existentialStep (n : Term Const Γ N) (vector : Term Const Γ V)
    (caseGuard : ProofSyntax Const Δ (.app (Guard.branchCaseGuardFor family motive branch) branchCase))
    (vectorGuard : ProofSyntax Const Δ (.app (NativeVectorAll.Reading.vectorCode original selection family n) vector)) :
    ProofSyntax Const (allArgument family motive n vector :: weakenHyps Δ)
      (weaken (parentExists motive branch n vector)) := by
  let hypotheses := allArgument family motive n vector :: weakenHyps Δ
  have casesMoved : ProofSyntax Const hypotheses
      (.app (Guard.branchCaseGuardFor (weaken family) (weaken motive) (weaken branch)) (weaken branchCase)) := by
    apply ProofSyntax.castIndices rfl ?_ ((caseGuard.renameShared Rename.weaken).prepend _)
    change Term.app (HOL.rename Rename.weaken (Guard.branchCaseGuardFor family motive branch)) (weaken branchCase) = _
    exact congrArg (fun predicate => Term.app predicate (weaken branchCase))
      (by simpa only [subst_ofRename,weaken] using
        IndexedVectorTreeSourceCaseGuardReadback.branchCaseGuardFor_subst (Subst.ofRename Rename.weaken) family motive branch)
  have vectorMoved : ProofSyntax Const hypotheses
      (.app (NativeVectorAll.Reading.vectorCode original selection (weaken family) (weaken n)) (weaken vector)) := by
    apply ProofSyntax.castIndices rfl ?_ ((vectorGuard.renameShared Rename.weaken).prepend _)
    exact congrArg (fun predicate => Term.app predicate (weaken vector))
      (vectorCode_rename Rename.weaken family n)
  have allMoved : ProofSyntax Const hypotheses
      (.app (NativeVectorAll.Reading.allCode original pairs witness selection
        (weaken family) (weaken motive) (weaken n) (weaken vector)) (.var .vz)) := by
    apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := hypotheses) 0)
    exact congrArg (fun predicate => Term.app predicate (.var .vz))
      (NativeVectorAll.Reading.rename_allCode original pairs witness selection Rename.weaken family motive n vector)
  have result := branchApply (weaken family) (weaken motive) (weaken branch) (weaken branchCase)
    (weaken n) (weaken vector) (.var .vz) casesMoved vectorMoved allMoved
  have inhabited := CurriedPredicates.existsValue_intro []
    (.app (weaken motive) (.app (.app (weaken branch) (weaken n)) (weaken vector))) PUnit.unit
    (.app (.app (.app (weaken branchCase) (weaken n)) (weaken vector)) (.var .vz)) result
  apply ProofSyntax.castIndices rfl ?_ inhabited
  change CurriedPredicates.existsValue []
    (.app (weaken motive) (.app (.app (weaken branch) (weaken n)) (weaken vector))) =
      HOL.rename Rename.weaken (CurriedPredicates.existsValue [] (.app motive (.app (.app branch n) vector)))
  rw [existsValue_rename]
  rfl

@[irreducible] def branchExists (n : Term Const Γ N) (vector : Term Const Γ V)
    (caseGuard : ProofSyntax Const Δ (.app (Guard.branchCaseGuardFor family motive branch) branchCase))
    (vectorGuard : ProofSyntax Const Δ (.app (NativeVectorAll.Reading.vectorCode original selection family n) vector))
    (all : ProofSyntax Const Δ (NativeVectorAll.Existence.query original pairs witness selection family motive n vector)) :
    ProofSyntax Const Δ (parentExists motive branch n vector) :=
  .exE (.impE (.eqPropEL (CurriedPredicates.existsValue_beta []
    (NativeVectorAll.Reading.allCode original pairs witness selection family motive n vector) PUnit.unit)) all)
    (existentialStep family motive branch branchCase n vector caseGuard vectorGuard)

private theorem existentialStep_free (n : Term Const Γ N) (vector : Term Const Γ V)
    (caseGuard : ProofSyntax Const Δ (.app (Guard.branchCaseGuardFor family motive branch) branchCase))
    (vectorGuard : ProofSyntax Const Δ (.app (NativeVectorAll.Reading.vectorCode original selection family n) vector))
    (caseFree : caseGuard.FunctionExtensionalityFree) (vectorFree : vectorGuard.FunctionExtensionalityFree) :
    (existentialStep family motive branch branchCase n vector caseGuard vectorGuard).FunctionExtensionalityFree := by
  unfold existentialStep
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply CurriedPredicates.existsValue_intro_free
  apply branchApply_free
  · simpa only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.prepend,
      ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.renameShared_eq,
      ProofSyntax.functionExtensionalityFree_rename] using caseFree
  · simpa only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.prepend,
      ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.renameShared_eq,
      ProofSyntax.functionExtensionalityFree_rename] using vectorFree
  · simp only [ProofSyntax.functionExtensionalityFree_castIndices]
    trivial

theorem branchExists_free (n : Term Const Γ N) (vector : Term Const Γ V)
    (caseGuard : ProofSyntax Const Δ (.app (Guard.branchCaseGuardFor family motive branch) branchCase))
    (vectorGuard : ProofSyntax Const Δ (.app (NativeVectorAll.Reading.vectorCode original selection family n) vector))
    (all : ProofSyntax Const Δ (NativeVectorAll.Existence.query original pairs witness selection family motive n vector))
    (caseFree : caseGuard.FunctionExtensionalityFree) (vectorFree : vectorGuard.FunctionExtensionalityFree)
    (allFree : all.FunctionExtensionalityFree) :
    (branchExists family motive branch branchCase n vector caseGuard vectorGuard all).FunctionExtensionalityFree := by
  unfold branchExists
  exact ⟨⟨CurriedPredicates.existsValue_beta_free _ _ _,allFree⟩,
    existentialStep_free family motive branch branchCase n vector caseGuard vectorGuard caseFree vectorFree⟩

#print axioms solvedApply_free
#print axioms branchApply
#print axioms branchApply_free
#print axioms branchExists
#print axioms branchExists_free
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeSourceCaseApplications
