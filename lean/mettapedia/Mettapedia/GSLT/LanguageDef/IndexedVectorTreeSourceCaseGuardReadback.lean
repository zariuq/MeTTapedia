import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeConstructorInstallation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorAllNaturality

/-!
# Symbolic readback of the two original source case guards

The source telescope remains the complete original seven-variable telescope.
Its case domains are compared with explicit dependent-product programs before
any particular represented family or constructor implementation is inserted.
The branch retains its original third All-W argument and the exact original
All program. These equations transport guards; they do not synthesize case
methods or supply a joint model of an installed source environment.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeSourceCaseGuardReadback
open Mettapedia.Logic Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation TypedEquality.Annotated AnnotatedPredicateReading
namespace Install
export IndexedVectorTreeConstructorInstallation (rawImages)
end Install
namespace Source
export IndexedVectorTreeNativeSourceReading
  (ambient ambientContext answerPredicate familyPredicate motiveCarrier solvedCaseCarrier branchCaseCarrier)
end Source
namespace Native
export IndexedVectorTreeNativeSourceReading.Native
  (Base Const N E V W original pairs witness selection lex elementLevel resultLevel separated)
end Native
open Native

def solvedCaseVariable : Var Source.ambient Source.solvedCaseCarrier := .vs .vz
def branchCaseVariable : Var Source.ambient Source.branchCaseCarrier := .vz
def motiveVariable : Var Source.ambient Source.motiveCarrier := .vs (.vs (.vs (.vs .vz)))
def solvedVariable : Var Source.ambient (E ⇒ E) := .vs (.vs (.vs .vz))
def branchVariable : Var Source.ambient (N ⇒ V ⇒ E) := .vs (.vs .vz)
def familyVariable : Var Source.ambient (E ⇒ .prop) := .vs (.vs (.vs (.vs (.vs .vz))))

variable {Ω Ξ : Ctx Base}

def solvedCaseGuardFor (answer : Term Const Ω (E ⇒ .prop))
    (motive : Term Const Ω (E ⇒ W ⇒ .prop)) (solved : Term Const Ω (E ⇒ E)) :
    Term Const Ω (Source.solvedCaseCarrier ⇒ .prop) :=
  PredicateProducts.pi answer (.app (weaken motive) (.app (weaken solved) (.var .vz)))

def branchCaseGuardFor (family : Term Const Ω (E ⇒ .prop))
    (motive : Term Const Ω (E ⇒ W ⇒ .prop)) (branch : Term Const Ω (N ⇒ V ⇒ E)) :
    Term Const Ω (Source.branchCaseCarrier ⇒ .prop) :=
  PredicateProducts.pi (PredicateProducts.full N)
    (PredicateProducts.pi
      (NativeVectorAll.Reading.vectorCode original selection (weaken family) (.var .vz))
      (PredicateProducts.pi
        (NativeVectorAll.Reading.allCode original pairs witness selection (weaken (weaken family))
          (weaken (weaken motive)) (.var (.vs .vz)) (.var .vz))
        (.app (weaken (weaken (weaken motive)))
          (.app (.app (weaken (weaken (weaken branch))) (.var (.vs (.vs .vz)))) (.var (.vs .vz))))))

theorem solvedCaseGuardFor_subst (images : Subst Const Ω Ξ)
    (answer : Term Const Ω (E ⇒ .prop)) (motive : Term Const Ω (E ⇒ W ⇒ .prop))
    (solved : Term Const Ω (E ⇒ E)) :
    HOL.subst images (solvedCaseGuardFor answer motive solved) =
      solvedCaseGuardFor (HOL.subst images answer) (HOL.subst images motive) (HOL.subst images solved) := by
  simp only [solvedCaseGuardFor,PredicateProducts.subst_pi,HOL.subst,subst_weaken,Subst.lift]

private theorem vectorCode_subst (images : Subst Const Ω Ξ)
    (family : Term Const Ω (E ⇒ .prop)) (index : Term Const Ω N) :
    HOL.subst images (NativeVectorAll.Reading.vectorCode original selection family index) =
      NativeVectorAll.Reading.vectorCode original selection (HOL.subst images family) (HOL.subst images index) := by
  simp only [NativeVectorAll.Reading.vectorCode,HOL.subst,subst_weakenCtx]

theorem branchCaseGuardFor_subst (images : Subst Const Ω Ξ)
    (family : Term Const Ω (E ⇒ .prop)) (motive : Term Const Ω (E ⇒ W ⇒ .prop))
    (branch : Term Const Ω (N ⇒ V ⇒ E)) :
    HOL.subst images (branchCaseGuardFor family motive branch) =
      branchCaseGuardFor (HOL.subst images family) (HOL.subst images motive) (HOL.subst images branch) := by
  simp only [branchCaseGuardFor,PredicateProducts.subst_pi,PredicateProducts.subst_full,
    vectorCode_subst,NativeVectorAll.Reading.subst_allCode,HOL.subst,subst_weaken,Subst.lift]
  rfl

theorem sourceSolvedCaseDomain : Source.ambientContext.telescope.domain solvedCaseVariable =
    solvedCaseGuardFor Source.answerPredicate (.var motiveVariable) (.var solvedVariable) := by
  with_unfolding_all rfl

private def originalBranchCaseType : CTm Tower.Head 7 :=
  .pi (.const NativeNaturalVectorFamilies.natName)
    (.pi (NativeVectorAll.Annotated.vector (.var 6) (.var 0))
      (.pi (NativeVectorAll.Annotated.Formation.allType resultLevel (.var 7) (.var 6) (.var 1) (.var 0))
        (.app (.var 7) (.app (.app (.var 5) (.var 2)) (.var 1)))))

private theorem originalBranchCaseType_retained :
    Source.ambientContext.source.lookup branchCaseVariable.toFin = originalBranchCaseType := by
  decide +kernel

theorem sourceBranchCaseDomain : Source.ambientContext.telescope.domain branchCaseVariable =
    branchCaseGuardFor Source.familyPredicate (.var motiveVariable) (.var branchVariable) := by
  apply Reader.term_unique (Source.ambientContext.reading.lookup branchCaseVariable)
  rw [originalBranchCaseType_retained]
  apply Reads.product (NativeVectorAll.Reading.natural_reads original pairs witness selection elementLevel resultLevel)
  apply Reads.product (NativeVectorAll.Reading.vector_application original pairs witness selection elementLevel resultLevel
    (.var (.vs familyVariable)) (.var .vz))
  apply Reads.product (NativeVectorAll.Reading.all_reads original pairs witness selection elementLevel resultLevel separated
    (.var (.vs (.vs familyVariable))) (.var (.vs (.vs motiveVariable))) (.var (.vs .vz)) (.var .vz))
  have lengthRead : Reads lex (Γ := W :: V :: N :: Source.ambient) (.var 2)
      (.var (.vs (.vs .vz))) := by
    convert (Reads.var (lex := lex) (Γ := W :: V :: N :: Source.ambient) (.vs (.vs .vz))) using 1
    congr 1
  have vectorRead : Reads lex (Γ := W :: V :: N :: Source.ambient) (.var 1)
      (.var (.vs .vz)) := by
    convert (Reads.var (lex := lex) (Γ := W :: V :: N :: Source.ambient) (.vs .vz)) using 1
    congr 1
  have motiveRead : Reads lex (Γ := W :: V :: N :: Source.ambient) (.var 7)
      (weaken (weaken (weaken (Term.var motiveVariable)))) := by
    simp only [weaken,HOL.rename,Rename.weaken]
    convert (Reads.var (lex := lex) (Γ := W :: V :: N :: Source.ambient) (.vs (.vs (.vs motiveVariable)))) using 1
    congr 1
  have branchRead : Reads lex (Γ := W :: V :: N :: Source.ambient) (.var 5)
      (weaken (weaken (weaken (Term.var branchVariable)))) := by
    simp only [weaken,HOL.rename,Rename.weaken]
    convert (Reads.var (lex := lex) (Γ := W :: V :: N :: Source.ambient) (.vs (.vs (.vs branchVariable)))) using 1
    congr 1
  exact Reads.application
    motiveRead
    (Reads.application
      (Reads.application branchRead lengthRead)
      vectorRead)

variable (answer family : Term Const Ω (E ⇒ .prop))
  (motive : Term Const Ω Source.motiveCarrier)
  (solved : Term Const Ω (E ⇒ E)) (branch : Term Const Ω (N ⇒ V ⇒ E))
  (solvedCase : Term Const Ω Source.solvedCaseCarrier)
  (branchCase : Term Const Ω Source.branchCaseCarrier)

theorem rawSolvedCaseGuard :
    HOL.subst (Install.rawImages answer family motive solved branch solvedCase branchCase)
      (Source.ambientContext.telescope.guard solvedCaseVariable) =
      .app (solvedCaseGuardFor answer motive solved) solvedCase := by
  change Term.app (HOL.subst (Install.rawImages answer family motive solved branch solvedCase branchCase)
    (Source.ambientContext.telescope.domain solvedCaseVariable))
    (HOL.subst (Install.rawImages answer family motive solved branch solvedCase branchCase) (.var solvedCaseVariable)) = _
  rw [sourceSolvedCaseDomain,solvedCaseGuardFor_subst]
  rfl

theorem rawBranchCaseGuard :
    HOL.subst (Install.rawImages answer family motive solved branch solvedCase branchCase)
      (Source.ambientContext.telescope.guard branchCaseVariable) =
      .app (branchCaseGuardFor family motive branch) branchCase := by
  change Term.app (HOL.subst (Install.rawImages answer family motive solved branch solvedCase branchCase)
    (Source.ambientContext.telescope.domain branchCaseVariable))
    (HOL.subst (Install.rawImages answer family motive solved branch solvedCase branchCase) (.var branchCaseVariable)) = _
  rw [sourceBranchCaseDomain,branchCaseGuardFor_subst]
  rfl

#print axioms solvedCaseGuardFor_subst
#print axioms branchCaseGuardFor_subst
#print axioms rawSolvedCaseGuard
#print axioms rawBranchCaseGuard

end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeSourceCaseGuardReadback
