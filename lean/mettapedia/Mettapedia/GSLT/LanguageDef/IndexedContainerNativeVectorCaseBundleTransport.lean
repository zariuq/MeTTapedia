import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorCaseContext

/-!
# Carrying the original queued bundle into the case-function context

The verified context embedding transports the actual original bundle guard.
Reading coherence identifies its renamed All program. Target-side constructor
equations and the retained recursor/projection laws then recover the head and
tail evidence. These equations and laws remain explicit premises.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorCaseBundleTransport

open Mettapedia.Logic
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation TypedEquality.Annotated AnnotatedPredicateReading
open IndexedContainerNativeVectorMethodReading
local infixr:60 " ⇒ " => HOL.Ty.arr

private abbrev carrier := IndexedContainerNativeVectorCaseContext.carrier
private abbrev context := IndexedContainerNativeVectorCaseContext.context
private abbrev nativeRenaming : HOL.Rename Base target carrier := IndexedContainerNativeVectorCaseContext.nativeRen
private abbrev rawRenaming := IndexedContainerNativeVectorCaseContext.sourceRen

def family := nativeRenaming IndexedContainerNativeVectorMethodEvidence.familyValue
def motive := nativeRenaming IndexedContainerNativeVectorMethodEvidence.motiveValue
def length := nativeRenaming IndexedContainerNativeVectorMethodEvidence.lengthValue
def vector := nativeRenaming IndexedContainerNativeVectorMethodEvidence.vectorValue
def bundle := nativeRenaming IndexedContainerNativeVectorMethodEvidence.bundleIndex

def predicate := NativeVectorAll.Reading.allCode original pairs witness selection
  (.var family) (.var motive) (.var length) (.var vector)

theorem predicate_renamed : HOL.rename nativeRenaming
    (NativeVectorAll.Reading.allCode original pairs witness selection
      (.var IndexedContainerNativeVectorMethodEvidence.familyValue)
      (.var IndexedContainerNativeVectorMethodEvidence.motiveValue)
      (.var IndexedContainerNativeVectorMethodEvidence.lengthValue)
      (.var IndexedContainerNativeVectorMethodEvidence.vectorValue)) = predicate := by
  have originalRead := NativeVectorAll.Reading.all_reads original pairs witness selection
    elementLevel resultLevel separated (.var IndexedContainerNativeVectorMethodEvidence.familyValue)
    (.var IndexedContainerNativeVectorMethodEvidence.motiveValue)
    (.var IndexedContainerNativeVectorMethodEvidence.lengthValue)
    (.var IndexedContainerNativeVectorMethodEvidence.vectorValue)
  have mapped := originalRead.rename nativeRenaming rawRenaming
    (fun index => IndexedContainerNativeVectorCaseContext.renaming_compatible index)
  have sourceEquation : (NativeVectorAll.Annotated.Formation.allType resultLevel
      (.var IndexedContainerNativeVectorMethodEvidence.familyValue.toFin)
      (.var IndexedContainerNativeVectorMethodEvidence.motiveValue.toFin)
      (.var IndexedContainerNativeVectorMethodEvidence.lengthValue.toFin)
      (.var IndexedContainerNativeVectorMethodEvidence.vectorValue.toFin)).rename rawRenaming =
      NativeVectorAll.Annotated.Formation.allType resultLevel
        (.var family.toFin) (.var motive.toFin) (.var length.toFin) (.var vector.toFin) := by
    rw [NativeVectorAll.Annotated.Formation.allType_rename]
    simp only [CTm.rename]
    congr 1
  rw [sourceEquation] at mapped
  exact Reader.term_unique mapped (NativeVectorAll.Reading.all_reads original pairs witness selection
    elementLevel resultLevel separated (.var family) (.var motive) (.var length) (.var vector))

@[irreducible] def received (roots : List (HOL.ClosedFormula Const)) :
    HOL.ProofSyntax Const (context.hypotheses roots) (.app predicate (.var bundle)) := by
  apply HOL.ProofSyntax.castIndices rfl ?_
    ((IndexedContainerNativeVectorCaseContext.embedding roots).transport
      (IndexedContainerNativeVectorMethodEvidence.bundle_proof roots))
  rw [HOL.subst_ofRename]
  change HOL.Term.app (HOL.rename nativeRenaming _) (.var bundle) = HOL.Term.app predicate (.var bundle)
  exact congrArg (fun code => HOL.Term.app code (.var bundle)) predicate_renamed

theorem received_free (roots : List (HOL.ClosedFormula Const)) :
    (received roots).FunctionExtensionalityFree := by
  unfold received
  apply (HOL.ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact GuardedSubstitution.transport_free _ _ (IndexedContainerNativeVectorCaseContext.embedding_free roots)
    (IndexedContainerNativeVectorMethodEvidence.actual_guards_free roots).1

variable (roots : List (HOL.ClosedFormula Const)) {assumptions : List (HOL.Formula Const carrier)}
    (placement : HOL.ProofSyntax.OccurrenceMap (context.hypotheses roots) assumptions)
    (index : HOL.Term Const carrier N) (head : HOL.Term Const carrier E) (tail : HOL.Term Const carrier V)
    (choice : HOL.ProofSyntax Const assumptions (HOL.SelectionProofs.principle (HOL.weakenCtx carrier selection)))
    (recursion : HOL.ProofSyntax Const assumptions (HOL.NaturalRecursionProofs.statement
      (HOL.weakenCtx carrier original.zero) (HOL.weakenCtx carrier original.successor) (V ⇒ W ⇒ .prop)))
    (headLaw : HOL.ProofSyntax Const assumptions (NativeVectorAll.Reading.operations original selection).headLaw)
    (tailLaw : HOL.ProofSyntax Const assumptions (NativeVectorAll.Reading.operations original selection).tailLaw)
    (firstLaw : HOL.ProofSyntax Const assumptions (HOL.weakenCtx carrier (HOL.PredicateSigma.firstLaw pairs)))
    (secondLaw : HOL.ProofSyntax Const assumptions (HOL.weakenCtx carrier (HOL.PredicateSigma.secondLaw pairs)))
    (lengthEquation : HOL.ProofSyntax Const assumptions
      (.eq (.var length) (.app (HOL.weakenCtx carrier original.successor) index)))
    (vectorEquation : HOL.ProofSyntax Const assumptions
      (.eq (.var vector) (.app (.app (.app (.app
        (HOL.weakenCtx carrier (NativeVectorAll.Reading.operations original selection).consCode) (.var family)) index) head) tail)))

def equations : HOL.ProofSyntax Const assumptions (.eq predicate
    (NativeVectorAll.Reading.allCode original pairs witness selection (.var family) (.var motive)
      (.app (HOL.weakenCtx carrier original.successor) index)
      (.app (.app (.app (.app (HOL.weakenCtx carrier (NativeVectorAll.Reading.operations original selection).consCode)
        (.var family)) index) head) tail))) :=
  .appCongr (.eqAppArg
    (.app (.app (.app (.app (HOL.weakenCtx carrier (NativeVectorAll.Reading.operations original selection).eliminator)
      (.var family)) (NativeVectorAll.Reading.motiveCode original selection))
      (NativeVectorAll.Reading.unitCode original witness))
      (NativeVectorAll.Reading.consCode original pairs selection (.var motive))) lengthEquation) vectorEquation

def decoded : HOL.ProofSyntax Const assumptions
    (NativeVectorAll.Evidence.decoded original pairs witness selection (.var family) (.var motive)
      index head tail (.var bundle)) :=
  NativeVectorAll.Evidence.cons_decode original pairs witness selection (.var family) (.var motive)
    choice recursion index head tail headLaw tailLaw (.var bundle) firstLaw secondLaw
    (.impE (.eqPropEL (.eqApp (.var bundle) (equations index head tail lengthEquation vectorEquation)))
      ((received roots).mono placement))

theorem decoded_free (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree)
    (headFree : headLaw.FunctionExtensionalityFree) (tailFree : tailLaw.FunctionExtensionalityFree)
    (firstFree : firstLaw.FunctionExtensionalityFree) (secondFree : secondLaw.FunctionExtensionalityFree)
    (lengthFree : lengthEquation.FunctionExtensionalityFree) (vectorFree : vectorEquation.FunctionExtensionalityFree) :
    (decoded roots placement index head tail choice recursion headLaw tailLaw firstLaw secondLaw lengthEquation vectorEquation).FunctionExtensionalityFree := by
  apply NativeVectorAll.Evidence.cons_decode_free
  · exact choiceFree
  · exact recursionFree
  · exact headFree
  · exact tailFree
  · exact firstFree
  · exact secondFree
  · refine ⟨?_, ?_⟩
    · simpa only [equations, HOL.ProofSyntax.appCongr, HOL.ProofSyntax.FunctionExtensionalityFree]
        using And.intro lengthFree vectorFree
    · exact (HOL.ProofSyntax.functionExtensionalityFree_mono placement (received roots)).mpr (received_free roots)

#print axioms received_free
#print axioms decoded_free

end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorCaseBundleTransport
