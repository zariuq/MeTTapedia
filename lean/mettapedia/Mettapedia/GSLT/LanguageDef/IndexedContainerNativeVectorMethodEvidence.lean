import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorMethodReading
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorAllEvidence

/-!
# Evidence at the original mixed method's queued hypothesis positions

The generic method-context reader receives the original provider source.
Lookup identifies the complete nested All guard and both direct IH guards at
their actual positions. Constructor-case equations transport that retained
bundle to a cons vector before its head and tail evidence are recovered.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorMethodEvidence

open Mettapedia.Logic
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation TypedEquality.Annotated AnnotatedPredicateReading IndexedContainerAnnotated
open IndexedContainerNativeVectorMethodReading
local infixr:60 " ⇒ " => HOL.Ty.arr

def generated : CCtx Tower.Head target.length :=
  generatedMethodSource (Γ := ambient) carriers IndexedContainerNativeVectorMethodFormation.indexing
    (IndexedContainerNativeVectorMethodFormation.containers resultLevel)
    IndexedContainerNativeVectorMethodFormation.code
    (IndexedContainerNativeVectorMethodFormation.context elementLevel resultLevel)
    (IndexedContainerNativeVectorMethodFormation.types.map (CTm.subst IndexedContainerNativeVectorMethodFormation.images))
    PUnit.unit (.var 1) (.var 0) [] [] rfl

theorem checked_source_generated : checkedSource = generated := by
  have sameCasts {n m : Nat} (first second : n = m) (context : CCtx Tower.Head n) :
      cast (congrArg (CCtx Tower.Head) first) context = second ▸ context := by
    cases first
    rfl
  simp only [checkedSource, generated, generatedMethodSource, source,
    IndexedContainerNativeVectorMethodFormation.completeContext]
  apply sameCasts
  decide +kernel

theorem generated_formed :
    CCtxFormed (NativeVectorAll.Annotated.Profile.church elementLevel resultLevel (fun _ => false)) generated := by
  rw [← checked_source_generated]
  exact checkedSource_formed

def received := readMethodContext? (Γ := ambient)
  (P := NativeVectorAll.Annotated.Profile.church elementLevel resultLevel (fun _ => false))
  (lex := lex) carriers IndexedContainerNativeVectorMethodFormation.indexing
    (IndexedContainerNativeVectorMethodFormation.containers resultLevel)
    IndexedContainerNativeVectorMethodFormation.code
    (IndexedContainerNativeVectorMethodFormation.context elementLevel resultLevel)
    (IndexedContainerNativeVectorMethodFormation.types.map (CTm.subst IndexedContainerNativeVectorMethodFormation.images))
    PUnit.unit (.var 1) (.var 0) [] [] rfl generated_formed

theorem received_eq : received = some guarded := by
  have originalRead : ContextReads lex generated guarded.telescope :=
    checked_source_generated ▸ guarded.reading
  have contextExt (first second : GuardedContext
      (NativeVectorAll.Annotated.Profile.church elementLevel resultLevel (fun _ => false)) lex target)
      (sameSource : first.source = second.source) (sameTelescope : first.telescope = second.telescope) :
      first = second := by
    cases first
    cases second
    cases sameSource
    cases sameTelescope
    rfl
  unfold received readMethodContext?
  change (Reader.readContext? lex target generated).map _ = some guarded
  rw [Reader.readContext_complete originalRead]
  apply congrArg some
  apply contextExt
  · exact checked_source_generated.symm
  · rfl

def atIndex (type : HOL.Ty Base) (position : Fin target.length) (same : target.get position = type) :
    HOL.Var target type := same ▸ HOL.Var.ofFin target position

def bundleIndex : HOL.Var target W := atIndex W ⟨1, by decide +kernel⟩ (by decide +kernel)
def beforeIH : HOL.Var target W := atIndex W ⟨2, by decide +kernel⟩ (by decide +kernel)
def afterIH : HOL.Var target W := atIndex W ⟨0, by decide +kernel⟩ (by decide +kernel)
def beforeValue : HOL.Var target E := atIndex E ⟨6, by decide +kernel⟩ (by decide +kernel)
def afterValue : HOL.Var target E := atIndex E ⟨3, by decide +kernel⟩ (by decide +kernel)
def vectorValue : HOL.Var target V := atIndex V ⟨4, by decide +kernel⟩ (by decide +kernel)
def lengthValue : HOL.Var target N := atIndex N ⟨7, by decide +kernel⟩ (by decide +kernel)
def motiveValue : HOL.Var target (E ⇒ W ⇒ .prop) :=
  atIndex _ ⟨9, by decide +kernel⟩ (by decide +kernel)
def familyValue : HOL.Var target (E ⇒ .prop) := atIndex _ ⟨10, by decide +kernel⟩ (by decide +kernel)

theorem bundle_source : guarded.source.lookup bundleIndex.toFin =
    NativeVectorAll.Annotated.Formation.allType resultLevel (.var familyValue.toFin) (.var motiveValue.toFin)
      (.var lengthValue.toFin) (.var vectorValue.toFin) := by decide +kernel

theorem before_source : guarded.source.lookup beforeIH.toFin =
    .app (.var motiveValue.toFin) (.var beforeValue.toFin) := by decide +kernel

theorem after_source : guarded.source.lookup afterIH.toFin =
    .app (.var motiveValue.toFin) (.var afterValue.toFin) := by decide +kernel

theorem bundle_domain : guarded.telescope.domain bundleIndex =
    NativeVectorAll.Reading.allCode original pairs witness selection (.var familyValue) (.var motiveValue)
      (.var lengthValue) (.var vectorValue) := by
  have found := guarded.reading.lookup bundleIndex
  rw [bundle_source] at found
  exact Reader.term_unique found (NativeVectorAll.Reading.all_reads original pairs witness selection
    elementLevel resultLevel separated (.var familyValue) (.var motiveValue) (.var lengthValue) (.var vectorValue))

theorem before_domain : guarded.telescope.domain beforeIH = .app (.var motiveValue) (.var beforeValue) := by
  have found := guarded.reading.lookup beforeIH
  rw [before_source] at found
  exact Reader.term_unique found (.application (.var motiveValue) (.var beforeValue))

theorem after_domain : guarded.telescope.domain afterIH = .app (.var motiveValue) (.var afterValue) := by
  have found := guarded.reading.lookup afterIH
  rw [after_source] at found
  exact Reader.term_unique found (.application (.var motiveValue) (.var afterValue))

variable (roots : List (HOL.ClosedFormula Const))

def bundle_proof : HOL.ProofSyntax Const (guarded.hypotheses roots)
    (.app (NativeVectorAll.Reading.allCode original pairs witness selection (.var familyValue) (.var motiveValue)
      (.var lengthValue) (.var vectorValue)) (.var bundleIndex)) :=
  HOL.ProofSyntax.castIndices rfl (congrArg (fun code => HOL.Term.app code (.var bundleIndex)) bundle_domain)
    (guarded.variableProof roots bundleIndex)

def before_proof : HOL.ProofSyntax Const (guarded.hypotheses roots)
    (.app (.app (.var motiveValue) (.var beforeValue)) (.var beforeIH)) :=
  HOL.ProofSyntax.castIndices rfl (congrArg (fun code => HOL.Term.app code (.var beforeIH)) before_domain)
    (guarded.variableProof roots beforeIH)

def after_proof : HOL.ProofSyntax Const (guarded.hypotheses roots)
    (.app (.app (.var motiveValue) (.var afterValue)) (.var afterIH)) :=
  HOL.ProofSyntax.castIndices rfl (congrArg (fun code => HOL.Term.app code (.var afterIH)) after_domain)
    (guarded.variableProof roots afterIH)

theorem actual_guards_free : (bundle_proof roots).FunctionExtensionalityFree ∧
    (before_proof roots).FunctionExtensionalityFree ∧ (after_proof roots).FunctionExtensionalityFree := by
  simp only [bundle_proof, before_proof, after_proof, HOL.ProofSyntax.functionExtensionalityFree_castIndices,
    GuardedContext.variableProof_free, and_self]

def all_arguments_eq (index : HOL.Term Const target N) (value : HOL.Term Const target V)
    (lengthEquation : HOL.ProofSyntax Const (guarded.hypotheses roots) (.eq (.var lengthValue) index))
    (vectorEquation : HOL.ProofSyntax Const (guarded.hypotheses roots) (.eq (.var vectorValue) value)) :
    HOL.ProofSyntax Const (guarded.hypotheses roots) (.eq
      (NativeVectorAll.Reading.allCode original pairs witness selection (.var familyValue) (.var motiveValue)
        (.var lengthValue) (.var vectorValue))
      (NativeVectorAll.Reading.allCode original pairs witness selection (.var familyValue) (.var motiveValue) index value)) :=
  .appCongr (.eqAppArg
    (.app (.app (.app (.app (HOL.weakenCtx target (NativeVectorAll.Reading.operations original selection).eliminator)
      (.var familyValue)) (NativeVectorAll.Reading.motiveCode original selection))
      (NativeVectorAll.Reading.unitCode original witness))
      (NativeVectorAll.Reading.consCode original pairs selection (.var motiveValue))) lengthEquation) vectorEquation

def bundle_at (index : HOL.Term Const target N) (value : HOL.Term Const target V)
    (lengthEquation : HOL.ProofSyntax Const (guarded.hypotheses roots) (.eq (.var lengthValue) index))
    (vectorEquation : HOL.ProofSyntax Const (guarded.hypotheses roots) (.eq (.var vectorValue) value)) :
    HOL.ProofSyntax Const (guarded.hypotheses roots) (.app
      (NativeVectorAll.Reading.allCode original pairs witness selection (.var familyValue) (.var motiveValue) index value)
      (.var bundleIndex)) :=
  .impE (.eqPropEL (.eqApp (.var bundleIndex) (all_arguments_eq roots index value lengthEquation vectorEquation)))
    (bundle_proof roots)

theorem bundle_at_free (index : HOL.Term Const target N) (value : HOL.Term Const target V)
    (lengthEquation : HOL.ProofSyntax Const (guarded.hypotheses roots) (.eq (.var lengthValue) index))
    (vectorEquation : HOL.ProofSyntax Const (guarded.hypotheses roots) (.eq (.var vectorValue) value))
    (lengthFree : lengthEquation.FunctionExtensionalityFree) (vectorFree : vectorEquation.FunctionExtensionalityFree) :
    (bundle_at roots index value lengthEquation vectorEquation).FunctionExtensionalityFree := by
  simp [bundle_at, all_arguments_eq, HOL.ProofSyntax.FunctionExtensionalityFree,
    HOL.ProofSyntax.appCongr, lengthFree, vectorFree, (actual_guards_free roots).1]

variable (index : HOL.Term Const target N) (head : HOL.Term Const target E) (tail : HOL.Term Const target V)
    (choice : HOL.ProofSyntax Const (guarded.hypotheses roots) (HOL.SelectionProofs.principle (HOL.weakenCtx target selection)))
    (recursion : HOL.ProofSyntax Const (guarded.hypotheses roots) (HOL.NaturalRecursionProofs.statement
      (HOL.weakenCtx target original.zero) (HOL.weakenCtx target original.successor) (V ⇒ W ⇒ .prop)))
    (headLaw : HOL.ProofSyntax Const (guarded.hypotheses roots) (NativeVectorAll.Reading.operations original selection).headLaw)
    (tailLaw : HOL.ProofSyntax Const (guarded.hypotheses roots) (NativeVectorAll.Reading.operations original selection).tailLaw)
    (firstLaw : HOL.ProofSyntax Const (guarded.hypotheses roots) (HOL.weakenCtx target (HOL.PredicateSigma.firstLaw pairs)))
    (secondLaw : HOL.ProofSyntax Const (guarded.hypotheses roots) (HOL.weakenCtx target (HOL.PredicateSigma.secondLaw pairs)))
    (lengthEquation : HOL.ProofSyntax Const (guarded.hypotheses roots)
      (.eq (.var lengthValue) (.app (HOL.weakenCtx target original.successor) index)))
    (vectorEquation : HOL.ProofSyntax Const (guarded.hypotheses roots)
      (.eq (.var vectorValue)
        (.app (.app (.app (.app (HOL.weakenCtx target (NativeVectorAll.Reading.operations original selection).consCode)
          (.var familyValue)) index) head) tail)))

/-- The only membership proof consumed here is the guard of the actual queued
bundle variable. Constructor-case equations retain the source field identity. -/
def cons_decoded : HOL.ProofSyntax Const (guarded.hypotheses roots)
    (NativeVectorAll.Evidence.decoded original pairs witness selection (.var familyValue) (.var motiveValue)
      index head tail (.var bundleIndex)) :=
  NativeVectorAll.Evidence.cons_decode original pairs witness selection (.var familyValue) (.var motiveValue)
    choice recursion index head tail headLaw tailLaw (.var bundleIndex) firstLaw secondLaw
    (bundle_at roots _ _ lengthEquation vectorEquation)

def cons_head : HOL.ProofSyntax Const (guarded.hypotheses roots)
    (.app (.app (.var motiveValue) head) (HOL.PredicateSigma.first pairs (.var bundleIndex))) :=
  .andEL (.andER (cons_decoded roots index head tail choice recursion headLaw tailLaw firstLaw secondLaw lengthEquation vectorEquation))

def cons_tail : HOL.ProofSyntax Const (guarded.hypotheses roots)
    (.app (NativeVectorAll.Reading.allCode original pairs witness selection (.var familyValue) (.var motiveValue) index tail)
      (HOL.PredicateSigma.second pairs (.var bundleIndex))) :=
  .andER (.andER (cons_decoded roots index head tail choice recursion headLaw tailLaw firstLaw secondLaw lengthEquation vectorEquation))

theorem cons_decoded_free (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree)
    (headFree : headLaw.FunctionExtensionalityFree) (tailFree : tailLaw.FunctionExtensionalityFree)
    (firstFree : firstLaw.FunctionExtensionalityFree) (secondFree : secondLaw.FunctionExtensionalityFree)
    (lengthFree : lengthEquation.FunctionExtensionalityFree) (vectorFree : vectorEquation.FunctionExtensionalityFree) :
    (cons_decoded roots index head tail choice recursion headLaw tailLaw firstLaw secondLaw lengthEquation vectorEquation).FunctionExtensionalityFree := by
  apply NativeVectorAll.Evidence.cons_decode_free
  · exact choiceFree
  · exact recursionFree
  · exact headFree
  · exact tailFree
  · exact firstFree
  · exact secondFree
  · exact bundle_at_free roots _ _ lengthEquation vectorEquation lengthFree vectorFree

#print axioms received_eq
#print axioms bundle_domain
#print axioms actual_guards_free

end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorMethodEvidence
