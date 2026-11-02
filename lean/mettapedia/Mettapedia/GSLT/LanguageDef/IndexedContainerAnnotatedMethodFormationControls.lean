import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerAnnotatedMethods
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerAnnotatedSubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerGuardedMethodContexts
import Mettapedia.GSLT.LanguageDef.IndexedContainerAnnotatedFormationControls

/-!
# Formation of an actual indexed source-method interface

The source binds a natural index and a field at that index, followed by its
dependent induction hypothesis. The family and motive have distinct universe
parameters. Constructor and motive variables live in a formed source context;
no closed datatype model or native case realization is inferred from it.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerAnnotatedMethodFormationControls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies
open IndexedContainerAnnotated
open Mettapedia.Logic
local infixr:60 " ⇒ " => HOL.Ty.arr

namespace Source

open IndexedContainerAnnotatedFormationControls.Formation (profile theory level)
open IndexedContainerAnnotatedFormationControls.Indexed

def resultLevel : Tower.Head := .sort (.param 1)

theorem methods : MethodPrimitives (P := theory) baseContext.source types indexing containers
    (.const natName) level resultLevel (fun _ => True) where
  toConstructorPrimitives := primitives
  resultUniverse := .sort _
  bundle := by intro n target images morphism context name entry absent; cases absent

def motive : CTm Tower.Head 2 := motiveType indexing types.family (.const natName) resultLevel

theorem motive_formed : CIsType theory baseContext.source motive := by
  apply CIsType.pi (Programs.Annotated.levelModel profile)
    ⟨.sort Tower.zero, .sort _, Programs.Annotated.Functions.natural_typed profile⟩
  apply CIsType.pi (Programs.Annotated.levelModel profile)
    ⟨level, .sort _,
      CDerivable.appElim
        (show CTyped theory (.snoc baseContext.source (.const natName)) (.var 1)
          (.pi (.const natName) (.head level)) from .var 1) (.var 0)⟩
  exact ⟨.sort (.succ (.param 1)), .sort _, .headType (.sort _)⟩

def constructor : CTm Tower.Head 2 := constructorType indexing containers code types PUnit.unit

theorem constructor_exact : constructor =
    .pi (.const natName) (.pi (.app (.var 1) (.var 0)) (.app (.var 2) (.var 1))) := by decide +kernel

theorem constructor_formed : CIsType theory baseContext.source constructor := by
  have same : types.map (CTm.subst identity) = types := by
    simp only [TypeSyntax.map, identity, CTm.subst_ids]
    rfl
  have formed := constructorType_formed (Programs.Annotated.levelModel profile) primitives code accepted
    identity identity_typed PUnit.unit True.intro
  rw [same] at formed
  exact formed

def context : CCtx Tower.Head 4 := .snoc (.snoc baseContext.source motive) (constructor.rename wk)

theorem context_formed : CCtxFormed theory context :=
  .snoc (.snoc baseContext.formed motive_formed)
    (constructor_formed.rename (CCtxRen.wk baseContext.source motive))

theorem constructor_reference_formed : CIsType theory baseContext.source constructor := by
  rw [constructor_exact]
  apply CIsType.pi (Programs.Annotated.levelModel profile)
    ⟨.sort Tower.zero, .sort _, Programs.Annotated.Functions.natural_typed profile⟩
  apply CIsType.pi (Programs.Annotated.levelModel profile)
    ⟨level, .sort _,
      CDerivable.appElim
        (show CTyped theory (.snoc baseContext.source (.const natName)) (.var 1)
          (.pi (.const natName) (.head level)) from .var 1) (.var 0)⟩
  exact ⟨level, .sort _,
    CDerivable.appElim
      (show CTyped theory (.snoc (.snoc baseContext.source (.const natName)) (.app (.var 1) (.var 0)))
        (.var 2) (.pi (.const natName) (.head level)) from .var 2) (.var 1)⟩

theorem reference_context_formed : CCtxFormed theory context :=
  .snoc (.snoc baseContext.formed motive_formed)
    (constructor_reference_formed.rename (CCtxRen.wk baseContext.source motive))

def images : CSub Tower.Head 2 4 := fun index => .var index.succ.succ

theorem images_typed : CSubstMor theory baseContext.source context images := by
  intro index
  fin_cases index
  · exact .var 2
  · exact .var 3

theorem motive_typed : CTyped theory context (.var 1)
    (motiveType indexing (types.family.subst images) (.const natName) resultLevel) := .var 1

theorem constructor_typed : CTyped theory context (.var 0)
    (constructorType indexing containers code (types.map (CTm.subst images)) PUnit.unit) := by
  have variableTyped : CTyped theory context (.var 0) ((constructor.rename wk).rename wk) := .var 0
  simpa only [constructor, constructorType, code, TypeSyntax.map, TypeSyntax.weaken,
    types, Indexing.familyAt, indexing, indices, IndexedContainerAnnotatedFormationControls.lengthTerm,
    weakenEnvironment, mapEnvironment, CTm.rename, CTm.subst, images, wk, liftRen,
    Fin.cases_zero, Fin.cases_succ] using variableTyped

def method : CTm Tower.Head 4 :=
  methodBody indexing containers code (types.map (CTm.subst images)) PUnit.unit (.var 1) (.var 0) []

theorem method_formed : CIsType theory context method :=
  methodBody_formed (Programs.Annotated.levelModel profile) methods code accepted images images_typed
    PUnit.unit True.intro (.var 1) (.var 0) [] motive_typed constructor_typed (by simp)

def expected : CTm Tower.Head 4 :=
  .pi (.const natName) (.pi (.app (.var 3) (.var 0))
    (.pi (.app (.app (.var 3) (.var 1)) (.var 0))
      (.app (.app (.var 4) (.var 2)) (.app (.app (.var 3) (.var 2)) (.var 1)))))

theorem method_exact : method = expected := by decide +kernel

theorem distinct_universes : level ≠ resultLevel := by decide +kernel

def wrongIndex : CTm Tower.Head 4 :=
  .pi (.const natName) (.pi (.app (.var 3) (.var 0))
    (.pi (.app (.app (.var 3) (.var 0)) (.var 0))
      (.app (.app (.var 4) (.var 2)) (.app (.app (.var 3) (.var 2)) (.var 1)))))

theorem changed_hypothesis_index_separated : method ≠ wrongIndex := by decide +kernel

open IndexedContainerAnnotatedFormationControls.Formation (Base Const operations lex)

abbrev ambientCarriers : HOL.Ctx Base :=
  [operations.number ⇒ operations.element ⇒ operations.element,
    operations.number ⇒ operations.element ⇒ (operations.result ⇒ .prop),
    operations.number ⇒ operations.elementPredicate, operations.elementPredicate]

def methodCarriers : MethodCarriers I registry Base where
  toFieldCarriers := carriers
  directHypothesis := operations.result
  nestedHypothesis _ _ absent := by cases absent

def generatedSource : CCtx Tower.Head (methodCarriers.context code ambientCarriers []).length :=
  generatedMethodSource (Γ := ambientCarriers) methodCarriers indexing containers code context
    (types.map (CTm.subst images)) PUnit.unit (.var 1) (.var 0) [] [] rfl

theorem generated_formed : CCtxFormed theory generatedSource :=
  generatedMethodSource_formed (Γ := ambientCarriers) (Programs.Annotated.levelModel profile) methodCarriers methods code accepted
    context context_formed images images_typed PUnit.unit True.intro
    (.var 1) (.var 0) [] motive_typed constructor_typed (by simp) [] rfl

def readContext := readMethodContext? (Γ := ambientCarriers) (lex := lex) methodCarriers indexing containers code context
  (types.map (CTm.subst images)) PUnit.unit (.var 1) (.var 0) [] [] rfl generated_formed

theorem complete_context_accepted : readContext.isSome = true := by decide +kernel
def guardedContext := readContext.get complete_context_accepted

def expectedContext : CCtx Tower.Head 7 :=
  .snoc (.snoc (.snoc context (.const natName)) (.app (.var 3) (.var 0)))
    (.app (.app (.var 3) (.var 1)) (.var 0))

theorem context_exact : guardedContext.source = expectedContext := by decide +kernel

theorem expected_context_formed : CCtxFormed theory expectedContext := by
  apply CCtxFormed.snoc
  · apply CCtxFormed.snoc
    · exact .snoc reference_context_formed
        ⟨.sort Tower.zero, .sort _, Programs.Annotated.Functions.natural_typed profile⟩
    · have family : CTyped theory (.snoc context (.const natName)) (.var 3)
          (.pi (.const natName) (.head level)) := .var 3
      exact ⟨level, .sort _, .appElim family (.var 0)⟩
  · have predicate : CTyped theory
        (.snoc (.snoc context (.const natName)) (.app (.var 3) (.var 0))) (.var 3)
        (.pi (.const natName) (.pi (.app (.var 5) (.var 0)) (.head resultLevel))) := .var 3
    have atIndex := CDerivable.appElim predicate
      (show CTyped theory (.snoc (.snoc context (.const natName)) (.app (.var 3) (.var 0)))
        (.var 1) (.const natName) from .var 1)
    exact ⟨resultLevel, .sort _, .appElim atIndex (.var 0)⟩

def contextCertificate : Programs.Annotated.JudgmentReplay.ContextCertificate profile 7 := by
  annotated_context_certificate 18000 expected_context_formed

theorem generated_context_checked : Programs.Annotated.JudgmentReplay.checkContext profile
    guardedContext.source contextCertificate = true := by decide +kernel

def wrongMethodCarriers : MethodCarriers I registry Base :=
  {methodCarriers with directHypothesis := operations.vector}

theorem wrong_generated_formed : CCtxFormed theory
    (generatedMethodSource (Γ := ambientCarriers) wrongMethodCarriers indexing containers code context
      (types.map (CTm.subst images)) PUnit.unit (.var 1) (.var 0) [] [] rfl) :=
  generatedMethodSource_formed (Γ := ambientCarriers) (Programs.Annotated.levelModel profile) wrongMethodCarriers methods code accepted
    context context_formed images images_typed PUnit.unit True.intro
    (.var 1) (.var 0) [] motive_typed constructor_typed (by simp) [] rfl

def wrongRead := readMethodContext? (Γ := ambientCarriers) (lex := lex) wrongMethodCarriers indexing containers code context
  (types.map (CTm.subst images)) PUnit.unit (.var 1) (.var 0) [] [] rfl wrong_generated_formed

theorem incompatible_hypothesis_carrier_refused : wrongRead.isNone = true := by decide +kernel

theorem wrong_hypothesis_context_refused : Programs.Annotated.JudgmentReplay.checkContext profile
    (.snoc (.snoc (.snoc context (.const natName)) (.app (.var 3) (.var 0)))
      (.app (.app (.var 3) (.var 0)) (.var 0))) contextCertificate = false := by decide +kernel

theorem source_substitution {n : Nat} (caller : CSub Tower.Head 4 n) :
    method.subst caller = methodBody indexing containers code
      ((types.map (CTm.subst images)).map (CTm.subst caller)) PUnit.unit
      (caller 1) (caller 0) [] := by
  simpa only [method, mapEnvironment, CTm.subst, List.map_nil] using
    methodBody_substitute indexing containers code (types.map (CTm.subst images)) PUnit.unit
      (.var 1) (.var 0) [] caller

end Source

#print axioms Source.method_formed
#print axioms Source.method_exact
#print axioms Source.generated_context_checked
#print axioms Source.incompatible_hypothesis_carrier_refused

end Mettapedia.GSLT.LanguageDef.IndexedContainerAnnotatedMethodFormationControls
