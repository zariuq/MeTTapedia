import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllAnnotatedTransport
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerAnnotatedMethodContexts
import Mettapedia.GSLT.LanguageDef.IndexedContainerAnnotatedFormationControls

/-!
# A concrete native-Vector provider for complete method formation

The registered field is the actual native Vec type. Its complete bundle is
the existing universe-valued All program with an explicit result level.
Native declaration typing and the formed All program discharge the primitive
contracts. The original mixed description then forms all five fields and
three queued IHs. Predicate reading and actual case-method construction remain
separate from this open source-interface formation result.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorMethodFormation

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies
open IndexedPolynomial.Description IndexedPositiveContainer IndexedContainerAnnotated
open NativeVectorAll.Annotated

abbrev I := IndexedContainerAnnotatedFormationControls.I
abbrev registry := IndexedContainerAnnotatedFormationControls.registry
abbrev indexing := IndexedContainerAnnotatedFormationControls.indexing
abbrev code := IndexedContainerAnnotatedFormationControls.code
abbrev types := IndexedContainerAnnotatedFormationControls.Formation.types

def containers (result : LevelExpr Nat) : RegistrySyntax I registry Tower.Head :=
  { IndexedContainerAnnotatedFormationControls.containers with
    bundleType := by
      intro context n name entry registered output environment A predicate field
      obtain rfl := IndexedPositiveContainerGuestControls.Vectors.registered_entry registered
      exact Formation.allType result A predicate (IndexedContainerAnnotatedFormationControls.lengthTerm output environment) field
    bundleType_substitute := by
      intro context n m name entry registered output environment A predicate field images
      obtain rfl := IndexedPositiveContainerGuestControls.Vectors.registered_entry registered
      rw [Formation.allType_substitute, IndexedContainerAnnotatedFormationControls.lengthTerm_substitute] }

def sourceContext (element : LevelExpr Nat) : CCtx Tower.Head 2 :=
  .snoc (.snoc .nil (Profile.elementSort element)) (Profile.elementSort element)

theorem sourceContext_formed (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection) :
    CCtxFormed (Profile.church element result enabled) (sourceContext element) :=
  .snoc (.snoc .nil ⟨.sort (.succ element), .sort _, .headType (.sort _)⟩)
    ⟨.sort (.succ element), .sort _, .headType (.sort _)⟩

theorem length_typed {element result : LevelExpr Nat} {enabled : Programs.ComputationProfiles.Selection}
    {n : Nat} {ambient : CCtx Tower.Head n} {context : List I.SortCode}
    {environment : TermEnvironment I Tower.Head n context} {dataTypes : I.SortCode → CTm Tower.Head n}
    (typed : EnvironmentTyped (P := Profile.church element result enabled) ambient dataTypes environment)
    (expression : VectorControl.LengthExpr context) :
    CTyped (Profile.church element result enabled) ambient
      (IndexedContainerAnnotatedFormationControls.lengthTerm expression environment) (dataTypes .length) := by
  induction expression with
  | here => exact typed.1
  | there _ previous => exact previous typed.2

theorem primitives (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection) :
    MethodPrimitives (P := Profile.church element result enabled) (sourceContext element) types indexing
      (containers result) PUnit.unit (.sort element) (.sort result) (fun _ => True) where
  isUniverse := .sort _
  data sort := by
    cases sort with
    | length => exact ⟨.sort Tower.zero, .sort _, Profile.natural_typed element result enabled⟩
    | payload => exact ⟨.sort element, .sort _, .var 1⟩
  family := .var 0
  indices := True.intro
  container := by
    intro n target images morphism context name entry registered output environment typed A elementTyped
    obtain rfl := IndexedPositiveContainerGuestControls.Vectors.registered_entry registered
    exact ⟨.sort element, .sort _, Profile.vector_typed element result enabled elementTyped (length_typed typed output)⟩
  resultUniverse := .sort _
  bundle := by
    intro n target images morphism context name entry registered output environment typed A predicate field
      elementTyped predicateTyped fieldTyped
    obtain rfl := IndexedPositiveContainerGuestControls.Vectors.registered_entry registered
    exact ⟨.sort result, .sort _, Formation.allType_typed element result enabled
      elementTyped predicateTyped (length_typed typed output) fieldTyped⟩

def constructor (result : LevelExpr Nat) : CTm Tower.Head 2 :=
  constructorType indexing (containers result) code types PUnit.unit

theorem constructor_formed (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection) :
    CIsType (Profile.church element result enabled) (sourceContext element) (constructor result) := by
  have identity : CSubstMor (Profile.church element result enabled) (sourceContext element) (sourceContext element) CTm.ids := by
    intro index
    simpa only [CTm.subst_ids, CTm.ids] using
      (CDerivable.var (P := Profile.church element result enabled) (Γ := sourceContext element) index)
  have same : types.map (CTm.subst CTm.ids) = types := by
    simp only [TypeSyntax.map, CTm.subst_ids]
  have formed := constructorType_formed (Profile.levelModel element result enabled)
    (primitives element result enabled).toConstructorPrimitives code
    (IndexedContainerAnnotatedFormationControls.Formation.indices_admitted code) CTm.ids identity PUnit.unit True.intro
  rw [same] at formed
  exact formed

def motive (result : LevelExpr Nat) : CTm Tower.Head 2 :=
  motiveType indexing types.family PUnit.unit (.sort result)

theorem motive_formed (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection) :
    CIsType (Profile.church element result enabled) (sourceContext element) (motive result) :=
  CIsType.pi (Profile.levelModel element result enabled)
    ⟨.sort element, .sort _, .var 0⟩ ⟨.sort (.succ result), .sort _, .headType (.sort _)⟩

def context (element result : LevelExpr Nat) : CCtx Tower.Head 4 :=
  .snoc (.snoc (sourceContext element) (motive result)) ((constructor result).rename wk)

theorem context_formed (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection) :
    CCtxFormed (Profile.church element result enabled) (context element result) :=
  .snoc (.snoc (sourceContext_formed element result enabled) (motive_formed element result enabled))
    ((constructor_formed element result enabled).rename (CCtxRen.wk _ _))

def images : CSub Tower.Head 2 4 := fun index => .var index.succ.succ

theorem images_typed (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection) :
    CSubstMor (Profile.church element result enabled) (sourceContext element) (context element result) images := by
  intro index
  fin_cases index
  · exact .var 2
  · exact .var 3

private theorem images_action (term : CTm Tower.Head 2) :
    term.subst images = term.rename (fun index => index.succ.succ) := by
  unfold images
  simpa only [CTm.subst_ids, CTm.ids, CTm.rename] using
    (CTm.rename_subst (fun index => index.succ.succ) CTm.ids term).symm

theorem constructor_typed (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection) :
    CTyped (Profile.church element result enabled) (context element result) (.var 0)
      (constructorType indexing (containers result) code (types.map (CTm.subst images)) PUnit.unit) := by
  have natural : (constructor result).subst images =
      constructorType indexing (containers result) code (types.map (CTm.subst images)) PUnit.unit :=
    constructorType_substitute indexing (containers result) code types PUnit.unit images
  rw [← natural, images_action]
  have typed : CTyped (Profile.church element result enabled) (context element result) (.var 0)
      (((constructor result).rename wk).rename wk) := .var 0
  simpa only [CTm.rename_comp, wk] using typed

theorem motive_typed (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection) :
    CTyped (Profile.church element result enabled) (context element result) (.var 1)
      (motiveType indexing (types.family.subst images) PUnit.unit (.sort result)) := .var 1

def method (result : LevelExpr Nat) : CTm Tower.Head 4 :=
  methodBody indexing (containers result) code (types.map (CTm.subst images)) PUnit.unit (.var 1) (.var 0) []

theorem method_formed (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection) :
    CIsType (Profile.church element result enabled) (context element result) (method result) :=
  methodBody_formed (Profile.levelModel element result enabled) (primitives element result enabled) code
    (IndexedContainerAnnotatedFormationControls.Formation.indices_admitted code) images (images_typed element result enabled)
    PUnit.unit True.intro (.var 1) (.var 0) [] (motive_typed element result enabled)
    (constructor_typed element result enabled) (by simp)

def completeContext (element result : LevelExpr Nat) :=
  methodContext indexing (containers result) code (context element result) (types.map (CTm.subst images))
    PUnit.unit (.var 1) (.var 0) []

theorem completeContext_formed (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection) :
    CCtxFormed (Profile.church element result enabled) (completeContext element result).2 :=
  methodContext_formed (Profile.levelModel element result enabled) (primitives element result enabled) code
    (IndexedContainerAnnotatedFormationControls.Formation.indices_admitted code) (context_formed element result enabled)
    images (images_typed element result enabled) PUnit.unit True.intro (.var 1) (.var 0) []
    (motive_typed element result enabled) (constructor_typed element result enabled) (by simp)

theorem original_fields_and_hypotheses :
    fieldCount code = 5 ∧ hypothesisCount code = 3 := by decide +kernel

theorem completeContext_size (element result : LevelExpr Nat) : (completeContext element result).1 = 12 := by
  rw [completeContext, methodContext_size]
  decide +kernel

theorem separate_level_method :
    CIsType (Profile.church (.param 0) (.param 2) (fun _ => false))
      (context (.param 0) (.param 2)) (method (.param 2)) :=
  method_formed (.param 0) (.param 2) (fun _ => false)

theorem separate_level_context :
    CCtxFormed (Profile.church (.param 0) (.param 2) (fun _ => false))
      (completeContext (.param 0) (.param 2)).2 :=
  completeContext_formed (.param 0) (.param 2) (fun _ => false)

theorem unraised_capacity_refused :
    ¬ (Programs.ComputationProfiles.rules (fun _ => false)).cumulative
      (.sort (.succ (.param 1))) (.sort (.max (.param 0) (.param 1))) := by
  intro insufficient
  have atZero := insufficient (fun _ => 0)
  have impossible : 1 ≤ 0 := atZero
  omega

theorem distinct_result_annotation :
    Formation.universeMotive (.param 0) (.var 0 : CTm Tower.Head 1) ≠
      Formation.universeMotive (.param 2) (.var 0 : CTm Tower.Head 1) := by decide +kernel

def naturalPredicate {n : Nat} : CTm Tower.Head n :=
  .lam (.const natName) (.id (.const natName) (.var 0) (.var 0))

theorem naturalPredicate_typed (result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection)
    {n : Nat} {ambient : CCtx Tower.Head n} :
    CTyped (Profile.church Tower.zero result enabled) ambient naturalPredicate
      (.pi (.const natName) (Formation.resultSort result)) := by
  apply CDerivable.lamIntro (Profile.natural_typed Tower.zero result enabled) (.sort _)
    (Formation.product_atBound Tower.zero result enabled (Formation.natural_atBound Tower.zero result enabled)
      (Formation.resultSort_typed Tower.zero result enabled)) (.sort _)
  refine .cumul (.idForm (Profile.natural_typed Tower.zero result enabled) (.sort _) (.var 0) (.var 0)) ?_
  change ∀ valuation : Nat → Nat, 0 ≤ result.eval valuation
  exact fun _ => Nat.zero_le _

def closedAll (result : LevelExpr Nat) : CTm Tower.Head 0 :=
  Formation.allType result (.const natName) naturalPredicate (.const zeroName)
    (Programs.Annotated.Append.nil (.const natName))

theorem closedAll_typed (result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection) :
    CTyped (Profile.church Tower.zero result enabled) .nil (closedAll result) (Formation.resultSort result) :=
  Formation.allType_typed Tower.zero result enabled (Profile.natural_typed Tower.zero result enabled)
    (naturalPredicate_typed result enabled) (Profile.zero_typed Tower.zero result enabled)
    (Profile.nil_typed Tower.zero result enabled (Profile.natural_typed Tower.zero result enabled))

theorem closed_original_all_typed :
    CTyped (Profile.church Tower.zero (.param 0) (fun _ => false)) .nil
      (NativeVectorAll.Annotated.allType (.const natName) naturalPredicate (.const zeroName)
        (Programs.Annotated.Append.nil (.const natName))) (Formation.resultSort (.param 0)) :=
  Formation.original_allType_typed Tower.zero (fun _ => false)
    (Profile.natural_typed Tower.zero (.param 0) (fun _ => false))
    (naturalPredicate_typed (.param 0) (fun _ => false))
    (Profile.zero_typed Tower.zero (.param 0) (fun _ => false))
    (Profile.nil_typed Tower.zero (.param 0) (fun _ => false)
      (Profile.natural_typed Tower.zero (.param 0) (fun _ => false)))

#print axioms primitives
#print axioms method_formed
#print axioms completeContext_formed
#print axioms unraised_capacity_refused
#print axioms closed_original_all_typed

end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorMethodFormation
