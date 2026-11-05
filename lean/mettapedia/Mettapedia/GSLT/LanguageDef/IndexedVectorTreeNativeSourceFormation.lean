import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorMethodFormation
import Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedPositiveVectorLowering

/-!
# Source formation for the complete parsed Vector-tree family

Both constructor ordinals come from the parsed solved/branch inventory. The
source ambient context binds the answer type, a separate family type, the
motive, both constructors and both case methods. The registered Vector and
its All hypothesis use the existing native formation provider.

The family is a source parameter here. Formation does not identify it with a
least predicate, establish a semantic carrier interpretation, or install the
complete context in a model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeSourceFormation

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies
open IndexedPolynomial.Description IndexedPositiveContainer IndexedContainerAnnotated
open NativeVectorAll.Annotated

namespace Provider
export IndexedContainerNativeVectorMethodFormation
  (I registry indexing types containers sourceContext sourceContext_formed primitives motive motive_formed)
end Provider

def codes : List (Code Provider.I Provider.registry 0 []) :=
  ModuleSource.IndexedPositiveVectorLowering.Controls.family.constructors.map (fun constructor => constructor.body.erase)

theorem codes_length : codes.length = 2 := rfl

def code (occurrence : Fin 2) : Code Provider.I Provider.registry 0 [] :=
  codes.get ⟨occurrence.val, by simpa only [codes_length] using occurrence.isLt⟩

theorem solved_code : code 0 =
    ModuleSource.IndexedPositiveVectorLowering.Controls.solved.body.erase := rfl

theorem branch_code : code 1 =
    ModuleSource.IndexedPositiveVectorLowering.Controls.branch.body.erase := rfl

def constructor (result : LevelExpr Nat) (occurrence : Fin 2) : CTm Tower.Head 2 :=
  constructorType Provider.indexing (Provider.containers result) (code occurrence) Provider.types PUnit.unit

theorem constructor_formed (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection)
    (occurrence : Fin 2) :
    CIsType (Profile.church element result enabled) (Provider.sourceContext element) (constructor result occurrence) := by
  have identity : CSubstMor (Profile.church element result enabled) (Provider.sourceContext element)
      (Provider.sourceContext element) CTm.ids := by
    intro index
    simpa only [CTm.subst_ids, CTm.ids] using
      (CDerivable.var (P := Profile.church element result enabled) (Γ := Provider.sourceContext element) index)
  have same : Provider.types.map (CTm.subst CTm.ids) = Provider.types := by
    simp only [TypeSyntax.map, CTm.subst_ids]
  have formed := constructorType_formed (Profile.levelModel element result enabled)
    (Provider.primitives element result enabled).toConstructorPrimitives (code occurrence)
    (IndexedContainerAnnotatedFormationControls.Formation.indices_admitted (code occurrence))
    CTm.ids identity PUnit.unit True.intro
  rw [same] at formed
  exact formed

/-- The newest slots are branch, solved and motive; the two type parameters
remain independently bound at slots three and four. -/
def coreContext (element result : LevelExpr Nat) : CCtx Tower.Head 5 :=
  .snoc (.snoc (.snoc (Provider.sourceContext element) (Provider.motive result))
    ((constructor result 0).rename wk)) (((constructor result 1).rename wk).rename wk)

theorem coreContext_formed (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection) :
    CCtxFormed (Profile.church element result enabled) (coreContext element result) :=
  .snoc (.snoc (.snoc (Provider.sourceContext_formed element result enabled)
    (Provider.motive_formed element result enabled))
    ((constructor_formed element result enabled 0).rename (CCtxRen.wk _ _)))
    (((constructor_formed element result enabled 1).rename (CCtxRen.wk _ _)).rename (CCtxRen.wk _ _))

def coreImages : CSub Tower.Head 2 5 := fun index => .var index.succ.succ.succ

theorem coreImages_typed (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection) :
    CSubstMor (Profile.church element result enabled) (Provider.sourceContext element)
      (coreContext element result) coreImages := by
  intro index
  fin_cases index
  · exact .var 3
  · exact .var 4

private theorem coreImages_action (term : CTm Tower.Head 2) :
    term.subst coreImages = ((term.rename wk).rename wk).rename wk := by
  let placement : Ren 2 5 := fun index => index.succ.succ.succ
  have natural := (CTm.rename_subst placement CTm.ids term).symm
  calc
    term.subst coreImages = term.subst (fun index => (CTm.ids index).rename placement) :=
      CTm.subst_ext (fun _ => rfl) term
    _ = term.rename placement := by simpa only [CTm.subst_ids] using natural
    _ = ((term.rename wk).rename wk).rename wk := by
      rw [CTm.rename_comp, CTm.rename_comp]
      apply CTm.rename_ext
      intro index
      rfl

def coreConstructor (occurrence : Fin 2) : CTm Tower.Head 5 :=
  .var ⟨1 - occurrence.val, by omega⟩

theorem coreConstructor_typed (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection)
    (occurrence : Fin 2) :
    CTyped (Profile.church element result enabled) (coreContext element result) (coreConstructor occurrence)
      (constructorType Provider.indexing (Provider.containers result) (code occurrence)
        (Provider.types.map (CTm.subst coreImages)) PUnit.unit) := by
  have natural : (constructor result occurrence).subst coreImages =
      constructorType Provider.indexing (Provider.containers result) (code occurrence)
        (Provider.types.map (CTm.subst coreImages)) PUnit.unit := by
    simpa only [constructor, mapEnvironment] using
      (constructorType_substitute Provider.indexing (Provider.containers result)
        (code occurrence) Provider.types PUnit.unit coreImages)
  rw [← natural, coreImages_action]
  fin_cases occurrence
  · exact .var 1
  · exact .var 0

theorem coreMotive_typed (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection) :
    CTyped (Profile.church element result enabled) (coreContext element result) (.var 2)
      (motiveType Provider.indexing (Provider.types.family.subst coreImages) PUnit.unit (.sort result)) := .var 2

def method (result : LevelExpr Nat) (occurrence : Fin 2) : CTm Tower.Head 5 :=
  methodBody Provider.indexing (Provider.containers result) (code occurrence)
    (Provider.types.map (CTm.subst coreImages)) PUnit.unit (.var 2) (coreConstructor occurrence) []

theorem method_formed (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection)
    (occurrence : Fin 2) :
    CIsType (Profile.church element result enabled) (coreContext element result) (method result occurrence) :=
  methodBody_formed (Profile.levelModel element result enabled) (Provider.primitives element result enabled)
    (code occurrence) (IndexedContainerAnnotatedFormationControls.Formation.indices_admitted (code occurrence))
    coreImages (coreImages_typed element result enabled) PUnit.unit True.intro (.var 2)
    (coreConstructor occurrence) [] (coreMotive_typed element result enabled)
    (coreConstructor_typed element result enabled occurrence) (by simp)

theorem solved_method (result : LevelExpr Nat) : method result 0 =
    .pi (.var 4) (.app (.var 3) (.app (.var 2) (.var 0))) := by
  change methodBody Provider.indexing (Provider.containers result)
    (.data .payload (.result ()) : Code Provider.I Provider.registry 0 [])
    (Provider.types.map (CTm.subst coreImages)) PUnit.unit (.var 2) (coreConstructor 0) [] = _
  simp only [methodBody, hypotheses, List.map_nil]
  rfl

theorem branch_method (result : LevelExpr Nat) : method result 1 =
    .pi (.const natName) (.pi (vector (.var 4) (.var 0))
      (.pi (Formation.allType result (.var 5) (.var 4) (.var 1) (.var 0))
        (.app (.var 5) (.app (.app (.var 3) (.var 2)) (.var 1))))) := by
  change methodBody Provider.indexing (Provider.containers result)
    (.data .length (.nested "Vector" VectorControl.entry (by simp [Provider.registry, VectorControl.registry])
      .here () (.result ())) : Code Provider.I Provider.registry 0 [])
    (Provider.types.map (CTm.subst coreImages)) PUnit.unit (.var 2) (coreConstructor 1) [] = _
  simp only [methodBody, hypotheses, List.map_nil, List.nil_append]
  rfl

/-- Both case-method assumptions follow the complete two-constructor ambient
context. Their bodies remain obligations of any eventual installation. -/
def context (element result : LevelExpr Nat) : CCtx Tower.Head 7 :=
  .snoc (.snoc (coreContext element result) (method result 0)) ((method result 1).rename wk)

theorem context_formed (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection) :
    CCtxFormed (Profile.church element result enabled) (context element result) :=
  .snoc (.snoc (coreContext_formed element result enabled) (method_formed element result enabled 0))
    ((method_formed element result enabled 1).rename (CCtxRen.wk _ _))

def images : CSub Tower.Head 2 7 := fun index => .var index.succ.succ.succ.succ.succ

theorem images_typed (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection) :
    CSubstMor (Profile.church element result enabled) (Provider.sourceContext element)
      (context element result) images := by
  intro index
  fin_cases index
  · exact .var 5
  · exact .var 6

private theorem images_action (term : CTm Tower.Head 2) :
    term.subst images = ((((term.rename wk).rename wk).rename wk).rename wk).rename wk := by
  let placement : Ren 2 7 := fun index => index.succ.succ.succ.succ.succ
  have natural := (CTm.rename_subst placement CTm.ids term).symm
  calc
    term.subst images = term.subst (fun index => (CTm.ids index).rename placement) :=
      CTm.subst_ext (fun _ => rfl) term
    _ = term.rename placement := by simpa only [CTm.subst_ids] using natural
    _ = ((((term.rename wk).rename wk).rename wk).rename wk).rename wk := by
      rw [CTm.rename_comp, CTm.rename_comp, CTm.rename_comp, CTm.rename_comp]
      apply CTm.rename_ext
      intro index
      rfl

def constructorAt (occurrence : Fin 2) : CTm Tower.Head 7 :=
  .var ⟨3 - occurrence.val, by omega⟩

theorem constructorAt_typed (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection)
    (occurrence : Fin 2) :
    CTyped (Profile.church element result enabled) (context element result) (constructorAt occurrence)
      (constructorType Provider.indexing (Provider.containers result) (code occurrence)
        (Provider.types.map (CTm.subst images)) PUnit.unit) := by
  have natural : (constructor result occurrence).subst images =
      constructorType Provider.indexing (Provider.containers result) (code occurrence)
        (Provider.types.map (CTm.subst images)) PUnit.unit := by
    simpa only [constructor, mapEnvironment] using
      (constructorType_substitute Provider.indexing (Provider.containers result)
        (code occurrence) Provider.types PUnit.unit images)
  rw [← natural, images_action]
  fin_cases occurrence
  · exact .var 3
  · exact .var 2

theorem motive_typed (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection) :
    CTyped (Profile.church element result enabled) (context element result) (.var 4)
      (motiveType Provider.indexing (Provider.types.family.subst images) PUnit.unit (.sort result)) := .var 4

def caseAt (occurrence : Fin 2) : CTm Tower.Head 7 :=
  .var ⟨1 - occurrence.val, by omega⟩

theorem caseAt_typed (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection)
    (occurrence : Fin 2) :
    CTyped (Profile.church element result enabled) (context element result) (caseAt occurrence)
      (((method result occurrence).rename wk).rename wk) := by
  fin_cases occurrence
  · exact .var 1
  · exact .var 0

def completeContext (element result : LevelExpr Nat) (occurrence : Fin 2) :=
  methodContext Provider.indexing (Provider.containers result) (code occurrence) (context element result)
    (Provider.types.map (CTm.subst images)) PUnit.unit (.var 4) (constructorAt occurrence) []

theorem completeContext_formed (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection)
    (occurrence : Fin 2) :
    CCtxFormed (Profile.church element result enabled) (completeContext element result occurrence).2 :=
  methodContext_formed (Profile.levelModel element result enabled) (Provider.primitives element result enabled)
    (code occurrence) (IndexedContainerAnnotatedFormationControls.Formation.indices_admitted (code occurrence))
    (context_formed element result enabled) images (images_typed element result enabled) PUnit.unit True.intro
    (.var 4) (constructorAt occurrence) [] (motive_typed element result enabled)
    (constructorAt_typed element result enabled occurrence) (by simp)

theorem solved_context (element result : LevelExpr Nat) : completeContext element result 0 =
    ⟨8, .snoc (context element result) (.var 6)⟩ := by
  change methodContext Provider.indexing (Provider.containers result)
    (.data .payload (.result ()) : Code Provider.I Provider.registry 0 [])
    (context element result) (Provider.types.map (CTm.subst images)) PUnit.unit (.var 4)
    (constructorAt 0) [] = _
  simp only [methodContext, hypothesesContext, List.map_nil]
  rfl

set_option maxRecDepth 2048 in
theorem branch_context (element result : LevelExpr Nat) : completeContext element result 1 =
    ⟨10, .snoc (.snoc (.snoc (context element result) (.const natName)) (vector (.var 6) (.var 0)))
      (Formation.allType result (.var 7) (.var 6) (.var 1) (.var 0))⟩ := by
  change methodContext Provider.indexing (Provider.containers result)
    (.data .length (.nested "Vector" VectorControl.entry (by simp [Provider.registry, VectorControl.registry])
      .here () (.result ())) : Code Provider.I Provider.registry 0 [])
    (context element result) (Provider.types.map (CTm.subst images)) PUnit.unit (.var 4)
    (constructorAt 1) [] = _
  simp only [methodContext, hypothesesContext, List.map_nil, List.nil_append]
  rfl

theorem solved_fields_and_hypotheses : fieldCount (code 0) = 1 ∧ hypothesisCount (code 0) = 0 := by
  decide +kernel

theorem branch_fields_and_hypotheses : fieldCount (code 1) = 2 ∧ hypothesisCount (code 1) = 1 := by
  decide +kernel

theorem solved_context_size (element result : LevelExpr Nat) : (completeContext element result 0).1 = 8 := by
  rw [completeContext, methodContext_size]
  decide +kernel

theorem branch_context_size (element result : LevelExpr Nat) : (completeContext element result 1).1 = 10 := by
  rw [completeContext, methodContext_size]
  decide +kernel

theorem independent_constructor_slots : coreConstructor 0 ≠ coreConstructor 1 := by decide +kernel

theorem branch_hypothesis_cannot_be_omitted : hypothesisCount (code 1) ≠ 0 := by decide +kernel

#print axioms constructor_formed
#print axioms context_formed
#print axioms completeContext_formed
#print axioms branch_hypothesis_cannot_be_omitted

end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeSourceFormation
