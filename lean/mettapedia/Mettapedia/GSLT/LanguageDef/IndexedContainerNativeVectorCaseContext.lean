import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorMethodEvidence
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllAnnotatedRenaming
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerGuardedSourceEquations

/-!
# An input case method before the original field/IH telescope

The method argument has the original formed method type. Adding it to the
four-parameter ambient context precedes the five fields and three queued IHs.
The original twelve-binder context embeds by a typed renaming that fixes its
eight field/IH positions. Source and predicate guards remain explicit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorCaseContext

open Mettapedia.Logic
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation TypedEquality.Annotated AnnotatedPredicateReading IndexedContainerAnnotated
open IndexedContainerNativeVectorMethodReading
local infixr:60 " ⇒ " => HOL.Ty.arr

abbrev methodCarrier := N ⇒ E ⇒ E ⇒ V ⇒ E ⇒ W ⇒ W ⇒ W ⇒ W
def theory := NativeVectorAll.Annotated.Profile.church elementLevel resultLevel (fun _ => false)
def methodType : CTm Tower.Head 4 :=
  .pi (.const NativeNaturalVectorFamilies.natName)
    (.pi (.var 3) (.pi (.var 5)
      (.pi (NativeVectorAll.Annotated.vector (.var 5) (.var 2))
        (.pi (.var 6) (.pi (.app (.var 6) (.var 3))
          (.pi (NativeVectorAll.Annotated.Formation.allType resultLevel (.var 8) (.var 7) (.var 5) (.var 2))
            (.pi (.app (.var 8) (.var 2))
              (.app (.var 9)
                (.app (.app (.app (.app (.app (.var 8) (.var 7)) (.var 6)) (.var 5)) (.var 4)) (.var 3))))))))))

theorem method_generated : methodType = IndexedContainerNativeVectorMethodFormation.method resultLevel := by
  symm
  simp only [IndexedContainerNativeVectorMethodFormation.method,
    IndexedContainerNativeVectorMethodFormation.code, IndexedContainerAnnotatedFormationControls.code,
    IndexedPositiveContainerGuestControls.Vectors.Mixed.code, IndexedPositiveContainerGuestControls.Vectors.Mixed.source,
    ModuleSource.IndexedPositiveVectorLowering.Code.erase, methodBody, hypotheses,
    List.map_cons, List.map_nil, List.nil_append, List.cons_append]
  rfl

def baseRead := Reader.readContext? lex ambient
  (IndexedContainerNativeVectorMethodFormation.context elementLevel resultLevel)
theorem base_readable : baseRead.isSome = true := by decide +kernel

def base : GuardedContext theory lex ambient where
  source := IndexedContainerNativeVectorMethodFormation.context elementLevel resultLevel
  telescope := (baseRead.get base_readable).val
  formed := IndexedContainerNativeVectorMethodFormation.context_formed elementLevel resultLevel (fun _ => false)
  reading := (baseRead.get base_readable).property

def methodRead := Reader.readTyped? lex ambient methodType (methodCarrier ⇒ .prop)
theorem method_readable : methodRead.isSome = true := by decide +kernel

theorem method_formed : CIsType theory base.source methodType :=
  method_generated.symm ▸ IndexedContainerNativeVectorMethodFormation.method_formed elementLevel resultLevel (fun _ => false)

def input := base.snoc (methodRead.get method_readable).val (methodRead.get method_readable).property method_formed
abbrev inputCarrier : HOL.Ctx Base := methodCarrier :: ambient

def images : CSub Tower.Head 2 inputCarrier.length := fun index => .var index.succ.succ.succ

theorem images_typed : CSubstMor theory (IndexedContainerNativeVectorMethodFormation.sourceContext elementLevel)
    input.source images := by
  intro index
  fin_cases index
  · exact .var 3
  · exact .var 4

private theorem images_action (term : CTm Tower.Head 2) :
    term.subst images = ((term.rename wk).rename wk).rename wk := by
  let placement : Ren 2 inputCarrier.length := fun index => index.succ.succ.succ
  have natural := (CTm.rename_subst placement CTm.ids term).symm
  calc
    term.subst images = term.subst (fun index => (CTm.ids index).rename placement) :=
      CTm.subst_ext (fun _ => rfl) term
    _ = term.rename placement := by simpa only [CTm.subst_ids] using natural
    _ = ((term.rename wk).rename wk).rename wk := by
      rw [CTm.rename_comp, CTm.rename_comp]
      apply CTm.rename_ext
      intro index
      rfl

def types := IndexedContainerNativeVectorMethodFormation.types.map (CTm.subst images)

theorem motive_typed : CTyped theory input.source (.var 2)
    (motiveType IndexedContainerNativeVectorMethodFormation.indexing
      (IndexedContainerNativeVectorMethodFormation.types.family.subst images) PUnit.unit (.sort resultLevel)) := .var 2

theorem constructor_typed : CTyped theory input.source (.var 1)
    (constructorType IndexedContainerNativeVectorMethodFormation.indexing
      (IndexedContainerNativeVectorMethodFormation.containers resultLevel)
      IndexedContainerNativeVectorMethodFormation.code types PUnit.unit) := by
  have natural : (constructorType IndexedContainerNativeVectorMethodFormation.indexing
      (IndexedContainerNativeVectorMethodFormation.containers resultLevel)
      IndexedContainerNativeVectorMethodFormation.code IndexedContainerNativeVectorMethodFormation.types PUnit.unit).subst images =
      constructorType IndexedContainerNativeVectorMethodFormation.indexing
        (IndexedContainerNativeVectorMethodFormation.containers resultLevel)
        IndexedContainerNativeVectorMethodFormation.code types PUnit.unit := by
    simpa only [types, mapEnvironment] using
      (constructorType_substitute IndexedContainerNativeVectorMethodFormation.indexing
        (IndexedContainerNativeVectorMethodFormation.containers resultLevel)
        IndexedContainerNativeVectorMethodFormation.code IndexedContainerNativeVectorMethodFormation.types PUnit.unit images)
  rw [← natural, images_action]
  exact .var 1

abbrev carrier : HOL.Ctx Base :=
  [W, W, W, E, V, E, E, N, methodCarrier, constructorCarrier, motiveCarrier, E ⇒ .prop, E ⇒ .prop]

theorem carrier_generated : carrier =
    carriers.context IndexedContainerNativeVectorMethodFormation.code inputCarrier [] := by decide +kernel

def source : CCtx Tower.Head carrier.length :=
  generatedMethodSource (Γ := inputCarrier) carriers IndexedContainerNativeVectorMethodFormation.indexing
    (IndexedContainerNativeVectorMethodFormation.containers resultLevel)
    IndexedContainerNativeVectorMethodFormation.code input.source types PUnit.unit (.var 2) (.var 1) [] [] rfl

theorem source_formed : CCtxFormed theory source :=
  generatedMethodSource_formed (NativeVectorAll.Annotated.Profile.levelModel elementLevel resultLevel (fun _ => false))
    carriers (IndexedContainerNativeVectorMethodFormation.primitives elementLevel resultLevel (fun _ => false))
    IndexedContainerNativeVectorMethodFormation.code
    (IndexedContainerAnnotatedFormationControls.Formation.indices_admitted IndexedContainerNativeVectorMethodFormation.code)
    input.source input.formed images images_typed PUnit.unit True.intro (.var 2) (.var 1) []
    motive_typed constructor_typed (by simp) [] rfl

def contextRead := Reader.readContext? lex carrier source
theorem context_readable : contextRead.isSome = true := by decide +kernel

theorem source_size : carrier.length = 13 := by decide +kernel

private def insertRen (tail : HOL.Ctx Base) (extra : HOL.Ty Base) :
    (front : HOL.Ctx Base) → HOL.Rename Base (front ++ tail) (front ++ extra :: tail)
  | [] => HOL.Rename.weaken
  | _ :: front => HOL.Rename.lift (insertRen tail extra front)

def nativeRen : HOL.Rename Base target carrier :=
  insertRen ambient methodCarrier [W, W, W, E, V, E, E, N]

def sourceRen (position : Fin 12) : Fin 13 :=
  if before : position.val < 8 then
    ⟨position.val, by omega⟩
  else
    ⟨position.val + 1, by have bound := position.isLt; omega⟩

def explicitSource : CCtx Tower.Head 13 :=
  .snoc (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc input.source
    (.const NativeNaturalVectorFamilies.natName)) (.var 4)) (.var 6))
    (NativeVectorAll.Annotated.vector (.var 6) (.var 2))) (.var 7))
    (.app (.var 7) (.var 3)))
    (NativeVectorAll.Annotated.Formation.allType resultLevel (.var 9) (.var 8) (.var 5) (.var 2)))
    (.app (.var 9) (.var 2))

private theorem source_pair :
    methodContext IndexedContainerNativeVectorMethodFormation.indexing
      (IndexedContainerNativeVectorMethodFormation.containers resultLevel)
      IndexedContainerNativeVectorMethodFormation.code input.source types PUnit.unit (.var 2) (.var 1) [] =
    ⟨13, explicitSource⟩ := by
  simp only [IndexedContainerNativeVectorMethodFormation.code, IndexedContainerAnnotatedFormationControls.code,
    IndexedPositiveContainerGuestControls.Vectors.Mixed.code, IndexedPositiveContainerGuestControls.Vectors.Mixed.source,
    ModuleSource.IndexedPositiveVectorLowering.Code.erase,
    IndexedContainerAnnotated.methodContext, IndexedContainerAnnotated.hypothesesContext,
    List.map_cons, List.map_nil, List.nil_append, List.cons_append]
  rfl

theorem source_explicit : source = explicitSource :=
  generatedMethodSource_eq carriers IndexedContainerNativeVectorMethodFormation.indexing
    (IndexedContainerNativeVectorMethodFormation.containers resultLevel)
    IndexedContainerNativeVectorMethodFormation.code input.source types PUnit.unit (.var 2) (.var 1)
    [] [] rfl explicitSource source_pair

def context : GuardedContext theory lex carrier where
  source := explicitSource
  telescope := (contextRead.get context_readable).val
  formed := source_explicit ▸ source_formed
  reading := source_explicit ▸ (contextRead.get context_readable).property

theorem context_generated : context.source = source := source_explicit.symm

def originalExplicitSource : CCtx Tower.Head 12 :=
  .snoc (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc base.source
    (.const NativeNaturalVectorFamilies.natName)) (.var 3)) (.var 5))
    (NativeVectorAll.Annotated.vector (.var 5) (.var 2))) (.var 6))
    (.app (.var 6) (.var 3)))
    (NativeVectorAll.Annotated.Formation.allType resultLevel (.var 8) (.var 7) (.var 5) (.var 2)))
    (.app (.var 8) (.var 2))

private theorem original_source_pair :
    methodContext IndexedContainerNativeVectorMethodFormation.indexing
      (IndexedContainerNativeVectorMethodFormation.containers resultLevel)
      IndexedContainerNativeVectorMethodFormation.code base.source
      (IndexedContainerNativeVectorMethodFormation.types.map (CTm.subst IndexedContainerNativeVectorMethodFormation.images))
      PUnit.unit (.var 1) (.var 0) [] = ⟨12, originalExplicitSource⟩ := by
  simp only [IndexedContainerNativeVectorMethodFormation.code, IndexedContainerAnnotatedFormationControls.code,
    IndexedPositiveContainerGuestControls.Vectors.Mixed.code, IndexedPositiveContainerGuestControls.Vectors.Mixed.source,
    ModuleSource.IndexedPositiveVectorLowering.Code.erase,
    IndexedContainerAnnotated.methodContext, IndexedContainerAnnotated.hypothesesContext,
    List.map_cons, List.map_nil, List.nil_append, List.cons_append]
  rfl

theorem original_source_explicit : guarded.source = originalExplicitSource := by
  change checkedSource = originalExplicitSource
  rw [IndexedContainerNativeVectorMethodEvidence.checked_source_generated]
  exact generatedMethodSource_eq carriers IndexedContainerNativeVectorMethodFormation.indexing
    (IndexedContainerNativeVectorMethodFormation.containers resultLevel)
    IndexedContainerNativeVectorMethodFormation.code base.source
    (IndexedContainerNativeVectorMethodFormation.types.map (CTm.subst IndexedContainerNativeVectorMethodFormation.images))
    PUnit.unit (.var 1) (.var 0) [] [] rfl originalExplicitSource original_source_pair

theorem explicit_source_compatible : CCtxRen originalExplicitSource explicitSource sourceRen := by
  unfold CCtxRen
  intro position
  refine Fin.cases ?_ ?_ position
  · rfl
  · intro position
    refine Fin.cases ?_ ?_ position
    · change explicitSource.lookup (Fin.succ (0 : Fin 12)) =
        CTm.rename sourceRen (originalExplicitSource.lookup (Fin.succ (0 : Fin 11)))
      simp only [explicitSource, originalExplicitSource, CCtx.lookup_snoc_zero, CCtx.lookup_snoc_succ,
        NativeVectorAll.Annotated.Formation.allType_rename, CTm.rename]
      rfl
    · intro position
      refine Fin.cases ?_ ?_ position
      · rfl
      · intro position
        refine Fin.cases ?_ ?_ position
        · rfl
        · intro position
          refine Fin.cases ?_ ?_ position
          · rfl
          · intro position
            refine Fin.cases ?_ ?_ position
            · rfl
            · intro position
              refine Fin.cases ?_ ?_ position
              · rfl
              · intro position
                refine Fin.cases ?_ ?_ position
                · rfl
                · intro position
                  refine Fin.cases ?_ ?_ position
                  · change explicitSource.lookup (0 : Fin 4).succ.succ.succ.succ.succ.succ.succ.succ.succ =
                      CTm.rename sourceRen (originalExplicitSource.lookup (0 : Fin 4).succ.succ.succ.succ.succ.succ.succ.succ)
                    simp only [explicitSource, originalExplicitSource, input, GuardedContext.snoc,
                      base, IndexedContainerNativeVectorMethodFormation.context,
                      CCtx.lookup_snoc_zero, CCtx.lookup_snoc_succ, CTm.rename_comp]
                    apply CTm.rename_ext
                    intro index
                    fin_cases index <;> rfl
                  · intro position
                    refine Fin.cases ?_ ?_ position
                    · rfl
                    · intro position
                      refine Fin.cases ?_ ?_ position
                      · rfl
                      · intro position
                        refine Fin.cases ?_ ?_ position
                        · rfl
                        · intro position
                          exact position.elim0

theorem source_compatible : CCtxRen guarded.source context.source sourceRen := by
  change CCtxRen guarded.source explicitSource sourceRen
  rw [original_source_explicit]
  exact explicit_source_compatible

theorem renaming_compatible {type : HOL.Ty Base} (index : HOL.Var target type) :
    (nativeRen index).toFin = sourceRen index.toFin := by
  cases index with
  | vz => rfl
  | vs index =>
    cases index with
    | vz => rfl
    | vs index =>
      cases index with
      | vz => rfl
      | vs index =>
        cases index with
        | vz => rfl
        | vs index =>
          cases index with
          | vz => rfl
          | vs index =>
            cases index with
            | vz => rfl
            | vs index =>
              cases index with
              | vz => rfl
              | vs index =>
                cases index with
                | vz => rfl
                | vs index =>
                  cases index with
                  | vz => rfl
                  | vs index =>
                    cases index with
                    | vz => rfl
                    | vs index =>
                      cases index with
                      | vz => rfl
                      | vs index =>
                        cases index with
                        | vz => rfl
                        | vs index =>
                          cases index

def embedding (roots : List (HOL.ClosedFormula Const)) :=
  GuardedSubstitution.ofRenaming roots guarded context sourceRen nativeRen
    (fun index => renaming_compatible index) source_compatible

theorem embedding_free (roots : List (HOL.ClosedFormula Const)) : (embedding roots).Free :=
  GuardedSubstitution.ofRenaming_free roots guarded context sourceRen nativeRen
    (fun index => renaming_compatible index) source_compatible

#print axioms source_formed
#print axioms embedding_free

end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorCaseContext
