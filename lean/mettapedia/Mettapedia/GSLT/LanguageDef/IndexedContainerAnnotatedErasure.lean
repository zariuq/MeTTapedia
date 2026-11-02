import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerAnnotatedSyntax
import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestTypes

/-!
# Exact erasure of annotated indexed-container generation

Primitive index and registered-operation correspondences suffice for the
whole generated constructor and dependent method. Every source field and
queued IH retains its original order, including complete registered bundles.
The annotated mathematical owner remains independent of this integration.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerAnnotatedErasure

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.IndexedPositiveContainer
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated

namespace Ann
export IndexedContainerAnnotated (TermEnvironment Indexing RegistrySyntax TypeSyntax)
end Ann

namespace Raw
export IndexedPositiveContainerGuestTypes (Indexing RegistrySyntax TypeSyntax)
end Raw

universe u
variable {I : Interface.{u}} {registry : Registry I} {Head : Type}

def eraseEnvironment {n : Nat} : {context : List I.SortCode} →
    Ann.TermEnvironment I Head n context → IndexedInductive.Guest.TermEnv I Head n context
  | [], _ => PUnit.unit
  | _ :: _, environment => (environment.1.erase, eraseEnvironment environment.2)

theorem eraseEnvironment_weaken {n : Nat} {context : List I.SortCode}
    (environment : Ann.TermEnvironment I Head n context) :
    eraseEnvironment (IndexedContainerAnnotated.weakenEnvironment environment) =
      IndexedInductive.Guest.Types.weakenEnvironment (eraseEnvironment environment) := by
  induction context with
  | nil => rfl
  | cons _ _ previous =>
      simp only [IndexedContainerAnnotated.weakenEnvironment, IndexedContainerAnnotated.mapEnvironment,
        eraseEnvironment, CTm.erase_rename, IndexedInductive.Guest.Types.weakenEnvironment,
        IndexedInductive.Guest.mapEnv]
      exact congrArg (Prod.mk _) (previous environment.2)

def eraseTypes {n : Nat} (types : Ann.TypeSyntax I Head n) : Raw.TypeSyntax I Head n where
  dataType sort := (types.dataType sort).erase
  family := types.family.erase
  constructor name := (types.constructor name).erase

theorem eraseTypes_dataType {n : Nat} (types : Ann.TypeSyntax I Head n) (sort : I.SortCode) :
    (eraseTypes types).dataType sort = (types.dataType sort).erase := rfl

theorem eraseTypes_weaken {n : Nat} (types : Ann.TypeSyntax I Head n) :
    eraseTypes types.weaken = (eraseTypes types).weaken := by
  cases types
  simp only [eraseTypes, IndexedContainerAnnotated.TypeSyntax.weaken, IndexedContainerAnnotated.TypeSyntax.map,
    IndexedPositiveContainerGuestTypes.TypeSyntax.weaken, IndexedPositiveContainerGuestTypes.TypeSyntax.map, CTm.erase_rename]

inductive IndexingCorrespondence : Ann.Indexing I Head → Raw.Indexing I Head → Prop where
  | indexed {first : IndexedContainerAnnotated.IndexSyntax I Head} {second : IndexedInductive.Guest.IndexSyntax I Head}
      (terms : ∀ {context n} (expression : I.IndexExpr context) (environment : Ann.TermEnvironment I Head n context),
        (first.term expression environment).erase = second.term expression (eraseEnvironment environment)) :
      IndexingCorrespondence (.indexed first) (.indexed second)
  | unindexed (first second : Subsingleton I.Index) : IndexingCorrespondence (.unindexed first) (.unindexed second)

theorem IndexingCorrespondence.familyAt {first : Ann.Indexing I Head} {second : Raw.Indexing I Head}
    (same : IndexingCorrespondence first second) {context : List I.SortCode} {n : Nat}
    (family : CTm Head n) (expression : I.IndexExpr context) (environment : Ann.TermEnvironment I Head n context) :
    (first.familyAt family expression environment).erase = second.familyAt family.erase expression (eraseEnvironment environment) := by
  cases same with
  | indexed terms => simp only [IndexedContainerAnnotated.Indexing.familyAt, IndexedPositiveContainerGuestTypes.Indexing.familyAt, CTm.erase, terms]
  | unindexed => rfl

structure RegistryCorrespondence (first : Ann.RegistrySyntax I registry Head) (second : Raw.RegistrySyntax I registry Head) : Prop where
  fieldType : ∀ {context n} name entry registered (output : entry.OutputExpr context)
    (environment : Ann.TermEnvironment I Head n context) (element : CTm Head n),
    (first.fieldType name entry registered output environment element).erase =
      second.fieldType name entry registered output (eraseEnvironment environment) element.erase
  bundleType : ∀ {context n} name entry registered (output : entry.OutputExpr context)
    (environment : Ann.TermEnvironment I Head n context) (element predicate field : CTm Head n),
    (first.bundleType name entry registered output environment element predicate field).erase =
      second.bundleType name entry registered output (eraseEnvironment environment) element.erase predicate.erase field.erase

theorem constructorType_erase {first : Ann.Indexing I Head} {second : Raw.Indexing I Head}
    (indices : IndexingCorrespondence first second)
    {firstRegistry : Ann.RegistrySyntax I registry Head} {secondRegistry : Raw.RegistrySyntax I registry Head}
    (containers : RegistryCorrespondence firstRegistry secondRegistry)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    {n : Nat} (types : Ann.TypeSyntax I Head n) (environment : Ann.TermEnvironment I Head n context) :
    (IndexedContainerAnnotated.constructorType first firstRegistry code types environment).erase =
      IndexedPositiveContainerGuestTypes.constructorType second secondRegistry code (eraseTypes types) (eraseEnvironment environment) := by
  induction code generalizing n with
  | result expression =>
      simpa only [IndexedContainerAnnotated.constructorType, IndexedPositiveContainerGuestTypes.constructorType, eraseTypes] using
        indices.familyAt types.family expression environment
  | data _ _ previous =>
      simp only [IndexedContainerAnnotated.constructorType, IndexedPositiveContainerGuestTypes.constructorType, CTm.erase, eraseTypes_dataType]
      congr 1
      simpa only [eraseTypes_weaken, eraseEnvironment, CTm.erase, eraseEnvironment_weaken] using
        previous types.weaken (.var 0, IndexedContainerAnnotated.weakenEnvironment environment)
  | recursive _ _ previous =>
      simp only [IndexedContainerAnnotated.constructorType, IndexedPositiveContainerGuestTypes.constructorType, CTm.erase, indices.familyAt]
      congr 1
      simpa only [eraseTypes_weaken, eraseEnvironment_weaken] using previous types.weaken (IndexedContainerAnnotated.weakenEnvironment environment)
  | nested _ _ _ _ _ _ previous =>
      simp only [IndexedContainerAnnotated.constructorType, IndexedPositiveContainerGuestTypes.constructorType,
        CTm.erase, containers.fieldType, indices.familyAt]
      congr 1
      simpa only [eraseTypes_weaken, eraseEnvironment_weaken] using previous types.weaken (IndexedContainerAnnotated.weakenEnvironment environment)

theorem hypotheses_erase {n : Nat} (pending : List (CTm Head n)) (result : CTm Head n) :
    (IndexedContainerAnnotated.hypotheses pending result).erase =
      IndexedPositiveContainerGuestTypes.hypotheses (pending.map CTm.erase) result.erase := by
  cases pending with
  | nil => simp only [IndexedContainerAnnotated.hypotheses, IndexedPositiveContainerGuestTypes.hypotheses,
      List.map_nil, FunctionArgumentAdapters.curriedType]
  | cons first rest =>
      simp only [IndexedContainerAnnotated.hypotheses, CTm.erase, IndexedPositiveContainerGuestTypes.hypotheses,
        List.map_cons, FunctionArgumentAdapters.curriedType_cons, FunctionArgumentAdapters.arrow]
      congr 1
      simpa only [IndexedPositiveContainerGuestTypes.hypotheses, FunctionArgumentAdapters.curriedType_rename,
        List.map_map, Function.comp_def, CTm.erase_rename] using
        hypotheses_erase (rest.map (CTm.rename wk)) (result.rename wk)
termination_by pending.length
decreasing_by simp

theorem methodBody_erase {first : Ann.Indexing I Head} {second : Raw.Indexing I Head}
    (indices : IndexingCorrespondence first second)
    {firstRegistry : Ann.RegistrySyntax I registry Head} {secondRegistry : Raw.RegistrySyntax I registry Head}
    (containers : RegistryCorrespondence firstRegistry secondRegistry)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    {n : Nat} (types : Ann.TypeSyntax I Head n) (environment : Ann.TermEnvironment I Head n context)
    (motive constructor : CTm Head n) (pending : List (CTm Head n)) :
    (IndexedContainerAnnotated.methodBody first firstRegistry code types environment motive constructor pending).erase =
      IndexedPositiveContainerGuestTypes.methodBody second secondRegistry code (eraseTypes types) (eraseEnvironment environment)
        motive.erase constructor.erase (pending.map CTm.erase) := by
  induction code generalizing n with
  | result _ => simp only [IndexedContainerAnnotated.methodBody, IndexedPositiveContainerGuestTypes.methodBody,
      hypotheses_erase, CTm.erase, indices.familyAt, IndexedPositiveContainerGuestTypes.Indexing.predicateAt]
  | data _ _ previous =>
      simp only [IndexedContainerAnnotated.methodBody, IndexedPositiveContainerGuestTypes.methodBody, CTm.erase, eraseTypes_dataType]
      congr 1
      simpa only [eraseTypes_weaken, eraseEnvironment, CTm.erase, eraseEnvironment_weaken, CTm.erase_rename,
        List.map_map, Function.comp_def] using
        previous types.weaken (.var 0, IndexedContainerAnnotated.weakenEnvironment environment)
          (motive.rename wk) (.app (constructor.rename wk) (.var 0)) (pending.map (CTm.rename wk))
  | recursive expression _ previous =>
      simp only [IndexedContainerAnnotated.methodBody, IndexedPositiveContainerGuestTypes.methodBody, CTm.erase, indices.familyAt]
      congr 1
      have step := previous types.weaken (IndexedContainerAnnotated.weakenEnvironment environment) (motive.rename wk)
        (.app (constructor.rename wk) (.var 0)) (pending.map (CTm.rename wk) ++
          [.app (first.familyAt (motive.rename wk) expression (IndexedContainerAnnotated.weakenEnvironment environment)) (.var 0)])
      rw [List.map_append, List.map_cons, List.map_nil] at step
      simpa only [eraseTypes_weaken, eraseEnvironment_weaken, CTm.erase, CTm.erase_rename, List.map_map,
        Function.comp_def, indices.familyAt, IndexedPositiveContainerGuestTypes.Indexing.predicateAt] using step
  | nested name entry registered output childIndex rest previous =>
      simp only [IndexedContainerAnnotated.methodBody, IndexedPositiveContainerGuestTypes.methodBody,
        CTm.erase, containers.fieldType, indices.familyAt]
      congr 1
      simpa only [eraseTypes_weaken, eraseEnvironment_weaken, CTm.erase, CTm.erase_rename, List.map_map,
        List.map_append, List.map_cons, List.map_nil, Function.comp_def, containers.bundleType, indices.familyAt,
        IndexedPositiveContainerGuestTypes.Indexing.predicateAt, eraseTypes,
        IndexedContainerAnnotated.TypeSyntax.weaken, IndexedContainerAnnotated.TypeSyntax.map,
        IndexedPositiveContainerGuestTypes.TypeSyntax.weaken, IndexedPositiveContainerGuestTypes.TypeSyntax.map] using
        previous types.weaken (IndexedContainerAnnotated.weakenEnvironment environment) (motive.rename wk)
          (.app (constructor.rename wk) (.var 0)) (pending.map (CTm.rename wk) ++
            [firstRegistry.bundleType name entry registered output (IndexedContainerAnnotated.weakenEnvironment environment)
              (first.familyAt (types.family.rename wk) childIndex (IndexedContainerAnnotated.weakenEnvironment environment))
              (first.familyAt (motive.rename wk) childIndex (IndexedContainerAnnotated.weakenEnvironment environment)) (.var 0)])

#print axioms constructorType_erase
#print axioms methodBody_erase

end Mettapedia.GSLT.LanguageDef.IndexedContainerAnnotatedErasure
