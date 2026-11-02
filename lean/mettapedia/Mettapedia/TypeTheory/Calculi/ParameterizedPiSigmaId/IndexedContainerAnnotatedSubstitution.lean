import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerAnnotatedSyntax

/-!
# Caller substitution through complete annotated methods

The original fields, dependent result and every queued induction hypothesis
move under the same scoped substitution. Registered bundle transport uses
the primitive registry law, rather than reconstructing a method after erasure.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerAnnotated

open Mettapedia.TypeTheory.IndexedPositiveContainer
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Presentation TypedEquality.Annotated

universe u
variable {I : Interface.{u}} {registry : Registry I} {Head : Type}

theorem hypotheses_substitute {n m : Nat} (pending : List (CTm Head n))
    (result : CTm Head n) (images : CSub Head n m) :
    (hypotheses pending result).subst images =
      hypotheses (pending.map (CTm.subst images)) (result.subst images) := by
  cases pending with
  | nil => simp only [hypotheses, List.map_nil]
  | cons first rest =>
      simp only [hypotheses, CTm.subst, List.map_cons]
      congr 1
      simpa only [List.map_map, Function.comp_def, CTm.subst_liftSub_wk] using
        hypotheses_substitute (rest.map (CTm.rename wk)) (result.rename wk) (CTm.liftSub images)
termination_by pending.length
decreasing_by simp_all

theorem methodBody_substitute (indexing : Indexing I Head)
    (containers : RegistrySyntax I registry Head) {parameters : Nat}
    {context : List I.SortCode} (code : Code I registry parameters context) {n m : Nat}
    (types : TypeSyntax I Head n) (environment : TermEnvironment I Head n context)
    (motive constructor : CTm Head n) (pending : List (CTm Head n)) (images : CSub Head n m) :
    (methodBody indexing containers code types environment motive constructor pending).subst images =
      methodBody indexing containers code (types.map (CTm.subst images))
        (mapEnvironment (CTm.subst images) environment) (motive.subst images)
        (constructor.subst images) (pending.map (CTm.subst images)) := by
  induction code generalizing n m with
  | result expression =>
      simp only [methodBody, hypotheses_substitute, CTm.subst, indexing.familyAt_substitute]
  | data sort rest previous =>
      simp only [methodBody, CTm.subst, TypeSyntax.map]
      congr 1
      simpa only [mapEnvironment, CTm.subst, CTm.liftSub, Fin.cases_zero, weakenEnvironment_substitute,
        TypeSyntax.weaken, TypeSyntax.map, CTm.subst_liftSub_wk, List.map_map, Function.comp_def] using
        previous types.weaken (.var 0, weakenEnvironment environment) (motive.rename wk)
          (.app (constructor.rename wk) (.var 0)) (pending.map (CTm.rename wk)) (CTm.liftSub images)
  | recursive expression rest previous =>
      simp only [methodBody, CTm.subst, indexing.familyAt_substitute, TypeSyntax.map]
      congr 1
      convert previous types.weaken (weakenEnvironment environment) (motive.rename wk)
        (.app (constructor.rename wk) (.var 0))
        (pending.map (CTm.rename wk) ++
          [.app (indexing.familyAt (motive.rename wk) expression (weakenEnvironment environment)) (.var 0)])
        (CTm.liftSub images) using 1
      simp only [CTm.subst, CTm.liftSub, Fin.cases_zero, weakenEnvironment_substitute,
        TypeSyntax.weaken, TypeSyntax.map, CTm.subst_liftSub_wk, List.map_map, Function.comp_def,
        List.map_append, List.map_cons, List.map_nil, indexing.familyAt_substitute]
  | nested name entry registered output childIndex rest previous =>
      simp only [methodBody, CTm.subst, containers.fieldType_substitute,
        indexing.familyAt_substitute, TypeSyntax.map]
      congr 1
      convert previous types.weaken (weakenEnvironment environment) (motive.rename wk)
        (.app (constructor.rename wk) (.var 0))
        (pending.map (CTm.rename wk) ++
          [containers.bundleType name entry registered output (weakenEnvironment environment)
            (indexing.familyAt (types.family.rename wk) childIndex (weakenEnvironment environment))
            (indexing.familyAt (motive.rename wk) childIndex (weakenEnvironment environment)) (.var 0)])
        (CTm.liftSub images) using 1
      simp only [CTm.subst, CTm.liftSub, Fin.cases_zero, weakenEnvironment_substitute,
        TypeSyntax.weaken, TypeSyntax.map, CTm.subst_liftSub_wk, List.map_map, Function.comp_def,
        List.map_append, List.map_cons, List.map_nil, containers.bundleType_substitute,
        indexing.familyAt_substitute]

#print axioms hypotheses_substitute
#print axioms methodBody_substitute

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerAnnotated
