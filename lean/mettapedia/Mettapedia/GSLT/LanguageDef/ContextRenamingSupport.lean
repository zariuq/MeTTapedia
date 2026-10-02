import Mettapedia.GSLT.LanguageDef.ContextRenamingTyping
import Mettapedia.GSLT.LanguageDef.ContextSupport

/-!
# Fixed-support ambient renaming

The common typed ambient action preserves reflective free-parameter support
at the same available target context. This theorem does not change boundary
values or assert that their dependency suffixes survive a new availability.
-/

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Reflection

mutual
  /-- A type-preserving ambient renaming keeps the same reflective support
  context. Free boundary parameters retain their existing dependency suffixes. -/
  theorem WellSorted.HasType.ReflectiveSupportSafeAt.renameAmbientBVarsAt
      {language : LanguageDef} {free : WellSorted.FreeTypeContext}
      {sourceBound targetBound inner : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr}
      {typed : WellSorted.HasType language free
        (inner ++ sourceBound)
        pattern type}
      {profile : ReflectionProfile}
      {support : ContextSupport.Support} {available : List TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt profile support available id)
      (rename : Nat → Nat) (preserves : WellSorted.PreservesBoundTypes sourceBound targetBound rename) :
      (typed.renameAmbientBVarsAt (inner := inner) rename preserves).ReflectiveSupportSafeAt
        profile support available id := by
    cases safe with
    | @bvar _ index _ lookup available _ =>
        by_cases inside : index < inner.length <;>
          simpa [WellSorted.HasType.renameAmbientBVarsAt,
          ContextSubstitution.renameAmbientBVarsAt, inside] using
          (WellSorted.HasType.ReflectiveSupportSafeAt.bvar
          (support := support)
          (binderImage := id)
          (preserves.lookup_prefix inner lookup) available)
    | fvar lookup available shape =>
        simpa [WellSorted.HasType.renameAmbientBVarsAt,
          ContextSubstitution.renameAmbientBVarsAt] using
          (WellSorted.HasType.ReflectiveSupportSafeAt.fvar
          (support := support)
          (binderImage := id)
          lookup available shape)
    | @constructorQuote _ _ _ membership notBare _ _ _ quoted argumentsSafe =>
        have thickenedArguments :=
          WellSorted.ArgumentsHaveTypes.ReflectiveSupportSafeAt.renameAmbientBVarsAt
            (inner := inner) argumentsSafe rename preserves
        simpa [WellSorted.HasType.renameAmbientBVarsAt,
          ContextSubstitution.renameAmbientBVarsAt] using
          (WellSorted.HasType.ReflectiveSupportSafeAt.constructorQuote
            (support := support) (membership := membership)
            (notBare := notBare) quoted thickenedArguments)
    | @constructorOrdinary _ _ _ membership notBare _ _ _ ordinary
        argumentsSafe =>
        have thickenedArguments :=
          WellSorted.ArgumentsHaveTypes.ReflectiveSupportSafeAt.renameAmbientBVarsAt
            (inner := inner) argumentsSafe rename preserves
        simpa [WellSorted.HasType.renameAmbientBVarsAt,
          ContextSubstitution.renameAmbientBVarsAt] using
          (WellSorted.HasType.ReflectiveSupportSafeAt.constructorOrdinary
            (support := support) (membership := membership)
            (notBare := notBare) ordinary thickenedArguments)
    | @lambda _ binder _ domain _ _ _ _ bodySafe =>
        have thickenedBody :=
          WellSorted.HasType.ReflectiveSupportSafeAt.renameAmbientBVarsAt
             (sourceBound := sourceBound)
            (targetBound := targetBound) (inner := domain :: inner)
            (support := support)
            (available := domain :: available)
            bodySafe rename preserves
        have constructed :=
          WellSorted.HasType.ReflectiveSupportSafeAt.lambda
            (support := support) (binder := binder) (binderImage := id)
            thickenedBody
        simpa [WellSorted.HasType.renameAmbientBVarsAt,
          ContextSubstitution.renameAmbientBVarsAt] using
          constructed
    | @multiLambda _ arity binders body domain codomain bodyTyped _ _
        bodySafe =>
        have contextEquality :
            List.replicate arity domain ++
                (inner ++ sourceBound) =
              (List.replicate arity domain ++ inner) ++
                sourceBound := by
          simp only [List.append_assoc]
        change bodyTyped.ReflectiveSupportSafeAt profile support
          (List.replicate arity domain ++ available) id at bodySafe
        have bodyTypedSafe :
            ∃ bodyTyped' : WellSorted.HasType language free
                ((List.replicate arity domain ++ inner) ++
                  sourceBound)
                body codomain,
              bodyTyped'.ReflectiveSupportSafeAt profile support
                (List.replicate arity domain ++ available) id := by
          rw [← contextEquality]
          exact ⟨bodyTyped, by simpa only using bodySafe⟩
        obtain ⟨bodyTyped', bodySafe'⟩ := bodyTypedSafe
        have thickenedBody :=
          WellSorted.HasType.ReflectiveSupportSafeAt.renameAmbientBVarsAt
             (sourceBound := sourceBound)
            (targetBound := targetBound)
            (inner := List.replicate arity domain ++ inner)
            (support := support)
            (available := List.replicate arity domain ++ available)
            bodySafe' rename preserves
        have thickenedBodyTyped : WellSorted.HasType language free
            (List.replicate arity domain ++ (inner ++ targetBound))
            (ContextSubstitution.renameAmbientBVarsAt rename (inner.length + arity) body)
            codomain := by
          simpa [List.append_assoc, List.length_append,
            List.length_replicate, Nat.add_comm] using
              bodyTyped'.renameAmbientBVarsAt
                (inner := List.replicate arity domain ++ inner) rename preserves
        have thickenedBodySafe :
            thickenedBodyTyped.ReflectiveSupportSafeAt profile support
              (List.replicate arity domain ++ available) id := by
          simpa [List.append_assoc, List.length_append,
            List.length_replicate, Nat.add_comm] using thickenedBody
        have constructed :=
          WellSorted.HasType.ReflectiveSupportSafeAt.multiLambda
            (support := support) (arity := arity) (binders := binders)
            (domain := domain) (bodyTyped := thickenedBodyTyped)
            (binderImage := id)
            thickenedBodySafe
        simpa [WellSorted.HasType.renameAmbientBVarsAt,
          ContextSubstitution.renameAmbientBVarsAt,
          List.append_assoc, List.length_append, List.length_replicate,
          Nat.add_comm] using constructed
    | @subst _ _ _ domain _ _ _ _ _ bodySafe replacementSafe =>
        have thickenedBody :=
          WellSorted.HasType.ReflectiveSupportSafeAt.renameAmbientBVarsAt
             (sourceBound := sourceBound)
            (targetBound := targetBound) (inner := domain :: inner)
            (support := support)
            (available := domain :: available)
            bodySafe rename preserves
        have thickenedReplacement :=
          WellSorted.HasType.ReflectiveSupportSafeAt.renameAmbientBVarsAt
             (sourceBound := sourceBound)
            (targetBound := targetBound) (inner := inner)
            (support := support) (available := available)
            replacementSafe rename preserves
        have constructed :=
          WellSorted.HasType.ReflectiveSupportSafeAt.subst (support := support)
            thickenedBody thickenedReplacement
        simpa [WellSorted.HasType.renameAmbientBVarsAt,
          ContextSubstitution.renameAmbientBVarsAt] using
          constructed
    | @collection _ _ _ _ _ elementsTyped _ _ elementsSafe =>
        have thickenedElements :=
          WellSorted.ElementsHaveType.ReflectiveSupportSafeAt.renameAmbientBVarsAt
            (inner := inner) elementsSafe rename preserves
        simpa [WellSorted.HasType.renameAmbientBVarsAt,
          ContextSubstitution.renameAmbientBVarsAt] using
          (WellSorted.HasType.ReflectiveSupportSafeAt.collection
            (support := support) thickenedElements)
    | @collectionConstructor _ _ parameterName _ _ _ _ membership parameterShape
        elementsTyped _ _ elementsSafe =>
        have thickenedElements :=
          WellSorted.ElementsHaveType.ReflectiveSupportSafeAt.renameAmbientBVarsAt
            (inner := inner) elementsSafe rename preserves
        simpa [WellSorted.HasType.renameAmbientBVarsAt,
          ContextSubstitution.renameAmbientBVarsAt] using
          (WellSorted.HasType.ReflectiveSupportSafeAt.collectionConstructor
            (support := support) (parameterName := parameterName)
            (membership := membership) (parameterShape := parameterShape)
            thickenedElements)

  /-- Argument-spine companion to reflective-support-preserving ambient
  binder insertion. -/
  theorem WellSorted.ArgumentsHaveTypes.ReflectiveSupportSafeAt.renameAmbientBVarsAt
      {language : LanguageDef} {free : WellSorted.FreeTypeContext}
      {sourceBound targetBound inner : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      {typed : WellSorted.ArgumentsHaveTypes language free
        (inner ++ sourceBound)
        arguments parameters}
      {profile : ReflectionProfile}
      {support : ContextSupport.Support} {available : List TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt profile support available id)
      (rename : Nat → Nat) (preserves : WellSorted.PreservesBoundTypes sourceBound targetBound rename) :
      (typed.renameAmbientBVarsAt (inner := inner) rename preserves).ReflectiveSupportSafeAt
        profile support available id := by
    cases safe with
    | nil bound available =>
        simpa [WellSorted.ArgumentsHaveTypes.renameAmbientBVarsAt] using
          (WellSorted.ArgumentsHaveTypes.ReflectiveSupportSafeAt.nil
            (support := support)
            (binderImage := id)
            (inner ++ targetBound) available)
    | @cons _ _ _ _ _ _ representation parameterType argumentTyped
        argumentsTyped _ _ argumentSafe argumentsSafe =>
        have thickenedArgument :=
          WellSorted.HasType.ReflectiveSupportSafeAt.renameAmbientBVarsAt
             (inner := inner)
            argumentSafe rename preserves
        have thickenedArguments :=
          WellSorted.ArgumentsHaveTypes.ReflectiveSupportSafeAt.renameAmbientBVarsAt
            (inner := inner) argumentsSafe rename preserves
        have transformedRepresentation :=
          WellSorted.MatchesParameterRepresentation.renameAmbientBVarsAt rename inner.length representation
        simpa [WellSorted.ArgumentsHaveTypes.renameAmbientBVarsAt] using
          (WellSorted.ArgumentsHaveTypes.ReflectiveSupportSafeAt.cons
            (support := support) (representation := transformedRepresentation)
            (parameterType := parameterType)
            (argumentTyped := argumentTyped.renameAmbientBVarsAt
              (inner := inner) rename preserves)
            (argumentsTyped := argumentsTyped.renameAmbientBVarsAt
              (inner := inner) rename preserves)
            thickenedArgument thickenedArguments)

  /-- Collection-spine companion to reflective-support-preserving ambient
  binder insertion. -/
  theorem WellSorted.ElementsHaveType.ReflectiveSupportSafeAt.renameAmbientBVarsAt
      {language : LanguageDef} {free : WellSorted.FreeTypeContext}
      {sourceBound targetBound inner : List TypeExpr}
      {elements : List Pattern} {elementType : TypeExpr}
      {typed : WellSorted.ElementsHaveType language free
        (inner ++ sourceBound)
        elements elementType}
      {profile : ReflectionProfile}
      {support : ContextSupport.Support} {available : List TypeExpr}
      (safe : typed.ReflectiveSupportSafeAt profile support available id)
      (rename : Nat → Nat) (preserves : WellSorted.PreservesBoundTypes sourceBound targetBound rename) :
      (typed.renameAmbientBVarsAt (inner := inner) rename preserves).ReflectiveSupportSafeAt
        profile support available id := by
    cases safe with
    | nil bound elementType available =>
        simpa [WellSorted.ElementsHaveType.renameAmbientBVarsAt] using
          (WellSorted.ElementsHaveType.ReflectiveSupportSafeAt.nil
            (support := support)
            (binderImage := id)
            (inner ++ targetBound) elementType available)
    | @cons _ _ _ _ elementTyped elementsTyped _ _ elementSafe
        elementsSafe =>
        have thickenedElement :=
          WellSorted.HasType.ReflectiveSupportSafeAt.renameAmbientBVarsAt
             (inner := inner)
            elementSafe rename preserves
        have thickenedElements :=
          WellSorted.ElementsHaveType.ReflectiveSupportSafeAt.renameAmbientBVarsAt
            (inner := inner) elementsSafe rename preserves
        simpa [WellSorted.ElementsHaveType.renameAmbientBVarsAt] using
          (WellSorted.ElementsHaveType.ReflectiveSupportSafeAt.cons
            (support := support)
            (elementTyped := elementTyped.renameAmbientBVarsAt
              (inner := inner) rename preserves)
            (elementsTyped := elementsTyped.renameAmbientBVarsAt
              (inner := inner) rename preserves)
            thickenedElement.castTyping thickenedElements.castTyping)
end

end Mettapedia.GSLT.LanguageDef
