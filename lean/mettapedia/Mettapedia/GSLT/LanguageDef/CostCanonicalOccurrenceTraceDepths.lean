import Mettapedia.GSLT.LanguageDef.CostCanonicalOccurrenceTraceRecursive

/-!
# Positional ancestry through two-depth keyed canonicalization

The hereditary Cost executor uses a key whose comparison can observe both the
quote-visible binder depth and the structural scope depth.  This module lifts
the exact occurrence trace to that two-depth traversal while reusing the
already proved finisher and parallel-phase position maps.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.Syntax

mutual
  /-- Reflect an exact selected occurrence through every phase of two-depth
  keyed canonicalization to one authored source occurrence. -/
  noncomputable def canonicalizeByDepthsOccurrenceSource
      {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl)
      (availableDepth scopeDepth : Nat) :
      (pattern : Pattern) →
        CostStaticFVarOccurrence
          (canonicalizeByDepths key declaration availableDepth scopeDepth
            pattern) →
        CostStaticFVarOccurrence pattern
    | .bvar index, occurrence => by
        have impossible := occurrence.name_mem_freeFvarNames
        simp [canonicalizeByDepths, Pattern.freeFvarNames] at impossible
    | .fvar name, occurrence => occurrence
    | .apply constructor arguments, occurrence => by
        let childAvailableDepth :=
          if constructor == declaration.quoteConstructor then 0
          else availableDepth
        let normalizedArguments :=
          canonicalizeListByDepths key declaration childAvailableDepth
            scopeDepth arguments
        let normalizedArgument := finishApplyOccurrenceSource declaration
          constructor normalizedArguments occurrence
        let sourceArgument := canonicalizeListByDepthsOccurrenceSource key
          declaration childAvailableDepth scopeDepth arguments
            normalizedArgument
        exact sourceArgument.inApply constructor
    | .lambda binder body, occurrence => by
        let normalizedBody :=
          canonicalizeByDepths key declaration (availableDepth + 1)
            (scopeDepth + 1) body
        let bodyOccurrence := lambdaOccurrenceBody binder normalizedBody
          occurrence
        let sourceBody := canonicalizeByDepthsOccurrenceSource key declaration
          (availableDepth + 1) (scopeDepth + 1) body bodyOccurrence
        exact sourceBody.inContext (.lambda binder .hole)
    | .multiLambda arity binders body, occurrence => by
        let normalizedBody :=
          canonicalizeByDepths key declaration (availableDepth + arity)
            (scopeDepth + arity) body
        let bodyOccurrence := multiLambdaOccurrenceBody arity binders
          normalizedBody occurrence
        let sourceBody := canonicalizeByDepthsOccurrenceSource key declaration
          (availableDepth + arity) (scopeDepth + arity) body bodyOccurrence
        exact sourceBody.inContext (.multiLambda arity binders .hole)
    | .subst body replacement, occurrence => by
        let normalizedBody :=
          canonicalizeByDepths key declaration (availableDepth + 1)
            (scopeDepth + 1) body
        let normalizedReplacement :=
          canonicalizeByDepths key declaration availableDepth scopeDepth
            replacement
        exact match substOccurrenceView normalizedBody normalizedReplacement
            occurrence with
        | .body inner contextEquality selected => by
            let nested : CostStaticFVarOccurrence normalizedBody :=
              { name := occurrence.name
                context := inner
                selected := selected }
            let sourceBody := canonicalizeByDepthsOccurrenceSource key
              declaration (availableDepth + 1) (scopeDepth + 1) body nested
            exact sourceBody.inContext (.substBody .hole replacement)
        | .replacement inner contextEquality selected => by
            let nested : CostStaticFVarOccurrence normalizedReplacement :=
              { name := occurrence.name
                context := inner
                selected := selected }
            let sourceReplacement := canonicalizeByDepthsOccurrenceSource key
              declaration availableDepth scopeDepth replacement nested
            exact sourceReplacement.inContext (.substReplacement body .hole)
    | .collection collectionType elements none, occurrence => by
        let normalizedElements := canonicalizeListByDepths key declaration
          availableDepth scopeDepth elements
        by_cases parallel : collectionType = declaration.parallelCollection
        · subst collectionType
          let phaseEquality :
              canonicalizeByDepths key declaration availableDepth scopeDepth
                  (.collection declaration.parallelCollection elements none) =
                collapseParallel declaration
                  (normalizeParallelElementsBy
                    (key availableDepth scopeDepth) declaration
                    normalizedElements) := by
            simp [canonicalizeByDepths, normalizedElements]
          let finalOccurrence : CostStaticFVarOccurrence
              (collapseParallel declaration
                (normalizeParallelElementsBy (key availableDepth scopeDepth)
                  declaration normalizedElements)) :=
            occurrence.castRoot phaseEquality
          let normalizedOccurrence := keyedParallelPhaseOccurrenceSource
            (key availableDepth scopeDepth) declaration normalizedElements
              finalOccurrence
          let sourceOccurrence := canonicalizeListByDepthsOccurrenceSource key
            declaration availableDepth scopeDepth elements normalizedOccurrence
          exact sourceOccurrence.inCollection declaration.parallelCollection
            none
        · let phaseEquality :
              canonicalizeByDepths key declaration availableDepth scopeDepth
                  (.collection collectionType elements none) =
                .collection collectionType normalizedElements none := by
            simp [canonicalizeByDepths, normalizedElements, parallel]
          let finalOccurrence := occurrence.castRoot phaseEquality
          let normalizedOccurrence := collectionOccurrenceMember collectionType
            normalizedElements none finalOccurrence
          let sourceOccurrence := canonicalizeListByDepthsOccurrenceSource key
            declaration availableDepth scopeDepth elements normalizedOccurrence
          exact sourceOccurrence.inCollection collectionType none
    | .collection collectionType elements (some rest), occurrence => by
        let normalizedElements := canonicalizeListByDepths key declaration
          availableDepth scopeDepth elements
        let phaseEquality :
            canonicalizeByDepths key declaration availableDepth scopeDepth
                (.collection collectionType elements (some rest)) =
              .collection collectionType normalizedElements (some rest) := by
          simp [canonicalizeByDepths, normalizedElements]
        let finalOccurrence := occurrence.castRoot phaseEquality
        let normalizedOccurrence := collectionOccurrenceMember collectionType
          normalizedElements (some rest) finalOccurrence
        let sourceOccurrence := canonicalizeListByDepthsOccurrenceSource key
          declaration availableDepth scopeDepth elements normalizedOccurrence
        exact sourceOccurrence.inCollection collectionType (some rest)
  termination_by pattern => 3 * sizeOf pattern + 2

  /-- Pointwise companion for an exact occurrence in a list canonicalized with
  the same two depths. -/
  noncomputable def canonicalizeListByDepthsOccurrenceSource
      {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl)
      (availableDepth scopeDepth : Nat) :
      (patterns : List Pattern) →
        CostStaticFVarListOccurrence
          (canonicalizeListByDepths key declaration availableDepth scopeDepth
            patterns) →
        CostStaticFVarListOccurrence patterns
    | [], occurrence => Fin.elim0 occurrence.position
    | head :: tail, occurrence => by
        rcases occurrence with ⟨position, nested⟩
        cases position using Fin.cases with
        | zero =>
            let sourceHead := canonicalizeByDepthsOccurrenceSource key
              declaration availableDepth scopeDepth head nested
            exact
              { position := ⟨0, by simp⟩
                occurrence := sourceHead }
        | succ tailPosition =>
            let tailOccurrence : CostStaticFVarListOccurrence
                (canonicalizeListByDepths key declaration availableDepth
                  scopeDepth tail) :=
              { position := tailPosition
                occurrence := nested }
            let sourceTail := canonicalizeListByDepthsOccurrenceSource key
              declaration availableDepth scopeDepth tail tailOccurrence
            exact
              { position := Fin.succ sourceTail.position
                occurrence := sourceTail.occurrence }
  termination_by patterns => 3 * sizeOf patterns + 1

  decreasing_by
    all_goals simp_all <;> omega

end

mutual
  /-- Two-depth recursive source reflection preserves the selected variable
  spelling while retaining the complete authored zipper. -/
  theorem canonicalizeByDepthsOccurrenceSource_name
      {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl)
      (availableDepth scopeDepth : Nat) (pattern : Pattern)
      (occurrence : CostStaticFVarOccurrence
        (canonicalizeByDepths key declaration availableDepth scopeDepth
          pattern)) :
      (canonicalizeByDepthsOccurrenceSource key declaration availableDepth
        scopeDepth pattern occurrence).name = occurrence.name := by
    cases pattern with
    | bvar index =>
        have impossible := occurrence.name_mem_freeFvarNames
        simp [canonicalizeByDepths, Pattern.freeFvarNames] at impossible
    | fvar name => rw [canonicalizeByDepthsOccurrenceSource]
    | apply constructor arguments =>
        rw [canonicalizeByDepthsOccurrenceSource]
        let childAvailableDepth :=
          if constructor == declaration.quoteConstructor then 0
          else availableDepth
        let normalizedArguments :=
          canonicalizeListByDepths key declaration childAvailableDepth
            scopeDepth arguments
        let normalizedArgument := finishApplyOccurrenceSource declaration
          constructor normalizedArguments occurrence
        let sourceArgument := canonicalizeListByDepthsOccurrenceSource key
          declaration childAvailableDepth scopeDepth arguments
            normalizedArgument
        change (sourceArgument.inApply constructor).name = occurrence.name
        exact (CostStaticFVarListOccurrence.inApply_name constructor
            sourceArgument).trans
          ((canonicalizeListByDepthsOccurrenceSource_name key declaration
            childAvailableDepth scopeDepth arguments normalizedArgument).trans
          (finishApplyOccurrenceSource_name declaration constructor
            normalizedArguments occurrence))
    | lambda binder body =>
        rw [canonicalizeByDepthsOccurrenceSource]
        let normalizedBody :=
          canonicalizeByDepths key declaration (availableDepth + 1)
            (scopeDepth + 1) body
        let bodyOccurrence := lambdaOccurrenceBody binder normalizedBody
          occurrence
        let sourceBody := canonicalizeByDepthsOccurrenceSource key declaration
          (availableDepth + 1) (scopeDepth + 1) body bodyOccurrence
        change (sourceBody.inContext (.lambda binder .hole)).name =
          occurrence.name
        exact (CostStaticFVarOccurrence.inContext_name sourceBody _).trans
          ((canonicalizeByDepthsOccurrenceSource_name key declaration
            (availableDepth + 1) (scopeDepth + 1) body bodyOccurrence).trans
          (lambdaOccurrenceBody_name binder normalizedBody occurrence))
    | multiLambda arity binders body =>
        rw [canonicalizeByDepthsOccurrenceSource]
        let normalizedBody :=
          canonicalizeByDepths key declaration (availableDepth + arity)
            (scopeDepth + arity) body
        let bodyOccurrence := multiLambdaOccurrenceBody arity binders
          normalizedBody occurrence
        let sourceBody := canonicalizeByDepthsOccurrenceSource key declaration
          (availableDepth + arity) (scopeDepth + arity) body bodyOccurrence
        change (sourceBody.inContext
          (.multiLambda arity binders .hole)).name = occurrence.name
        exact (CostStaticFVarOccurrence.inContext_name sourceBody _).trans
          ((canonicalizeByDepthsOccurrenceSource_name key declaration
            (availableDepth + arity) (scopeDepth + arity) body
              bodyOccurrence).trans
          (multiLambdaOccurrenceBody_name arity binders normalizedBody
            occurrence))
    | subst body replacement =>
        let normalizedBody :=
          canonicalizeByDepths key declaration (availableDepth + 1)
            (scopeDepth + 1) body
        let normalizedReplacement :=
          canonicalizeByDepths key declaration availableDepth scopeDepth
            replacement
        generalize viewEquality :
          substOccurrenceView normalizedBody normalizedReplacement occurrence =
            view
        cases view with
        | body inner contextEquality selected =>
            let nested : CostStaticFVarOccurrence normalizedBody :=
              { name := occurrence.name
                context := inner
                selected := selected }
            let sourceBody := canonicalizeByDepthsOccurrenceSource key
              declaration (availableDepth + 1) (scopeDepth + 1) body nested
            rw [canonicalizeByDepthsOccurrenceSource]
            rw [viewEquality]
            exact (CostStaticFVarOccurrence.inContext_name sourceBody _).trans
              (canonicalizeByDepthsOccurrenceSource_name key declaration
                (availableDepth + 1) (scopeDepth + 1) body nested)
        | replacement inner contextEquality selected =>
            let nested : CostStaticFVarOccurrence normalizedReplacement :=
              { name := occurrence.name
                context := inner
                selected := selected }
            let sourceReplacement := canonicalizeByDepthsOccurrenceSource key
              declaration availableDepth scopeDepth replacement nested
            rw [canonicalizeByDepthsOccurrenceSource]
            rw [viewEquality]
            exact (CostStaticFVarOccurrence.inContext_name sourceReplacement _
              ).trans
              (canonicalizeByDepthsOccurrenceSource_name key declaration
                availableDepth scopeDepth replacement nested)
    | collection collectionType elements rest =>
        let normalizedElements := canonicalizeListByDepths key declaration
          availableDepth scopeDepth elements
        cases rest with
        | none =>
            rw [canonicalizeByDepthsOccurrenceSource]
            by_cases parallel :
                collectionType = declaration.parallelCollection
            · subst collectionType
              rw [dif_pos rfl]
              let phaseEquality :
                  canonicalizeByDepths key declaration availableDepth
                      scopeDepth
                      (.collection declaration.parallelCollection elements
                        none) =
                    collapseParallel declaration
                      (normalizeParallelElementsBy
                        (key availableDepth scopeDepth) declaration
                        normalizedElements) := by
                simp [canonicalizeByDepths, normalizedElements]
              let finalOccurrence := occurrence.castRoot phaseEquality
              let normalizedOccurrence := keyedParallelPhaseOccurrenceSource
                (key availableDepth scopeDepth) declaration normalizedElements
                  finalOccurrence
              let sourceOccurrence := canonicalizeListByDepthsOccurrenceSource
                key declaration availableDepth scopeDepth elements
                  normalizedOccurrence
              change (sourceOccurrence.inCollection
                declaration.parallelCollection none).name = occurrence.name
              exact (CostStaticFVarListOccurrence.inCollection_name _ _
                  sourceOccurrence).trans
                ((canonicalizeListByDepthsOccurrenceSource_name key declaration
                  availableDepth scopeDepth elements normalizedOccurrence).trans
                ((keyedParallelPhaseOccurrenceSource_name
                  (key availableDepth scopeDepth) declaration
                    normalizedElements finalOccurrence).trans
                (CostStaticFVarOccurrence.castRoot_name phaseEquality
                  occurrence)))
            · rw [dif_neg parallel]
              let phaseEquality :
                  canonicalizeByDepths key declaration availableDepth
                      scopeDepth
                      (.collection collectionType elements none) =
                    .collection collectionType normalizedElements none := by
                simp [canonicalizeByDepths, normalizedElements, parallel]
              let finalOccurrence := occurrence.castRoot phaseEquality
              let normalizedOccurrence := collectionOccurrenceMember
                collectionType normalizedElements none finalOccurrence
              let sourceOccurrence := canonicalizeListByDepthsOccurrenceSource
                key declaration availableDepth scopeDepth elements
                  normalizedOccurrence
              change (sourceOccurrence.inCollection collectionType none).name =
                occurrence.name
              exact (CostStaticFVarListOccurrence.inCollection_name _ _
                  sourceOccurrence).trans
                ((canonicalizeListByDepthsOccurrenceSource_name key declaration
                  availableDepth scopeDepth elements normalizedOccurrence).trans
                ((collectionOccurrenceMember_name collectionType
                  normalizedElements none finalOccurrence).trans
                (CostStaticFVarOccurrence.castRoot_name phaseEquality
                  occurrence)))
        | some collectionRest =>
            rw [canonicalizeByDepthsOccurrenceSource]
            let phaseEquality :
                canonicalizeByDepths key declaration availableDepth scopeDepth
                    (.collection collectionType elements
                      (some collectionRest)) =
                  .collection collectionType normalizedElements
                    (some collectionRest) := by
              simp [canonicalizeByDepths, normalizedElements]
            let finalOccurrence := occurrence.castRoot phaseEquality
            let normalizedOccurrence := collectionOccurrenceMember
              collectionType normalizedElements (some collectionRest)
                finalOccurrence
            let sourceOccurrence := canonicalizeListByDepthsOccurrenceSource key
              declaration availableDepth scopeDepth elements
                normalizedOccurrence
            change (sourceOccurrence.inCollection collectionType
              (some collectionRest)).name = occurrence.name
            exact (CostStaticFVarListOccurrence.inCollection_name _ _
                sourceOccurrence).trans
              ((canonicalizeListByDepthsOccurrenceSource_name key declaration
                availableDepth scopeDepth elements normalizedOccurrence).trans
              ((collectionOccurrenceMember_name collectionType
                normalizedElements (some collectionRest) finalOccurrence).trans
              (CostStaticFVarOccurrence.castRoot_name phaseEquality occurrence)))
  termination_by 3 * sizeOf pattern + 2

  theorem canonicalizeListByDepthsOccurrenceSource_name
      {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl)
      (availableDepth scopeDepth : Nat) :
      ∀ (patterns : List Pattern)
        (occurrence : CostStaticFVarListOccurrence
          (canonicalizeListByDepths key declaration availableDepth scopeDepth
            patterns)),
        (canonicalizeListByDepthsOccurrenceSource key declaration
          availableDepth scopeDepth patterns occurrence).occurrence.name =
            occurrence.occurrence.name
    | [], occurrence => Fin.elim0 occurrence.position
    | head :: tail, occurrence => by
        rcases occurrence with ⟨position, nested⟩
        cases position using Fin.cases with
        | zero =>
            rw [canonicalizeListByDepthsOccurrenceSource]
            exact canonicalizeByDepthsOccurrenceSource_name key declaration
              availableDepth scopeDepth head nested
        | succ tailPosition =>
            rw [canonicalizeListByDepthsOccurrenceSource]
            let tailOccurrence : CostStaticFVarListOccurrence
                (canonicalizeListByDepths key declaration availableDepth
                  scopeDepth tail) :=
              { position := tailPosition
                occurrence := nested }
            exact canonicalizeListByDepthsOccurrenceSource_name key declaration
              availableDepth scopeDepth tail tailOccurrence
  termination_by patterns _ => 3 * sizeOf patterns + 1

  decreasing_by
    all_goals simp_all <;> omega

end


/-! ## Public two-depth certificate -/

/-- One exact final occurrence together with the authored zipper that created
it under scope-sensitive keyed canonicalization. -/
structure KeyedCanonicalDepthsFVarCertificate
    {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (availableDepth scopeDepth : Nat) (source : Pattern)
    (targetOccurrence : CostStaticFVarOccurrence
      (canonicalizeByDepths key declaration availableDepth scopeDepth source))
    where
  sourceOccurrence : CostStaticFVarOccurrence source
  name_eq : sourceOccurrence.name = targetOccurrence.name

/-- Construct the exact source certificate for any final two-depth canonical
free-variable occurrence. -/
noncomputable def keyedCanonicalDepthsFVarCertificate
    {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (availableDepth scopeDepth : Nat) (source : Pattern)
    (targetOccurrence : CostStaticFVarOccurrence
      (canonicalizeByDepths key declaration availableDepth scopeDepth source)) :
    KeyedCanonicalDepthsFVarCertificate key declaration availableDepth
      scopeDepth source targetOccurrence where
  sourceOccurrence := canonicalizeByDepthsOccurrenceSource key declaration
    availableDepth scopeDepth source targetOccurrence
  name_eq := canonicalizeByDepthsOccurrenceSource_name key declaration
    availableDepth scopeDepth source targetOccurrence

/-- Public existential reflection remains non-unique when equal source
occurrences or coalesced names are present. -/
theorem exists_sourceOccurrence_of_canonicalByDepths
    {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (availableDepth scopeDepth : Nat) (source : Pattern)
    (targetOccurrence : CostStaticFVarOccurrence
      (canonicalizeByDepths key declaration availableDepth scopeDepth source)) :
    ∃ sourceOccurrence : CostStaticFVarOccurrence source,
      sourceOccurrence.name = targetOccurrence.name :=
  ⟨(keyedCanonicalDepthsFVarCertificate key declaration availableDepth
      scopeDepth source targetOccurrence).sourceOccurrence,
    (keyedCanonicalDepthsFVarCertificate key declaration availableDepth
      scopeDepth source targetOccurrence).name_eq⟩

end Mettapedia.GSLT.LanguageDef
