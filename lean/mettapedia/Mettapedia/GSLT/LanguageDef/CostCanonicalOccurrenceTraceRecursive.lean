import Mettapedia.GSLT.LanguageDef.CostCanonicalOccurrenceTrace

/-!
# Recursive positional ancestry through keyed canonicalization

The outer parallel phases retain exact list positions through collapse,
sorting, filtering, and flattening.  This module supplies the constructor
views needed to recurse from those canonical child occurrences back to the
authored source pattern.

`Selects` is proof-irrelevant and lives in `Prop`.  Each view is therefore
obtained by classical choice from a proved `Nonempty` statement; all chosen
zipper data is then retained in `Type` by the resulting occurrence carrier.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Constructor occurrence views -/

structure CostApplyOccurrenceView (constructor : String)
    (arguments : List Pattern)
    (occurrence : CostStaticFVarOccurrence (.apply constructor arguments)) where
  before : List Pattern
  argument : Pattern
  after : List Pattern
  inner : OneHoleContext
  arguments_eq : arguments = before ++ argument :: after
  context_eq : occurrence.context = .apply constructor before inner after
  selected : Selects (.fvar occurrence.name) inner argument

theorem CostApplyOccurrenceView.nonempty (constructor : String)
    (arguments : List Pattern)
    (occurrence : CostStaticFVarOccurrence (.apply constructor arguments)) :
    Nonempty (CostApplyOccurrenceView constructor arguments occurrence) := by
  rcases occurrence with ⟨name, context, selected⟩
  cases selected with
  | apply innerSelected =>
      exact ⟨
        { before := _
          argument := _
          after := _
          inner := _
          arguments_eq := rfl
          context_eq := rfl
          selected := innerSelected }⟩

noncomputable def applyOccurrenceArgument (constructor : String)
    (arguments : List Pattern)
    (occurrence : CostStaticFVarOccurrence (.apply constructor arguments)) :
    CostStaticFVarListOccurrence arguments :=
  let view := Classical.choice
    (CostApplyOccurrenceView.nonempty constructor arguments occurrence)
  let inBounds : view.before.length < arguments.length := by
    have lengthEquality := congrArg List.length view.arguments_eq
    simp only [List.length_append, List.length_cons] at lengthEquality
    omega
  let position : Fin arguments.length := ⟨view.before.length, inBounds⟩
  have argumentEquality : arguments.get position = view.argument := by
    exact List.getElem_of_append view.arguments_eq rfl
  { position := position
    occurrence :=
      { name := occurrence.name
        context := view.inner
        selected := argumentEquality.symm ▸ view.selected } }

@[simp]
theorem applyOccurrenceArgument_name (constructor : String)
    (arguments : List Pattern)
    (occurrence : CostStaticFVarOccurrence (.apply constructor arguments)) :
    (applyOccurrenceArgument constructor arguments occurrence
      ).occurrence.name = occurrence.name :=
  rfl

structure CostLambdaOccurrenceView (binder : Option String) (body : Pattern)
    (occurrence : CostStaticFVarOccurrence (.lambda binder body)) where
  inner : OneHoleContext
  context_eq : occurrence.context = .lambda binder inner
  selected : Selects (.fvar occurrence.name) inner body

theorem CostLambdaOccurrenceView.nonempty (binder : Option String)
    (body : Pattern)
    (occurrence : CostStaticFVarOccurrence (.lambda binder body)) :
    Nonempty (CostLambdaOccurrenceView binder body occurrence) := by
  rcases occurrence with ⟨name, context, selected⟩
  cases selected with
  | lambda innerSelected =>
      exact ⟨
        { inner := _
          context_eq := rfl
          selected := innerSelected }⟩

noncomputable def lambdaOccurrenceBody (binder : Option String) (body : Pattern)
    (occurrence : CostStaticFVarOccurrence (.lambda binder body)) :
    CostStaticFVarOccurrence body :=
  let view := Classical.choice
    (CostLambdaOccurrenceView.nonempty binder body occurrence)
  { name := occurrence.name
    context := view.inner
    selected := view.selected }

@[simp]
theorem lambdaOccurrenceBody_name (binder : Option String) (body : Pattern)
    (occurrence : CostStaticFVarOccurrence (.lambda binder body)) :
    (lambdaOccurrenceBody binder body occurrence).name = occurrence.name :=
  rfl

structure CostMultiLambdaOccurrenceView (arity : Nat) (binders : List String)
    (body : Pattern)
    (occurrence : CostStaticFVarOccurrence
      (.multiLambda arity binders body)) where
  inner : OneHoleContext
  context_eq : occurrence.context = .multiLambda arity binders inner
  selected : Selects (.fvar occurrence.name) inner body

theorem CostMultiLambdaOccurrenceView.nonempty (arity : Nat)
    (binders : List String) (body : Pattern)
    (occurrence : CostStaticFVarOccurrence
      (.multiLambda arity binders body)) :
    Nonempty (CostMultiLambdaOccurrenceView arity binders body occurrence) := by
  rcases occurrence with ⟨name, context, selected⟩
  cases selected with
  | multiLambda innerSelected =>
      exact ⟨
        { inner := _
          context_eq := rfl
          selected := innerSelected }⟩

noncomputable def multiLambdaOccurrenceBody (arity : Nat)
    (binders : List String) (body : Pattern)
    (occurrence : CostStaticFVarOccurrence
      (.multiLambda arity binders body)) :
    CostStaticFVarOccurrence body :=
  let view := Classical.choice
    (CostMultiLambdaOccurrenceView.nonempty arity binders body occurrence)
  { name := occurrence.name
    context := view.inner
    selected := view.selected }

@[simp]
theorem multiLambdaOccurrenceBody_name (arity : Nat)
    (binders : List String) (body : Pattern)
    (occurrence : CostStaticFVarOccurrence
      (.multiLambda arity binders body)) :
    (multiLambdaOccurrenceBody arity binders body occurrence).name =
      occurrence.name :=
  rfl

inductive CostSubstOccurrenceView (body replacement : Pattern)
    (occurrence : CostStaticFVarOccurrence (.subst body replacement)) : Type where
  | body (inner : OneHoleContext)
      (context_eq : occurrence.context = .substBody inner replacement)
      (selected : Selects (.fvar occurrence.name) inner body) :
      CostSubstOccurrenceView body replacement occurrence
  | replacement (inner : OneHoleContext)
      (context_eq : occurrence.context = .substReplacement body inner)
      (selected : Selects (.fvar occurrence.name) inner replacement) :
      CostSubstOccurrenceView body replacement occurrence

theorem CostSubstOccurrenceView.nonempty (body replacement : Pattern)
    (occurrence : CostStaticFVarOccurrence (.subst body replacement)) :
    Nonempty (CostSubstOccurrenceView body replacement occurrence) := by
  rcases occurrence with ⟨name, context, selected⟩
  cases selected with
  | substBody innerSelected =>
      exact ⟨.body _ rfl innerSelected⟩
  | substReplacement innerSelected =>
      exact ⟨.replacement _ rfl innerSelected⟩

noncomputable def substOccurrenceView (body replacement : Pattern)
    (occurrence : CostStaticFVarOccurrence (.subst body replacement)) :
    CostSubstOccurrenceView body replacement occurrence :=
  Classical.choice
    (CostSubstOccurrenceView.nonempty body replacement occurrence)

/-! ## Application finisher -/

inductive FinishApplyShape (declaration : ReflectivePresentationDecl)
    (constructor : String) (arguments : List Pattern) : Type where
  | retained
      (result_eq : finishNormalizeReflectiveApply declaration constructor
        arguments = .apply constructor arguments) :
      FinishApplyShape declaration constructor arguments
  | exposed (name : Pattern)
      (constructor_eq : constructor = declaration.quoteConstructor)
      (arguments_eq : arguments =
        [.apply declaration.dropConstructor [name]])
      (result_eq : finishNormalizeReflectiveApply declaration constructor
        arguments = name) :
      FinishApplyShape declaration constructor arguments

theorem FinishApplyShape.nonempty (declaration : ReflectivePresentationDecl)
    (constructor : String) (arguments : List Pattern) :
    Nonempty (FinishApplyShape declaration constructor arguments) := by
  by_cases quoted : constructor = declaration.quoteConstructor
  · subst constructor
    cases arguments with
    | nil =>
        exact ⟨.retained (by simp [finishNormalizeReflectiveApply])⟩
    | cons first rest =>
        cases rest with
        | cons second tail =>
            exact ⟨.retained (by simp [finishNormalizeReflectiveApply])⟩
        | nil =>
            cases first with
            | apply drop dropArguments =>
                cases dropArguments with
                | nil =>
                    exact ⟨.retained (by
                      simp [finishNormalizeReflectiveApply])⟩
                | cons name nameRest =>
                    cases nameRest with
                    | cons second tail =>
                        exact ⟨.retained (by
                          simp [finishNormalizeReflectiveApply])⟩
                    | nil =>
                        by_cases dropped :
                            drop = declaration.dropConstructor
                        · subst drop
                          exact ⟨.exposed name rfl rfl (by
                            simp [finishNormalizeReflectiveApply])⟩
                        · exact ⟨.retained (by
                            simp [finishNormalizeReflectiveApply, dropped])⟩
            | bvar index =>
                exact ⟨.retained (by simp [finishNormalizeReflectiveApply])⟩
            | fvar name =>
                exact ⟨.retained (by simp [finishNormalizeReflectiveApply])⟩
            | lambda binder body =>
                exact ⟨.retained (by simp [finishNormalizeReflectiveApply])⟩
            | multiLambda arity binders body =>
                exact ⟨.retained (by simp [finishNormalizeReflectiveApply])⟩
            | subst body replacement =>
                exact ⟨.retained (by simp [finishNormalizeReflectiveApply])⟩
            | collection collectionType elements collectionRest =>
                exact ⟨.retained (by simp [finishNormalizeReflectiveApply])⟩
  · exact ⟨.retained (by
      simp [finishNormalizeReflectiveApply, quoted])⟩

noncomputable def finishApplyShape (declaration : ReflectivePresentationDecl)
    (constructor : String) (arguments : List Pattern) :
    FinishApplyShape declaration constructor arguments :=
  Classical.choice (FinishApplyShape.nonempty declaration constructor arguments)

/-- Reflect a selected occurrence through the Quote/Drop finisher into the
exact normalized argument position. -/
noncomputable def finishApplyOccurrenceSource
    (declaration : ReflectivePresentationDecl) (constructor : String)
    (arguments : List Pattern)
    (occurrence : CostStaticFVarOccurrence
      (finishNormalizeReflectiveApply declaration constructor arguments)) :
    CostStaticFVarListOccurrence arguments :=
  match finishApplyShape declaration constructor arguments with
  | .retained resultEquality =>
      applyOccurrenceArgument constructor arguments
        (occurrence.castRoot resultEquality)
  | .exposed name constructorEquality argumentsEquality resultEquality =>
      let exposed := occurrence.castRoot resultEquality
      let nested := exposed.inContext
        (.apply declaration.dropConstructor [] .hole [])
      let singleton : CostStaticFVarListOccurrence
          [.apply declaration.dropConstructor [name]] :=
        { position := ⟨0, by simp⟩
          occurrence := nested }
      singleton.castPatterns argumentsEquality.symm

@[simp]
theorem finishApplyOccurrenceSource_name
    (declaration : ReflectivePresentationDecl) (constructor : String)
    (arguments : List Pattern)
    (occurrence : CostStaticFVarOccurrence
      (finishNormalizeReflectiveApply declaration constructor arguments)) :
    (finishApplyOccurrenceSource declaration constructor arguments occurrence
      ).occurrence.name = occurrence.name := by
  unfold finishApplyOccurrenceSource
  cases finishApplyShape declaration constructor arguments with
  | retained resultEquality => simp
  | exposed name constructorEquality argumentsEquality resultEquality => simp

/-! ## Recursive source reflection -/

private theorem take_get_drop (patterns : List Pattern)
    (position : Fin patterns.length) :
    patterns.take position ++ patterns.get position ::
        patterns.drop (position + 1) = patterns := by
  rw [List.cons_get_drop_succ]
  exact List.take_append_drop position patterns

namespace CostStaticFVarListOccurrence

/-- Place an exact list occurrence back into an authored application. -/
def inApply (constructor : String) {patterns : List Pattern}
    (occurrence : CostStaticFVarListOccurrence patterns) :
    CostStaticFVarOccurrence (.apply constructor patterns) where
  name := occurrence.occurrence.name
  context := .apply constructor (patterns.take occurrence.position)
    occurrence.occurrence.context
    (patterns.drop (occurrence.position + 1))
  selected := by
    have selected : Selects (.fvar occurrence.occurrence.name)
        (.apply constructor (patterns.take occurrence.position)
          occurrence.occurrence.context
          (patterns.drop (occurrence.position + 1)))
        (.apply constructor
          (patterns.take occurrence.position ++
            patterns.get occurrence.position ::
              patterns.drop (occurrence.position + 1))) :=
      Selects.apply occurrence.occurrence.selected
    rw [take_get_drop] at selected
    exact selected

@[simp]
theorem inApply_name (constructor : String) {patterns : List Pattern}
    (occurrence : CostStaticFVarListOccurrence patterns) :
    (occurrence.inApply constructor).name = occurrence.occurrence.name :=
  rfl

end CostStaticFVarListOccurrence

mutual
  /-- Reflect an exact selected occurrence through every phase of keyed
  canonicalization back to one authored source occurrence. -/
  noncomputable def canonicalizeByAtOccurrenceSource
      {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl) (availableDepth : Nat) :
      (pattern : Pattern) →
        CostStaticFVarOccurrence
          (canonicalizeByAt key declaration availableDepth pattern) →
        CostStaticFVarOccurrence pattern
    | .bvar index, occurrence => by
        have impossible := occurrence.name_mem_freeFvarNames
        simp [canonicalizeByAt, Pattern.freeFvarNames] at impossible
    | .fvar name, occurrence => occurrence
    | .apply constructor arguments, occurrence => by
        let childDepth :=
          if constructor == declaration.quoteConstructor then 0
          else availableDepth
        let normalizedArguments :=
          canonicalizeListByAt key declaration childDepth arguments
        let normalizedArgument := finishApplyOccurrenceSource declaration
          constructor normalizedArguments occurrence
        let sourceArgument := canonicalizeListByAtOccurrenceSource key
          declaration childDepth arguments normalizedArgument
        exact sourceArgument.inApply constructor
    | .lambda binder body, occurrence => by
        let normalizedBody :=
          canonicalizeByAt key declaration (availableDepth + 1) body
        let bodyOccurrence := lambdaOccurrenceBody binder normalizedBody occurrence
        let sourceBody := canonicalizeByAtOccurrenceSource key declaration
          (availableDepth + 1) body bodyOccurrence
        exact sourceBody.inContext (.lambda binder .hole)
    | .multiLambda arity binders body, occurrence => by
        let normalizedBody :=
          canonicalizeByAt key declaration (availableDepth + arity) body
        let bodyOccurrence := multiLambdaOccurrenceBody arity binders
          normalizedBody occurrence
        let sourceBody := canonicalizeByAtOccurrenceSource key declaration
          (availableDepth + arity) body bodyOccurrence
        exact sourceBody.inContext (.multiLambda arity binders .hole)
    | .subst body replacement, occurrence => by
        let normalizedBody :=
          canonicalizeByAt key declaration (availableDepth + 1) body
        let normalizedReplacement :=
          canonicalizeByAt key declaration availableDepth replacement
        exact match substOccurrenceView normalizedBody normalizedReplacement
            occurrence with
        | .body inner contextEquality selected => by
            let nested : CostStaticFVarOccurrence normalizedBody :=
              { name := occurrence.name
                context := inner
                selected := selected }
            let sourceBody := canonicalizeByAtOccurrenceSource key declaration
              (availableDepth + 1) body nested
            exact sourceBody.inContext (.substBody .hole replacement)
        | .replacement inner contextEquality selected => by
            let nested : CostStaticFVarOccurrence normalizedReplacement :=
              { name := occurrence.name
                context := inner
                selected := selected }
            let sourceReplacement := canonicalizeByAtOccurrenceSource key
              declaration availableDepth replacement nested
            exact sourceReplacement.inContext (.substReplacement body .hole)
    | .collection collectionType elements none, occurrence => by
        let normalizedElements :=
          canonicalizeListByAt key declaration availableDepth elements
        by_cases parallel : collectionType = declaration.parallelCollection
        · subst collectionType
          let phaseEquality :
              canonicalizeByAt key declaration availableDepth
                  (.collection declaration.parallelCollection elements none) =
                collapseParallel declaration
                  (normalizeParallelElementsBy (key availableDepth) declaration
                    normalizedElements) := by
            simp [canonicalizeByAt, normalizedElements]
          let finalOccurrence : CostStaticFVarOccurrence
              (collapseParallel declaration
                (normalizeParallelElementsBy (key availableDepth) declaration
                  normalizedElements)) :=
            occurrence.castRoot phaseEquality
          let normalizedOccurrence := keyedParallelPhaseOccurrenceSource
            (key availableDepth) declaration normalizedElements finalOccurrence
          let sourceOccurrence := canonicalizeListByAtOccurrenceSource key
            declaration availableDepth elements normalizedOccurrence
          exact sourceOccurrence.inCollection
            declaration.parallelCollection none
        · let phaseEquality :
              canonicalizeByAt key declaration availableDepth
                  (.collection collectionType elements none) =
                .collection collectionType normalizedElements none := by
            simp [canonicalizeByAt, normalizedElements, parallel]
          let finalOccurrence := occurrence.castRoot phaseEquality
          let normalizedOccurrence := collectionOccurrenceMember collectionType
            normalizedElements none finalOccurrence
          let sourceOccurrence := canonicalizeListByAtOccurrenceSource key
            declaration availableDepth elements normalizedOccurrence
          exact sourceOccurrence.inCollection collectionType none
    | .collection collectionType elements (some rest), occurrence => by
        let normalizedElements :=
          canonicalizeListByAt key declaration availableDepth elements
        let phaseEquality :
            canonicalizeByAt key declaration availableDepth
                (.collection collectionType elements (some rest)) =
              .collection collectionType normalizedElements (some rest) := by
          simp [canonicalizeByAt, normalizedElements]
        let finalOccurrence := occurrence.castRoot phaseEquality
        let normalizedOccurrence := collectionOccurrenceMember collectionType
          normalizedElements (some rest) finalOccurrence
        let sourceOccurrence := canonicalizeListByAtOccurrenceSource key
          declaration availableDepth elements normalizedOccurrence
        exact sourceOccurrence.inCollection collectionType (some rest)
  termination_by pattern => 3 * sizeOf pattern + 2

  /-- Pointwise recursive companion for an exact occurrence in a canonicalized
  pattern list. -/
  noncomputable def canonicalizeListByAtOccurrenceSource
      {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl) (availableDepth : Nat) :
      (patterns : List Pattern) →
        CostStaticFVarListOccurrence
          (canonicalizeListByAt key declaration availableDepth patterns) →
        CostStaticFVarListOccurrence patterns
    | [], occurrence => Fin.elim0 occurrence.position
    | head :: tail, occurrence => by
        rcases occurrence with ⟨position, nested⟩
        cases position using Fin.cases with
        | zero =>
            let sourceHead := canonicalizeByAtOccurrenceSource key declaration
              availableDepth head nested
            exact
              { position := ⟨0, by simp⟩
                occurrence := sourceHead }
        | succ tailPosition =>
            let tailOccurrence : CostStaticFVarListOccurrence
                (canonicalizeListByAt key declaration availableDepth tail) :=
              { position := tailPosition
                occurrence := nested }
            let sourceTail := canonicalizeListByAtOccurrenceSource key
              declaration availableDepth tail tailOccurrence
            exact
              { position := Fin.succ sourceTail.position
                occurrence := sourceTail.occurrence }
  termination_by patterns => 3 * sizeOf patterns + 1

  decreasing_by
    all_goals simp_all <;> omega

end

mutual
  /-- Recursive canonical source reflection preserves the selected variable
  spelling while retaining the complete source zipper. -/
  theorem canonicalizeByAtOccurrenceSource_name
      {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl) (availableDepth : Nat)
      (pattern : Pattern)
      (occurrence : CostStaticFVarOccurrence
        (canonicalizeByAt key declaration availableDepth pattern)) :
      (canonicalizeByAtOccurrenceSource key declaration availableDepth pattern
        occurrence).name = occurrence.name := by
    cases pattern with
    | bvar index =>
        have impossible := occurrence.name_mem_freeFvarNames
        simp [canonicalizeByAt, Pattern.freeFvarNames] at impossible
    | fvar name => rw [canonicalizeByAtOccurrenceSource]
    | apply constructor arguments =>
        rw [canonicalizeByAtOccurrenceSource]
        let childDepth :=
          if constructor == declaration.quoteConstructor then 0
          else availableDepth
        let normalizedArguments :=
          canonicalizeListByAt key declaration childDepth arguments
        let normalizedArgument := finishApplyOccurrenceSource declaration
          constructor normalizedArguments occurrence
        let sourceArgument := canonicalizeListByAtOccurrenceSource key
          declaration childDepth arguments normalizedArgument
        change (sourceArgument.inApply constructor).name = occurrence.name
        exact (CostStaticFVarListOccurrence.inApply_name constructor
            sourceArgument).trans
          ((canonicalizeListByAtOccurrenceSource_name key declaration
            childDepth arguments normalizedArgument).trans
          (finishApplyOccurrenceSource_name declaration constructor
            normalizedArguments occurrence))
    | lambda binder body =>
        rw [canonicalizeByAtOccurrenceSource]
        let normalizedBody :=
          canonicalizeByAt key declaration (availableDepth + 1) body
        let bodyOccurrence := lambdaOccurrenceBody binder normalizedBody occurrence
        let sourceBody := canonicalizeByAtOccurrenceSource key declaration
          (availableDepth + 1) body bodyOccurrence
        change (sourceBody.inContext (.lambda binder .hole)).name =
          occurrence.name
        exact (CostStaticFVarOccurrence.inContext_name sourceBody _).trans
          ((canonicalizeByAtOccurrenceSource_name key declaration
            (availableDepth + 1) body bodyOccurrence).trans
          (lambdaOccurrenceBody_name binder normalizedBody occurrence))
    | multiLambda arity binders body =>
        rw [canonicalizeByAtOccurrenceSource]
        let normalizedBody :=
          canonicalizeByAt key declaration (availableDepth + arity) body
        let bodyOccurrence := multiLambdaOccurrenceBody arity binders
          normalizedBody occurrence
        let sourceBody := canonicalizeByAtOccurrenceSource key declaration
          (availableDepth + arity) body bodyOccurrence
        change (sourceBody.inContext
          (.multiLambda arity binders .hole)).name = occurrence.name
        exact (CostStaticFVarOccurrence.inContext_name sourceBody _).trans
          ((canonicalizeByAtOccurrenceSource_name key declaration
            (availableDepth + arity) body bodyOccurrence).trans
          (multiLambdaOccurrenceBody_name arity binders normalizedBody occurrence))
    | subst body replacement =>
        let normalizedBody :=
          canonicalizeByAt key declaration (availableDepth + 1) body
        let normalizedReplacement :=
          canonicalizeByAt key declaration availableDepth replacement
        generalize viewEquality :
          substOccurrenceView normalizedBody normalizedReplacement occurrence =
            view
        cases view with
        | body inner contextEquality selected =>
            let nested : CostStaticFVarOccurrence normalizedBody :=
              { name := occurrence.name
                context := inner
                selected := selected }
            let sourceBody := canonicalizeByAtOccurrenceSource key declaration
              (availableDepth + 1) body nested
            rw [canonicalizeByAtOccurrenceSource]
            rw [viewEquality]
            exact (CostStaticFVarOccurrence.inContext_name sourceBody _).trans
              (canonicalizeByAtOccurrenceSource_name key declaration
                (availableDepth + 1) body nested)
        | replacement inner contextEquality selected =>
            let nested : CostStaticFVarOccurrence normalizedReplacement :=
              { name := occurrence.name
                context := inner
                selected := selected }
            let sourceReplacement := canonicalizeByAtOccurrenceSource key
              declaration availableDepth replacement nested
            rw [canonicalizeByAtOccurrenceSource]
            rw [viewEquality]
            exact (CostStaticFVarOccurrence.inContext_name sourceReplacement _
              ).trans
              (canonicalizeByAtOccurrenceSource_name key declaration
                availableDepth replacement nested)
    | collection collectionType elements rest =>
        let normalizedElements :=
          canonicalizeListByAt key declaration availableDepth elements
        cases rest with
        | none =>
            rw [canonicalizeByAtOccurrenceSource]
            by_cases parallel :
                collectionType = declaration.parallelCollection
            · subst collectionType
              rw [dif_pos rfl]
              let phaseEquality :
                  canonicalizeByAt key declaration availableDepth
                      (.collection declaration.parallelCollection elements none) =
                    collapseParallel declaration
                      (normalizeParallelElementsBy (key availableDepth)
                        declaration normalizedElements) := by
                simp [canonicalizeByAt, normalizedElements]
              let finalOccurrence := occurrence.castRoot phaseEquality
              let normalizedOccurrence := keyedParallelPhaseOccurrenceSource
                (key availableDepth) declaration normalizedElements
                  finalOccurrence
              let sourceOccurrence := canonicalizeListByAtOccurrenceSource key
                declaration availableDepth elements normalizedOccurrence
              change (sourceOccurrence.inCollection
                declaration.parallelCollection none).name = occurrence.name
              exact (CostStaticFVarListOccurrence.inCollection_name _ _
                  sourceOccurrence).trans
                ((canonicalizeListByAtOccurrenceSource_name key declaration
                  availableDepth elements normalizedOccurrence).trans
                ((keyedParallelPhaseOccurrenceSource_name
                  (key availableDepth) declaration normalizedElements
                    finalOccurrence).trans
                (CostStaticFVarOccurrence.castRoot_name phaseEquality occurrence)))
            · rw [dif_neg parallel]
              let phaseEquality :
                  canonicalizeByAt key declaration availableDepth
                      (.collection collectionType elements none) =
                    .collection collectionType normalizedElements none := by
                simp [canonicalizeByAt, normalizedElements, parallel]
              let finalOccurrence := occurrence.castRoot phaseEquality
              let normalizedOccurrence := collectionOccurrenceMember
                collectionType normalizedElements none finalOccurrence
              let sourceOccurrence := canonicalizeListByAtOccurrenceSource key
                declaration availableDepth elements normalizedOccurrence
              change (sourceOccurrence.inCollection collectionType none).name =
                occurrence.name
              exact (CostStaticFVarListOccurrence.inCollection_name _ _
                  sourceOccurrence).trans
                ((canonicalizeListByAtOccurrenceSource_name key declaration
                  availableDepth elements normalizedOccurrence).trans
                ((collectionOccurrenceMember_name collectionType
                  normalizedElements none finalOccurrence).trans
                (CostStaticFVarOccurrence.castRoot_name phaseEquality occurrence)))
        | some collectionRest =>
            rw [canonicalizeByAtOccurrenceSource]
            let phaseEquality :
                canonicalizeByAt key declaration availableDepth
                    (.collection collectionType elements (some collectionRest)) =
                  .collection collectionType normalizedElements
                    (some collectionRest) := by
              simp [canonicalizeByAt, normalizedElements]
            let finalOccurrence := occurrence.castRoot phaseEquality
            let normalizedOccurrence := collectionOccurrenceMember
              collectionType normalizedElements (some collectionRest)
                finalOccurrence
            let sourceOccurrence := canonicalizeListByAtOccurrenceSource key
              declaration availableDepth elements normalizedOccurrence
            change (sourceOccurrence.inCollection collectionType
              (some collectionRest)).name = occurrence.name
            exact (CostStaticFVarListOccurrence.inCollection_name _ _
                sourceOccurrence).trans
              ((canonicalizeListByAtOccurrenceSource_name key declaration
                availableDepth elements normalizedOccurrence).trans
              ((collectionOccurrenceMember_name collectionType
                normalizedElements (some collectionRest) finalOccurrence).trans
              (CostStaticFVarOccurrence.castRoot_name phaseEquality occurrence)))
  termination_by 3 * sizeOf pattern + 2

  theorem canonicalizeListByAtOccurrenceSource_name
      {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl) (availableDepth : Nat) :
      ∀ (patterns : List Pattern)
        (occurrence : CostStaticFVarListOccurrence
          (canonicalizeListByAt key declaration availableDepth patterns)),
        (canonicalizeListByAtOccurrenceSource key declaration availableDepth
          patterns occurrence).occurrence.name = occurrence.occurrence.name
    | [], occurrence => Fin.elim0 occurrence.position
    | head :: tail, occurrence => by
        rcases occurrence with ⟨position, nested⟩
        cases position using Fin.cases with
        | zero =>
            rw [canonicalizeListByAtOccurrenceSource]
            exact canonicalizeByAtOccurrenceSource_name key declaration
              availableDepth head nested
        | succ tailPosition =>
            rw [canonicalizeListByAtOccurrenceSource]
            let tailOccurrence : CostStaticFVarListOccurrence
                (canonicalizeListByAt key declaration availableDepth tail) :=
              { position := tailPosition
                occurrence := nested }
            exact canonicalizeListByAtOccurrenceSource_name key declaration
              availableDepth tail tailOccurrence
  termination_by patterns _ => 3 * sizeOf patterns + 1

  decreasing_by
    all_goals simp_all <;> omega

end

/-! ## Public canonical occurrence certificate -/

/-- One exact final occurrence together with a source zipper that created it.
The target root is definitionally the keyed canonical representative of the
source root; the separate equality records the selected variable spelling. -/
structure KeyedCanonicalFVarCertificate
    {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) (availableDepth : Nat)
    (source : Pattern)
    (targetOccurrence : CostStaticFVarOccurrence
      (canonicalizeByAt key declaration availableDepth source)) where
  sourceOccurrence : CostStaticFVarOccurrence source
  name_eq : sourceOccurrence.name = targetOccurrence.name

/-- Every final canonical free-variable occurrence has a proof-relevant
authored source occurrence. -/
noncomputable def keyedCanonicalFVarCertificate
    {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) (availableDepth : Nat)
    (source : Pattern)
    (targetOccurrence : CostStaticFVarOccurrence
      (canonicalizeByAt key declaration availableDepth source)) :
    KeyedCanonicalFVarCertificate key declaration availableDepth source
      targetOccurrence where
  sourceOccurrence := canonicalizeByAtOccurrenceSource key declaration
    availableDepth source targetOccurrence
  name_eq := canonicalizeByAtOccurrenceSource_name key declaration
    availableDepth source targetOccurrence

/-- Public existential reflection erases internal phase positions without
claiming a unique source for duplicate equal occurrences. -/
theorem exists_sourceOccurrence_of_canonical
    {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) (availableDepth : Nat)
    (source : Pattern)
    (targetOccurrence : CostStaticFVarOccurrence
      (canonicalizeByAt key declaration availableDepth source)) :
    ∃ sourceOccurrence : CostStaticFVarOccurrence source,
      sourceOccurrence.name = targetOccurrence.name :=
  ⟨(keyedCanonicalFVarCertificate key declaration availableDepth source
      targetOccurrence).sourceOccurrence,
    (keyedCanonicalFVarCertificate key declaration availableDepth source
      targetOccurrence).name_eq⟩

end Mettapedia.GSLT.LanguageDef
